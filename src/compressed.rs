//! Immutable, Huffman-compressed sequences of keys.
use crate::{Key, Rodeo, RodeoReader};
use alloc::{collections::BinaryHeap, vec, vec::Vec};
use core::{cmp::Reverse, marker::PhantomData};
use rkyv::{
    rend::{u16_le, u32_le},
    Archive, Deserialize, Serialize,
};

const TABLE_BITS: usize = 12;
const BLOCK: usize = 64;

/// A read-only collection of key sequences, addressed by dense keys in insertion order.
///
/// Created by consuming a Rodeo or RodeoReader of vectors, preserving its keys and
/// deduplication. Resolution is lazy and allocation-free, including directly from
/// a validated rkyv archive.
///
/// Element IDs index the code tables directly, so elements should be dense keys,
/// such as the keys of one rodeo.
///
/// ```
/// use lasso::{Rodeo, Key, Spur};
/// let element = Spur::<()>::try_from_usize(42).unwrap();
/// let mut rodeo = Rodeo::<Vec<Spur<()>>, Spur<()>>::new();
/// let key = rodeo.get_or_intern([element, element]);
/// let resolver = rodeo.into_compressed_resolver();
/// assert_eq!(resolver.resolve(&key).collect::<Vec<_>>(), [element, element]);
/// ```
#[derive(Debug, Archive, Serialize, Deserialize)]
pub struct CompressedRodeoResolver<K, E> {
    first_key: u32_le,
    bytes: Vec<u8>,
    checkpoints: Vec<u32_le>,
    offsets: Vec<u16_le>,
    primary_symbols: Vec<u32_le>,
    primary_lengths: Vec<u8>,
    sorted: Vec<u32_le>,
    first: Vec<u32_le>,
    counts: Vec<u32_le>,
    starts: Vec<u32_le>,
    marker: PhantomData<(K, E)>,
}

impl<K: Key, E: Key> CompressedRodeoResolver<K, E> {
    fn from_sequences(sequences: &[&[E]], first_key: usize) -> Self {
        let sequences: Vec<Vec<usize>> = sequences
            .iter()
            .map(|sequence| sequence.iter().copied().map(Key::into_usize).collect())
            .collect();
        // END is the ID after the largest element.
        let end = sequences
            .iter()
            .flatten()
            .map(|&id| id + 1)
            .max()
            .unwrap_or(0);
        let end = u32::try_from(end).expect("compressed resolver element ID exceeds u32");
        let mut frequencies = vec![0u64; end as usize + 1];
        for seq in &sequences {
            for &id in seq {
                frequencies[id] += 1;
            }
            frequencies[end as usize] += 1;
        }
        let lengths = code_lengths(&frequencies);
        let max = *lengths.iter().max().unwrap() as usize;
        let mut counts = vec![0u32; max + 1];
        for &length in &lengths {
            counts[length as usize] += 1;
        }
        let mut first = vec![0u32; max + 1];
        let mut starts = vec![0u32; max + 1];
        let (mut code, mut index) = (0u64, 0u32);
        for length in 1..=max {
            first[length] = code as u32;
            starts[length] = index;
            code = (code + u64::from(counts[length])) << 1;
            index += counts[length];
        }
        let mut sorted: Vec<_> = (0..=end).collect();
        sorted.sort_unstable_by_key(|&symbol| (lengths[symbol as usize], symbol));
        let mut next: Vec<u64> = first.iter().map(|&n| u64::from(n)).collect();
        let mut codes = vec![0u32; lengths.len()];
        let mut primary_symbols = vec![u32_le::from_native(0); 1 << TABLE_BITS];
        let mut primary_lengths = vec![0; 1 << TABLE_BITS];
        for &symbol in &sorted {
            let length = lengths[symbol as usize] as usize;
            let code = next[length] as u32;
            codes[symbol as usize] = code;
            next[length] += 1;
            if length <= TABLE_BITS {
                let base = (code as usize) << (TABLE_BITS - length);
                let range = base..base + (1 << (TABLE_BITS - length));
                primary_symbols[range.clone()].fill(symbol.into());
                primary_lengths[range].fill(length as u8);
            }
        }
        let mut bytes = Vec::new();
        let mut checkpoints = Vec::new();
        let mut offsets = Vec::new();
        let (mut acc, mut acc_bits, mut total) = (0u64, 0usize, 0u64);
        let mut checkpoint = 0;
        for (i, seq) in sequences.iter().enumerate() {
            if i % BLOCK == 0 {
                checkpoint = total;
                checkpoints.push(u32_le::from_native(total as u32));
            }
            offsets.push(block_offset(total, checkpoint).into());
            for &symbol in seq.iter().chain(&[end as usize]) {
                let length = lengths[symbol] as usize;
                total += length as u64;
                checked_bits(total);
                acc = (acc << length) | u64::from(codes[symbol]);
                acc_bits += length;
                while acc_bits >= 8 {
                    acc_bits -= 8;
                    bytes.push((acc >> acc_bits) as u8);
                }
            }
        }
        if acc_bits != 0 {
            bytes.push((acc << (8 - acc_bits)) as u8);
        }
        bytes.extend([0; 8]);
        CompressedRodeoResolver {
            first_key: u32::try_from(first_key)
                .expect("compressed resolver first key exceeds u32")
                .into(),
            bytes,
            checkpoints,
            offsets,
            primary_symbols,
            primary_lengths,
            sorted: sorted.into_iter().map(Into::into).collect(),
            first: first.into_iter().map(Into::into).collect(),
            counts: counts.into_iter().map(Into::into).collect(),
            starts: starts.into_iter().map(Into::into).collect(),
            marker: PhantomData,
        }
    }
}

impl<E: Key + Eq + core::hash::Hash + Copy + 'static, K: Key, S> Rodeo<Vec<E>, K, S> {
    /// Consumes this interner into a compressed resolver, preserving its keys.
    ///
    /// Panics if a Huffman code exceeds 32 bits, total encoded bits exceed u32,
    /// an element ID does not fit in u32, or a sequence start exceeds its
    /// 64-sequence checkpoint by more than u16 bits.
    pub fn into_compressed_resolver(self) -> CompressedRodeoResolver<K, E> {
        CompressedRodeoResolver::from_sequences(&self.strings, self.first_key)
    }
}

impl<E: Key + Eq + core::hash::Hash + Copy + 'static, K: Key, S> RodeoReader<Vec<E>, K, S> {
    /// Consumes this reader into a compressed resolver, preserving its keys.
    /// Has the same format limits as [`Rodeo::into_compressed_resolver`].
    pub fn into_compressed_resolver(self) -> CompressedRodeoResolver<K, E> {
        CompressedRodeoResolver::from_sequences(&self.strings, self.first_key)
    }
}

fn checked_bits(total: u64) {
    assert!(
        total <= u32::MAX as u64,
        "compressed resolver total bits exceed u32"
    );
}
fn block_offset(total: u64, checkpoint: u64) -> u16 {
    u16::try_from(total - checkpoint)
        .expect("compressed resolver block-relative bit offset exceeds u16")
}

fn code_lengths(frequencies: &[u64]) -> Vec<u8> {
    let n = frequencies.len();
    let mut parents = vec![0; 2 * n];
    let mut heap: BinaryHeap<_> = frequencies
        .iter()
        .enumerate()
        .map(|(id, &frequency)| Reverse((frequency.max(1), id)))
        .collect();
    let mut next = n;
    while heap.len() > 1 {
        let Reverse((a, i)) = heap.pop().unwrap();
        let Reverse((b, j)) = heap.pop().unwrap();
        parents[i] = next;
        parents[j] = next;
        heap.push(Reverse((a + b, next)));
        next += 1;
    }
    let root = next - 1;
    let mut depths = vec![0u8; next];
    for node in (0..root).rev() {
        depths[node] = depths[parents[node]] + 1;
        assert!(
            depths[node] <= 32,
            "compressed resolver Huffman code exceeds 32 bits"
        );
    }
    depths.truncate(n);
    if n == 1 {
        depths[0] = 1;
    }
    depths
}

// Endian-aware integers archive to themselves, so both owners lend precisely the
// same slices to the decoder, with no virtual calls or reconstructed tables.
#[derive(Debug, Clone, Copy)]
struct View<'a> {
    bytes: &'a [u8],
    primary_symbols: &'a [u32_le],
    primary_lengths: &'a [u8],
    sorted: &'a [u32_le],
    first: &'a [u32_le],
    counts: &'a [u32_le],
    starts: &'a [u32_le],
}

/// A lazy, allocation-free iterator over one compressed sequence.
/// Stops at its END symbol; dropping it does not decode the remaining elements.
#[derive(Debug)]
pub struct CompressedElements<'a, E> {
    view: View<'a>,
    bit: u64,
    done: bool,
    marker: PhantomData<E>,
}

impl<E: Key> Iterator for CompressedElements<'_, E> {
    type Item = E;
    fn next(&mut self) -> Option<E> {
        if self.done {
            return None;
        }
        let byte = usize::try_from(self.bit / 8).expect("compressed bit position exceeds usize");
        let word = u64::from_be_bytes(self.view.bytes[byte..byte + 8].try_into().unwrap());
        let peek = ((word << (self.bit % 8)) >> 32) as u32;
        let slot = (peek >> (32 - TABLE_BITS)) as usize;
        let mut length = self.view.primary_lengths[slot] as usize;
        let symbol = if length != 0 {
            self.view.primary_symbols[slot].to_native()
        } else {
            length = (TABLE_BITS + 1..self.view.counts.len())
                .find(|&length| {
                    let code = peek >> (32 - length);
                    code.checked_sub(self.view.first[length].to_native())
                        .is_some_and(|delta| delta < self.view.counts[length].to_native())
                })
                .expect("invalid compressed Huffman code");
            let delta = (peek >> (32 - length)) - self.view.first[length].to_native();
            self.view.sorted
                [(u64::from(self.view.starts[length].to_native()) + u64::from(delta)) as usize]
                .to_native()
        } as usize;
        self.bit += length as u64;
        // END is the last symbol ID.
        if symbol == self.view.sorted.len() - 1 {
            self.done = true;
            None
        } else {
            Some(E::try_from_usize(symbol).expect("compressed element ID is invalid for key type"))
        }
    }
}
impl<E: Key> core::iter::FusedIterator for CompressedElements<'_, E> {}

macro_rules! resolver_methods {
    () => {
        /// Returns the number of sequences (including an interned empty sequence).
        pub fn len(&self) -> usize {
            self.offsets.len()
        }
        /// Returns whether there are no sequences.
        pub fn is_empty(&self) -> bool {
            self.offsets.is_empty()
        }
        /// Returns whether the key is in bounds.
        pub fn contains_key(&self, key: &K) -> bool {
            key.into_usize()
                .checked_sub(self.first_key.to_native() as usize)
                .is_some_and(|index| index < self.len())
        }
        /// Lazily resolves a sequence. Panics if the key is out of bounds.
        pub fn resolve(&self, key: &K) -> CompressedElements<'_, E> {
            self.try_resolve(key)
                .expect("compressed resolver key out of bounds")
        }
        /// Lazily resolves a sequence, or returns None for an out-of-bounds key.
        pub fn try_resolve(&self, key: &K) -> Option<CompressedElements<'_, E>> {
            let index = key
                .into_usize()
                .checked_sub(self.first_key.to_native() as usize)?;
            let offset = self.offsets.get(index)?.to_native();
            Some(CompressedElements {
                view: View {
                    bytes: &self.bytes,
                    primary_symbols: &self.primary_symbols,
                    primary_lengths: &self.primary_lengths,
                    sorted: &self.sorted,
                    first: &self.first,
                    counts: &self.counts,
                    starts: &self.starts,
                },
                bit: u64::from(self.checkpoints[index / BLOCK].to_native()) + u64::from(offset),
                done: false,
                marker: PhantomData,
            })
        }
        /// Visits sequences in key order without decoding their elements eagerly.
        pub fn iter(&self) -> impl ExactSizeIterator<Item = (K, CompressedElements<'_, E>)> + '_ {
            (0..self.len()).map(|index| {
                let key = K::try_from_usize(index + self.first_key.to_native() as usize)
                    .expect("compressed resolver key space exhausted");
                let elements = self.resolve(&key);
                (key, elements)
            })
        }
    };
}
impl<K: Key, E: Key> CompressedRodeoResolver<K, E> {
    resolver_methods!();
}
impl<K: Key, E: Key> ArchivedCompressedRodeoResolver<K, E> {
    resolver_methods!();
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{LargeSpur, Spur};
    // Deliberately implements no traits, including Archive and Debug.
    struct Marker;
    type K = Spur<Marker>;
    type E = LargeSpur<Marker>;
    type Resolver = CompressedRodeoResolver<K, E>;

    fn build(sequences: &[Vec<usize>]) -> Resolver {
        let mut rodeo = Rodeo::<Vec<E>, K>::new();
        for sequence in sequences {
            let sequence: Vec<E> = sequence
                .iter()
                .map(|&id| E::try_from_usize(id).unwrap())
                .collect();
            let key = rodeo.get_or_intern(&sequence);
            assert_eq!(rodeo.get_or_intern(&sequence), key);
        }
        rodeo.into_compressed_resolver()
    }

    fn roundtrip(sequences: &[Vec<usize>]) -> Resolver {
        let resolver = build(sequences);
        let mut unique = Vec::new();
        for sequence in sequences {
            if !unique.contains(sequence) {
                unique.push(sequence.clone());
            }
        }
        let sequences = unique.as_slice();
        let bytes = rkyv::to_bytes::<rkyv::rancor::Error>(&resolver).unwrap();
        assert_eq!(
            bytes.as_slice(),
            rkyv::to_bytes::<rkyv::rancor::Error>(&build(sequences))
                .unwrap()
                .as_slice()
        );
        let archived =
            rkyv::access::<ArchivedCompressedRodeoResolver<K, E>, rkyv::rancor::Error>(&bytes)
                .unwrap();
        let restored: Resolver = rkyv::deserialize::<_, rkyv::rancor::Error>(archived).unwrap();
        assert_eq!(archived.len(), sequences.len());
        assert_eq!(archived.is_empty(), sequences.is_empty());
        for owner in [&resolver, &restored] {
            assert_eq!(owner.len(), sequences.len());
            assert_eq!(owner.is_empty(), sequences.is_empty());
            for ((key, elements), expected) in owner.iter().zip(sequences) {
                assert!(owner.contains_key(&key));
                assert_eq!(elements.map(Key::into_usize).collect::<Vec<_>>(), *expected);
                assert_eq!(
                    owner
                        .try_resolve(&key)
                        .unwrap()
                        .map(Key::into_usize)
                        .collect::<Vec<_>>(),
                    *expected
                );
            }
            let missing = K::try_from_usize(sequences.len()).unwrap();
            assert!(!owner.contains_key(&missing));
            assert!(owner.try_resolve(&missing).is_none());
        }
        for ((key, elements), expected) in archived.iter().zip(sequences) {
            assert!(archived.contains_key(&key));
            assert_eq!(elements.map(Key::into_usize).collect::<Vec<_>>(), *expected);
        }
        let missing = K::try_from_usize(sequences.len()).unwrap();
        assert!(!archived.contains_key(&missing));
        assert!(archived.try_resolve(&missing).is_none());
        resolver
    }

    #[test]
    fn edges() {
        roundtrip(&[]);
        roundtrip(&vec![vec![]; 130]);
        roundtrip(&[vec![0]]);
        let resolver = roundtrip(&[vec![], vec![0, 7, 19], vec![0, 7, 19], vec![], vec![7]]);
        let mut elements = resolver.resolve(&K::try_from_usize(1).unwrap());
        let start = elements.bit;
        assert_eq!(elements.next().unwrap().into_usize(), 0);
        assert!(elements.bit > start);
        assert!(elements.bit < resolver.resolve(&K::try_from_usize(2).unwrap()).bit);
        let mut empty = resolver.resolve(&K::try_from_usize(0).unwrap());
        assert!(empty.next().is_none());
        let end = empty.bit;
        assert!(empty.next().is_none());
        assert_eq!(empty.bit, end);
    }

    #[test]
    fn skewed_randomized_and_checkpoints() {
        let mut seed = 17u64;
        let mut sequences = Vec::new();
        for index in 0..257 {
            let mut sequence = Vec::new();
            for _ in 0..index % 39 {
                seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
                sequence.push(seed.trailing_zeros() as usize);
            }
            sequence.push(index);
            sequences.push(sequence);
        }
        let resolver = roundtrip(&sequences);
        assert_eq!(resolver.checkpoints.len(), 5);
        assert!(resolver
            .offsets
            .iter()
            .any(|offset| offset.to_native() % 8 != 0));
    }

    #[test]
    fn long_codes_use_fallback() {
        // Power-of-two frequencies force a deep tree. One sequence avoids the
        // block-relative offset limit even though its payload is large.
        let mut sequence = Vec::new();
        for symbol in 0..16 {
            sequence.extend(core::iter::repeat_n(symbol, 1 << symbol));
        }
        let resolver = roundtrip(&[sequence]);
        assert!(resolver.counts.len() - 1 > TABLE_BITS);
        assert!(resolver.counts[TABLE_BITS + 1..]
            .iter()
            .any(|count| count.to_native() != 0));
    }

    #[test]
    #[should_panic(expected = "block-relative bit offset exceeds u16")]
    fn block_overflow() {
        build(&[vec![0; u16::MAX as usize + 1], vec![]]);
    }

    #[test]
    #[should_panic(expected = "Huffman code exceeds 32 bits")]
    fn code_overflow() {
        let mut frequencies = vec![1, 1];
        for i in 2..35 {
            frequencies.push(frequencies[i - 1] + frequencies[i - 2]);
        }
        code_lengths(&frequencies);
    }
}
