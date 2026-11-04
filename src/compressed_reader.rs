//! Compressed rows with an exact index of a derived column.
use crate::{CompressedElements, CompressedRodeoResolver, Key};
use alloc::{vec, vec::Vec};
use core::{
    hash::{Hash, Hasher},
    marker::PhantomData,
};
#[cfg(feature = "no-std")]
use hashbrown::HashSet;
use rkyv::{
    rend::{u32_le, u64_le},
    Archive, Archived, Deserialize, Serialize,
};
#[cfg(not(feature = "no-std"))]
use std::collections::HashSet;

/// A derived column over compressed rows. Hashing a row must write the same
/// byte stream as hashing its query. The supplied hasher is chunk-independent.
/// Context is borrowed, never stored; it must describe the same projection at
/// construction and lookup. Matching may stop decoding at the first difference.
pub trait Projection<T> {
    /// External data needed to interpret a row.
    type Context<'a>;
    /// The column's query type.
    type Query: ?Sized;
    /// Hash the derived value of one row.
    fn hash_row(cx: &Self::Context<'_>, row: impl Iterator<Item = T>, h: &mut ProjectionHasher);
    /// Hash a query using the same byte stream as its matching row.
    fn hash_query(q: &Self::Query, h: &mut ProjectionHasher);
    /// Compare the derived value to a query, preferably streaming and short-circuiting.
    fn matches(cx: &Self::Context<'_>, row: impl Iterator<Item = T>, q: &Self::Query) -> bool;
}

/// Immutable compressed rows numbered by their derived column's MPHF slot.
/// The projection type ties lookups to construction. The index contains only
/// bit arrays and rank checkpoints, not copies of either rows or projected values.
#[derive(Debug, Archive, Serialize, Deserialize)]
pub struct CompressedRodeoReader<K, T, P> {
    rows: CompressedRodeoResolver<K, T>,
    index: Mphf,
    marker: PhantomData<P>,
}

impl<K: Key, T: Copy + Eq + Hash, P> Default for CompressedRodeoReader<K, T, P> {
    fn default() -> Self {
        Self {
            rows: CompressedRodeoResolver::from_sequences(&[], 0),
            index: Mphf {
                levels: Vec::new(),
                seed: 0.into(),
            },
            marker: PhantomData,
        }
    }
}

impl<K: Key, T: Copy + Eq + Hash, P: Projection<T>> CompressedRodeoReader<K, T, P> {
    /// Build from a set. Both key assignment and archive bytes are independent
    /// of its iteration order. Fixed seeds are retried to separate hash collisions;
    /// distinct rows projecting to the same value are a construction error.
    pub fn build<S>(cx: &P::Context<'_>, rows: HashSet<Vec<T>, S>) -> Self {
        let rows: Vec<_> = rows.into_iter().collect();
        let (seed, hashes) = (0..128u64)
            .find_map(|seed| {
                let hashes: Vec<_> = rows
                    .iter()
                    .map(|row| {
                        let mut h = ProjectionHasher::new(seed);
                        P::hash_row(cx, row.iter().copied(), &mut h);
                        h.finish()
                    })
                    .collect();
                (hashes.iter().copied().collect::<HashSet<_>>().len() == hashes.len())
                    .then_some((seed, hashes))
            })
            .expect("duplicate projection hashes after deterministic seed retries");
        let index = Mphf::build(&hashes, seed);
        let mut slots: Vec<_> = (0..rows.len()).map(|_| None).collect();
        for (row, hash) in rows.into_iter().zip(hashes) {
            let slot = index.slot(hash).unwrap();
            K::try_from_usize(slot).expect("compressed reader key space exhausted");
            assert!(slots[slot].replace(row).is_none());
        }
        let rows: Vec<_> = slots.into_iter().map(Option::unwrap).collect();
        Self {
            rows: CompressedRodeoResolver::from_sequences(
                &rows.iter().map(Vec::as_slice).collect::<Vec<_>>(),
                0,
            ),
            index,
            marker: PhantomData,
        }
    }

    /// Exact reverse lookup: hash the query, then compare only its candidate row.
    pub fn get(&self, cx: &P::Context<'_>, q: &P::Query) -> Option<K> {
        let mut h = ProjectionHasher::new(self.index.seed.to_native());
        P::hash_query(q, &mut h);
        let key = K::try_from_usize(self.index.slot(h.finish())?)?;
        P::matches(cx, self.rows.resolve(&key).copied(), q).then_some(key)
    }
}

impl<K: Key, T: Archive, P: Projection<Archived<T>>> ArchivedCompressedRodeoReader<K, T, P>
where
    Archived<T>: Copy,
{
    /// Exact lookup directly in validated archived rows and index. The projection
    /// interprets archived elements with its corresponding borrowed context.
    pub fn get(&self, cx: &P::Context<'_>, q: &P::Query) -> Option<K> {
        let mut h = ProjectionHasher::new(self.index.seed.to_native());
        P::hash_query(q, &mut h);
        let key = K::try_from_usize(slot(
            h.finish(),
            self.index
                .levels
                .iter()
                .map(|l| (l.bits.as_slice(), l.ranks.as_slice())),
        )?)?;
        P::matches(cx, self.rows.resolve(&key).copied(), q).then_some(key)
    }
}

macro_rules! reader_methods {
    ($element:ty) => {
        /// Number of rows.
        pub fn len(&self) -> usize {
            self.rows.len()
        }
        /// Whether there are no rows.
        pub fn is_empty(&self) -> bool {
            self.rows.is_empty()
        }
        /// Whether a key is in bounds.
        pub fn contains_key(&self, key: &K) -> bool {
            self.rows.contains_key(key)
        }
        /// Decode one row lazily.
        pub fn resolve(&self, key: &K) -> CompressedElements<'_, $element> {
            self.rows.resolve(key)
        }
        /// Decode one row lazily, or return None for an out-of-bounds key.
        pub fn try_resolve(&self, key: &K) -> Option<CompressedElements<'_, $element>> {
            self.rows.try_resolve(key)
        }
        /// Visit rows in slot order without eagerly decoding their elements.
        pub fn iter(
            &self,
        ) -> impl ExactSizeIterator<Item = (K, CompressedElements<'_, $element>)> + '_ {
            self.rows.iter()
        }
    };
}
impl<K: Key, T, P> CompressedRodeoReader<K, T, P> {
    reader_methods!(T);
}
impl<K: Key, T: Archive, P> ArchivedCompressedRodeoReader<K, T, P> {
    reader_methods!(Archived<T>);
}

#[derive(Debug, Archive, Serialize, Deserialize)]
struct Mphf {
    levels: Vec<Level>,
    seed: u64_le,
}
#[derive(Debug, Archive, Serialize, Deserialize)]
struct Level {
    bits: Vec<u64_le>,
    // Global rank before each group of eight words (512 bits).
    ranks: Vec<u32_le>,
}
impl Mphf {
    fn build(hashes: &[u64], seed: u64) -> Self {
        let mut remaining = hashes.to_vec();
        let len = u32::try_from(remaining.len()).expect("compressed reader exceeds u32");
        let mut levels = Vec::new();
        let mut assigned = 0u32;
        while !remaining.is_empty() {
            assert!(levels.len() < 128, "MPHF failed to separate hashes");
            // BBHash with gamma = 2, rounded to whole words for tiny tail levels.
            let words = (remaining.len() * 2).div_ceil(64);
            let mut seen = vec![0u64; words];
            let mut collisions = vec![0u64; words];
            for &hash in &remaining {
                let bit = position(hash, levels.len(), words);
                let mask = 1 << (bit % 64);
                collisions[bit / 64] |= seen[bit / 64] & mask;
                seen[bit / 64] |= mask;
            }
            for (bits, collisions) in seen.iter_mut().zip(collisions) {
                *bits &= !collisions;
            }
            remaining.retain(|&hash| {
                let bit = position(hash, levels.len(), words);
                seen[bit / 64] & (1 << (bit % 64)) == 0
            });
            let mut ranks = Vec::new();
            for (i, &bits) in seen.iter().enumerate() {
                if i % 8 == 0 {
                    ranks.push(assigned.into());
                }
                assigned += bits.count_ones();
            }
            levels.push(Level {
                bits: seen.into_iter().map(Into::into).collect(),
                ranks,
            });
        }
        assert_eq!(assigned, len);
        Self {
            levels,
            seed: seed.into(),
        }
    }
    fn slot(&self, hash: u64) -> Option<usize> {
        slot(
            hash,
            self.levels
                .iter()
                .map(|l| (l.bits.as_slice(), l.ranks.as_slice())),
        )
    }
}
fn slot<'a>(
    hash: u64,
    levels: impl Iterator<Item = (&'a [u64_le], &'a [u32_le])>,
) -> Option<usize> {
    for (level, (bits, ranks)) in levels.enumerate() {
        if bits.is_empty() {
            continue;
        }
        let bit = position(hash, level, bits.len());
        let word = bit / 64;
        let mask = 1u64 << (bit % 64);
        if bits[word].to_native() & mask != 0 {
            let rank = ranks.get(word / 8)?.to_native()
                + bits[word / 8 * 8..word]
                    .iter()
                    .map(|n| n.to_native().count_ones())
                    .sum::<u32>()
                + (bits[word].to_native() & (mask - 1)).count_ones();
            return Some(rank as usize);
        }
    }
    None
}
// Each collision round uses a fixed seed and SplitMix64's finalizer. Rank
// assigns slots in bucket order, never in the input set's iteration order.
fn position(hash: u64, level: usize, words: usize) -> usize {
    let mut hash = hash ^ (level as u64).wrapping_mul(0x9e3779b97f4a7c15);
    hash = (hash ^ (hash >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
    hash = (hash ^ (hash >> 27)).wrapping_mul(0x94d049bb133111eb);
    hash ^= hash >> 31;
    (hash % (words as u64 * 64)) as usize
}
/// Fixed-width rkyv FxHasher64 over bytes, buffered so chunk boundaries do not
/// affect its result. Projections supply the column's bytes explicitly.
#[derive(Default)]
pub struct ProjectionHasher {
    inner: rkyv::hash::FxHasher64,
    pending: [u8; 8],
    len: usize,
    total: u64,
}
impl core::fmt::Debug for ProjectionHasher {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("ProjectionHasher").finish_non_exhaustive()
    }
}
impl ProjectionHasher {
    fn new(seed: u64) -> Self {
        let mut h = Self::default();
        h.write(&seed.to_le_bytes());
        h
    }
    /// Append bytes to the projected value's hash stream.
    pub fn write(&mut self, mut bytes: &[u8]) {
        self.total += bytes.len() as u64;
        while !bytes.is_empty() {
            let take = (8 - self.len).min(bytes.len());
            self.pending[self.len..self.len + take].copy_from_slice(&bytes[..take]);
            self.len += take;
            bytes = &bytes[take..];
            if self.len == 8 {
                self.inner.write(&self.pending);
                self.len = 0;
            }
        }
    }
    fn finish(mut self) -> u64 {
        // The length keeps values that differ only by trailing zero bytes apart.
        self.inner.write(&self.pending[..self.len]);
        self.inner.write(&self.total.to_le_bytes());
        self.inner.finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Spur;
    use alloc::{format, string::String};
    #[derive(Debug)]
    struct Text;
    impl Projection<u8> for Text {
        type Context<'a> = ();
        type Query = str;
        fn hash_row(_: &(), row: impl Iterator<Item = u8>, h: &mut ProjectionHasher) {
            for byte in row {
                h.write(&[byte]);
            }
        }
        fn hash_query(q: &str, h: &mut ProjectionHasher) {
            h.write(q.as_bytes());
        }
        fn matches(_: &(), row: impl Iterator<Item = u8>, q: &str) -> bool {
            row.eq(q.bytes())
        }
    }
    #[test]
    fn portable_hash_vector() {
        let mut whole = ProjectionHasher::new(0);
        whole.write(b"hello");
        let mut chunks = ProjectionHasher::new(0);
        chunks.write(b"he");
        chunks.write(b"llo");
        assert_eq!(whole.finish(), 11965337433813237274);
        assert_eq!(chunks.finish(), 11965337433813237274);
        let hash = |bytes: &[u8]| {
            let mut h = ProjectionHasher::new(0);
            h.write(bytes);
            h.finish()
        };
        assert_ne!(hash(b"a"), hash(b"a\0"));
    }

    type Reader = CompressedRodeoReader<Spur<()>, u8, Text>;
    #[test]
    fn exact_deterministic_owned_and_archived() {
        let values: Vec<_> = (0..10000)
            .map(|i| format!("sentence {i} 東京").into_bytes())
            .chain([
                vec![],
                b"Ich bin keine Hexe.".to_vec(),
                b"Ich bin keine Hure.".to_vec(),
            ])
            .collect();
        let reader = Reader::build(&(), values.iter().cloned().collect::<HashSet<_>>());
        let reversed = Reader::build(&(), values.iter().rev().cloned().collect::<HashSet<_>>());
        let bytes = rkyv::to_bytes::<rkyv::rancor::Error>(&reader).unwrap();
        assert_eq!(
            bytes.as_slice(),
            rkyv::to_bytes::<rkyv::rancor::Error>(&reversed)
                .unwrap()
                .as_slice()
        );
        let archived = rkyv::access::<Archived<Reader>, rkyv::rancor::Error>(&bytes).unwrap();
        for value in values {
            let query = String::from_utf8(value).unwrap();
            let key = reader.get(&(), &query).unwrap();
            assert_eq!(archived.get(&(), &query), Some(key));
            assert!(reader.resolve(&key).copied().eq(query.bytes()));
            assert!(archived.resolve(&key).copied().eq(query.bytes()));
        }
        for i in 0..10000 {
            let query = format!("absent {i}");
            assert_eq!(reader.get(&(), &query), None);
            assert_eq!(archived.get(&(), &query), None);
        }
    }
    #[test]
    fn empty() {
        let reader = Reader::build(&(), HashSet::<Vec<u8>>::new());
        assert!(reader.is_empty());
        assert_eq!(reader.get(&(), ""), None);
        let bytes = rkyv::to_bytes::<rkyv::rancor::Error>(&reader).unwrap();
        let archived = rkyv::access::<Archived<Reader>, rkyv::rancor::Error>(&bytes).unwrap();
        assert!(archived.is_empty());
        assert_eq!(archived.get(&(), ""), None);
    }
    #[test]
    #[should_panic(expected = "duplicate projection hash")]
    fn duplicate_projection() {
        #[derive(Debug)]
        struct Constant;
        impl Projection<u8> for Constant {
            type Context<'a> = ();
            type Query = str;
            fn hash_row(_: &(), _: impl Iterator<Item = u8>, h: &mut ProjectionHasher) {
                h.write(b"same");
            }
            fn hash_query(_: &str, h: &mut ProjectionHasher) {
                h.write(b"same");
            }
            fn matches(_: &(), _: impl Iterator<Item = u8>, _: &str) -> bool {
                true
            }
        }
        CompressedRodeoReader::<Spur<()>, _, Constant>::build(
            &(),
            [vec![1], vec![2]].into_iter().collect::<HashSet<_>>(),
        );
    }
}
