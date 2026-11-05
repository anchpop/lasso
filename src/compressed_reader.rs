//! Compressed rows with an exact index of a derived column.
use crate::{
    BuildSymbolTable, CompressedElements, CompressedRodeoResolver, Key, RunTable, SymbolTable,
};
use alloc::{string::String, vec, vec::Vec};
use core::{hash::Hash, marker::PhantomData};
#[cfg(feature = "no-std")]
use hashbrown::HashSet;
use rkyv::{
    rend::{u32_le, u64_le},
    Archive, Archived, Deserialize, Serialize,
};
#[cfg(not(feature = "no-std"))]
use std::collections::HashSet;

/// A trained, build-time row tokenizer. Values may borrow the input row.
pub trait Splitter<Row: ?Sized>: Sized {
    /// One emitted symbol.
    type Value<'r>: Copy + Eq + Hash
    where
        Row: 'r;
    /// Train on the complete input, without retaining borrowed rows.
    fn train<'r>(rows: impl Iterator<Item = &'r Row> + Clone) -> Self
    where
        Row: 'r;
    /// Emit a row's symbols in order.
    fn split<'r>(&self, row: &'r Row, emit: &mut impl FnMut(Self::Value<'r>));
}

/// Emits the elements of a vector unchanged.
#[derive(Debug)]
pub struct Passthrough;
impl<T: Eq + Hash> Splitter<Vec<T>> for Passthrough {
    type Value<'r>
        = &'r T
    where
        T: 'r;
    fn train<'r>(_: impl Iterator<Item = &'r Vec<T>> + Clone) -> Self
    where
        T: 'r,
    {
        Self
    }
    fn split<'r>(&self, row: &'r Vec<T>, emit: &mut impl FnMut(&'r T)) {
        row.iter().for_each(emit);
    }
}

/// A derived column over compressed rows. Hashing a row must write the same
/// byte stream as hashing its query. The supplied hasher is chunk-independent.
/// Context is borrowed, never stored; it must describe the same projection at
/// construction and lookup. Matching may stop decoding at the first difference.
pub trait Projection<A: SymbolTable> {
    /// External data needed to interpret a row.
    type Context<'a>;
    /// The column's query type.
    type Query: ?Sized;
    /// Hash the derived value of one row.
    fn hash_row<'a>(
        cx: &Self::Context<'_>,
        row: impl Iterator<Item = A::Item<'a>>,
        h: &mut ProjectionHasher,
    ) where
        A: 'a;
    /// Hash a query using the same byte stream as its matching row.
    fn hash_query(q: &Self::Query, h: &mut ProjectionHasher);
    /// Compare the derived value to a query, preferably streaming and short-circuiting.
    fn matches<'a>(
        cx: &Self::Context<'_>,
        row: impl Iterator<Item = A::Item<'a>>,
        q: &Self::Query,
    ) -> bool
    where
        A: 'a;
}

/// Immutable compressed rows numbered by their derived column's MPHF slot.
/// The projection type ties lookups to construction. The index contains only
/// bit arrays and rank checkpoints, not copies of either rows or projected values.
#[derive(Debug, Archive, Serialize, Deserialize)]
pub struct CompressedRodeoReader<K, A, P> {
    rows: CompressedRodeoResolver<K, A>,
    index: Mphf,
    marker: PhantomData<P>,
}

impl<K: Key, A: SymbolTable + Default, P> Default for CompressedRodeoReader<K, A, P> {
    fn default() -> Self {
        Self {
            rows: CompressedRodeoResolver::from_ids(A::default(), 0, Vec::new(), 0),
            index: Mphf {
                levels: Vec::new(),
                seed: 0.into(),
            },
            marker: PhantomData,
        }
    }
}

impl<K: Key, T: Clone + Eq + Hash, P: Projection<Vec<T>>> CompressedRodeoReader<K, Vec<T>, P> {
    /// Build vector rows using the passthrough splitter.
    pub fn build<H>(cx: &P::Context<'_>, rows: HashSet<Vec<T>, H>) -> Self {
        Self::build_with::<_, Passthrough>(cx, rows.iter())
    }
}

impl<K: Key, A: SymbolTable, P: Projection<A>> CompressedRodeoReader<K, A, P> {
    /// Train and split each row once. Number symbols in MPHF slot order so
    /// deterministic splitters produce archive bytes independent of input order.
    /// Distinct rows with identical projections are a construction error.
    fn build_with<'r, Row: ?Sized + 'r, S: Splitter<Row>>(
        cx: &P::Context<'_>,
        rows: impl Iterator<Item = &'r Row> + Clone,
    ) -> Self
    where
        A: BuildSymbolTable<S::Value<'r>>,
    {
        let splitter = S::train(rows.clone());
        let rows: Vec<Vec<_>> = rows
            .map(|row| {
                let mut values = Vec::new();
                splitter.split(row, &mut |value| values.push(value));
                values
            })
            .collect();
        Self::from_split(cx, rows)
    }

    fn from_split<V: Copy + Eq + Hash>(cx: &P::Context<'_>, rows: Vec<Vec<V>>) -> Self
    where
        A: BuildSymbolTable<V>,
    {
        // Hash through the same table API used at lookup, then rebuild in slot order.
        let mut alphabet = A::default();
        let mut ids = hashbrown::HashMap::new();
        let encoded: Vec<Vec<_>> = rows
            .iter()
            .map(|row| {
                row.iter()
                    .map(|&value| {
                        let next = ids.len();
                        *ids.entry(value).or_insert_with(|| {
                            alphabet.push(value);
                            next
                        })
                    })
                    .collect()
            })
            .collect();
        let (seed, hashes) = (0..128u64)
            .find_map(|seed| {
                let hashes: Vec<_> = encoded
                    .iter()
                    .map(|row| {
                        let mut h = ProjectionHasher::new(seed);
                        P::hash_row(cx, row.iter().map(|&id| alphabet.get(id)), &mut h);
                        h.finish()
                    })
                    .collect();
                (hashes.iter().copied().collect::<HashSet<_>>().len() == hashes.len())
                    .then_some((seed, hashes))
            })
            .expect("duplicate projection hashes after deterministic seed retries");
        drop((alphabet, ids, encoded));
        let index = Mphf::build(&hashes, seed);
        let mut slots: Vec<_> = (0..rows.len()).map(|_| None).collect();
        for (row, hash) in rows.into_iter().zip(hashes) {
            let slot = index.slot(hash).unwrap();
            K::try_from_usize(slot).expect("compressed reader key space exhausted");
            assert!(slots[slot].replace(row).is_none());
        }
        let rows: Vec<_> = slots.into_iter().map(Option::unwrap).collect();
        Self {
            rows: CompressedRodeoResolver::from_values(rows, 0),
            index,
            marker: PhantomData,
        }
    }

    /// Exact reverse lookup: hash the query, then compare only its candidate row.
    pub fn get(&self, cx: &P::Context<'_>, q: &P::Query) -> Option<K> {
        let mut h = ProjectionHasher::new(self.index.seed.to_native());
        P::hash_query(q, &mut h);
        let key = K::try_from_usize(self.index.slot(h.finish())?)?;
        P::matches(cx, self.rows.resolve(&key), q).then_some(key)
    }
}

impl<K: Key, A: Archive, P: Projection<Archived<A>>> ArchivedCompressedRodeoReader<K, A, P>
where
    Archived<A>: SymbolTable,
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
        P::matches(cx, self.rows.resolve(&key), q).then_some(key)
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
impl<K: Key, A: SymbolTable, P> CompressedRodeoReader<K, A, P> {
    reader_methods!(A);
}
impl<K: Key, A: Archive, P> ArchivedCompressedRodeoReader<K, A, P>
where
    Archived<A>: SymbolTable,
{
    reader_methods!(Archived<A>);
}

/// The concatenated UTF-8 text of a row of runs.
#[derive(Debug)]
pub struct Text;
impl<A: SymbolTable + 'static> Projection<A> for Text
where
    for<'a> A: SymbolTable<Item<'a> = &'a str>,
{
    type Context<'a> = ();
    type Query = str;
    fn hash_row<'a>(_: &(), row: impl Iterator<Item = &'a str>, h: &mut ProjectionHasher)
    where
        A: 'a,
    {
        for run in row {
            h.write(run.as_bytes());
        }
    }
    fn hash_query(q: &str, h: &mut ProjectionHasher) {
        h.write(q.as_bytes());
    }
    fn matches<'a>(_: &(), row: impl Iterator<Item = &'a str>, mut q: &str) -> bool
    where
        A: 'a,
    {
        for run in row {
            let Some(rest) = q.strip_prefix(run) else {
                return false;
            };
            q = rest;
        }
        q.is_empty()
    }
}
impl<K: Key> CompressedRodeoReader<K, RunTable, Text> {
    /// Train a text splitter and verify that its runs reproduce every input exactly.
    pub fn build<S>(rows: HashSet<String>) -> Self
    where
        for<'r> S: Splitter<str, Value<'r> = &'r str>,
    {
        let splitter = S::train(rows.iter().map(String::as_str));
        let rows = rows
            .iter()
            .map(|row| {
                let mut runs = Vec::new();
                splitter.split(row, &mut |run| runs.push(run));
                assert!(
                    <Text as Projection<RunTable>>::matches(&(), runs.iter().copied(), row),
                    "splitter runs do not reconstruct input"
                );
                runs
            })
            .collect();
        Self::from_split(&(), rows)
    }
}

macro_rules! text_methods {
    () => {
        /// Clear and reuse a string buffer to resolve one row.
        pub fn resolve_into(&self, key: &K, text: &mut String) {
            text.clear();
            for run in self.resolve(key) {
                text.push_str(run);
            }
        }
        /// Resolve one row into a new string.
        pub fn resolve_string(&self, key: &K) -> String {
            let mut text = String::new();
            self.resolve_into(key, &mut text);
            text
        }
    };
}
impl<K: Key> CompressedRodeoReader<K, RunTable, Text> {
    text_methods!();
}
impl<K: Key> ArchivedCompressedRodeoReader<K, RunTable, Text> {
    text_methods!();
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
/// Portable, seeded streaming XXH3. Chunk boundaries do not affect the hash;
/// projections supply the column's bytes explicitly.
#[derive(Default)]
pub struct ProjectionHasher {
    inner: xxhash_rust::xxh3::Xxh3,
}
impl core::fmt::Debug for ProjectionHasher {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("ProjectionHasher").finish_non_exhaustive()
    }
}
impl ProjectionHasher {
    fn new(seed: u64) -> Self {
        Self {
            inner: xxhash_rust::xxh3::Xxh3::with_seed(seed),
        }
    }
    /// Append bytes to the projected value's hash stream.
    pub fn write(&mut self, bytes: &[u8]) {
        self.inner.update(bytes);
    }
    fn finish(self) -> u64 {
        self.inner.digest()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn similar_nine_byte_texts_have_distinct_chunk_independent_hashes() {
        // FxHash's top-byte/one-byte-tail mixing collided on these real definitions.
        let values = [
            "importava",
            "important",
            "atendente",
            "atendendo",
            "chance de",
            "chance to",
        ];
        for seed in 0..128 {
            let hashes: HashSet<_> = values
                .iter()
                .map(|value| {
                    let mut whole = ProjectionHasher::new(seed);
                    whole.write(value.as_bytes());
                    let hash = whole.finish();
                    for split in 0..=value.len() {
                        let mut chunks = ProjectionHasher::new(seed);
                        chunks.write(&value.as_bytes()[..split]);
                        chunks.write(&value.as_bytes()[split..]);
                        assert_eq!(hash, chunks.finish());
                    }
                    hash
                })
                .collect();
            assert_eq!(hashes.len(), values.len(), "seed {seed}");
        }
        let reader =
            TextReader::build::<Characters>(values.iter().map(|s| String::from(*s)).collect());
        let bytes = rkyv::to_bytes::<rkyv::rancor::Error>(&reader).unwrap();
        let archived = rkyv::access::<Archived<TextReader>, rkyv::rancor::Error>(&bytes).unwrap();
        for value in values {
            let key = reader.get(&(), value).unwrap();
            assert_eq!(archived.get(&(), value), Some(key));
            assert_eq!(archived.resolve_string(&key), value);
        }
    }
    use crate::Spur;
    use alloc::{format, string::String};
    #[derive(Debug)]
    struct Text;
    impl<A: SymbolTable + 'static> Projection<A> for Text
    where
        for<'a> A: SymbolTable<Item<'a> = &'a u8>,
    {
        type Context<'a> = ();
        type Query = str;
        fn hash_row<'a>(_: &(), row: impl Iterator<Item = &'a u8>, h: &mut ProjectionHasher)
        where
            A: 'a,
        {
            for byte in row {
                h.write(&[*byte]);
            }
        }
        fn hash_query(q: &str, h: &mut ProjectionHasher) {
            h.write(q.as_bytes());
        }
        fn matches<'a>(_: &(), row: impl Iterator<Item = &'a u8>, q: &str) -> bool
        where
            A: 'a,
        {
            row.copied().eq(q.bytes())
        }
    }
    #[derive(Debug)]
    struct Characters;
    impl Splitter<str> for Characters {
        type Value<'r> = &'r str;
        fn train<'r>(rows: impl Iterator<Item = &'r str> + Clone) -> Self {
            assert_eq!(rows.clone().count(), rows.count());
            Self
        }
        fn split<'r>(&self, row: &'r str, emit: &mut impl FnMut(&'r str)) {
            for (start, ch) in row.char_indices() {
                emit(&row[start..start + ch.len_utf8()]);
            }
        }
    }
    type TextReader = CompressedRodeoReader<Spur<()>, RunTable, super::Text>;

    #[test]
    fn text_runs_roundtrip() {
        let values = ["", "a", "ab", "bonjour le monde", "東京", "é😊", "é😊!"];
        let reader =
            TextReader::build::<Characters>(values.iter().map(|s| String::from(*s)).collect());
        let bytes = rkyv::to_bytes::<rkyv::rancor::Error>(&reader).unwrap();
        let reversed = TextReader::build::<Characters>(
            values.iter().rev().map(|s| String::from(*s)).collect(),
        );
        assert_eq!(
            bytes.as_slice(),
            rkyv::to_bytes::<rkyv::rancor::Error>(&reversed)
                .unwrap()
                .as_slice()
        );
        let archived = rkyv::access::<Archived<TextReader>, rkyv::rancor::Error>(&bytes).unwrap();
        let restored: TextReader = rkyv::deserialize::<_, rkyv::rancor::Error>(archived).unwrap();
        let mut buffer = String::from("previous contents");
        for value in values {
            let key = reader.get(&(), value).unwrap();
            for owner in [&reader, &restored] {
                assert_eq!(owner.get(&(), value), Some(key));
                assert_eq!(owner.resolve_string(&key), value);
                owner.resolve_into(&key, &mut buffer);
                assert_eq!(buffer, value);
            }
            assert_eq!(archived.get(&(), value), Some(key));
            assert_eq!(archived.resolve_string(&key), value);
            archived.resolve_into(&key, &mut buffer);
            assert_eq!(buffer, value);
            assert_eq!(reader.resolve(&key).collect::<Vec<_>>().concat(), value);
        }
        for value in ["abc", "b", "bon", "bonjour le monde!", "東", "é", "é😊!!"] {
            assert_eq!(reader.get(&(), value), None);
            assert_eq!(archived.get(&(), value), None);
            assert_eq!(restored.get(&(), value), None);
        }
        let matches = |runs: &[&str], q| {
            <super::Text as Projection<RunTable>>::matches(&(), runs.iter().copied(), q)
        };
        assert!(!matches(&["ab"], "a"));
        assert!(!matches(&["a"], "ab"));
        assert!(matches(&["", "é", "😊", ""], "é😊"));
        let mut count = 0;
        assert!(!<super::Text as Projection<RunTable>>::matches(
            &(),
            ["x", "y"].into_iter().inspect(|_| count += 1),
            "z"
        ));
        assert_eq!(count, 1);
        let empty = TextReader::build::<Characters>(HashSet::new());
        assert!(empty.is_empty());
        assert_eq!(empty.get(&(), ""), None);
    }

    #[test]
    #[should_panic(expected = "splitter runs do not reconstruct input")]
    fn bad_splitter() {
        struct Bad;
        impl Splitter<str> for Bad {
            type Value<'r> = &'r str;
            fn train<'r>(_: impl Iterator<Item = &'r str> + Clone) -> Self {
                Self
            }
            fn split<'r>(&self, _: &'r str, emit: &mut impl FnMut(&'r str)) {
                emit("wrong");
            }
        }
        TextReader::build::<Bad>([String::from("right")].into_iter().collect());
    }

    #[test]
    fn portable_hash_vector() {
        let mut whole = ProjectionHasher::new(0);
        whole.write(b"hello");
        let mut chunks = ProjectionHasher::new(0);
        chunks.write(b"he");
        chunks.write(b"llo");
        assert_eq!(whole.finish(), 10760762337991515389);
        assert_eq!(chunks.finish(), 10760762337991515389);
        let hash = |bytes: &[u8]| {
            let mut h = ProjectionHasher::new(0);
            h.write(bytes);
            h.finish()
        };
        assert_ne!(hash(b"a"), hash(b"a\0"));
    }

    type Reader = CompressedRodeoReader<Spur<()>, Vec<u8>, Text>;
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
        impl Projection<Vec<u8>> for Constant {
            type Context<'a> = ();
            type Query = str;
            fn hash_row<'a>(_: &(), _: impl Iterator<Item = &'a u8>, h: &mut ProjectionHasher) {
                h.write(b"same");
            }
            fn hash_query(_: &str, h: &mut ProjectionHasher) {
                h.write(b"same");
            }
            fn matches<'a>(_: &(), _: impl Iterator<Item = &'a u8>, _: &str) -> bool {
                true
            }
        }
        CompressedRodeoReader::<Spur<()>, _, Constant>::build(
            &(),
            [vec![1], vec![2]].into_iter().collect::<HashSet<_>>(),
        );
    }
}
