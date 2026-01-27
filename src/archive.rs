use crate::{
    keys::{Key, Spur},
    reader::RodeoReader,
    rodeo::{Internable, Rodeo},
};
use alloc::vec::Vec;
use core::hash::{BuildHasher, Hash};
use rkyv::{
    collections::swiss_table::{ArchivedHashMap, HashMapResolver},
    hash::hash_value,
    rancor::{Fallible, Source},
    ser::{Allocator, Writer},
    with::{ArchiveWith, DeserializeWith, SerializeWith},
    Archive, Archived, Deserialize, Place, Serialize,
};

/// Trait for accessing the archived reference form of an interned type.
///
/// This is used to access the data stored in an archived rodeo.
/// For `String`, this returns `&str`.
/// For `Vec<T>`, this returns `&[Archived<T>]` (the archived element type).
pub trait ArchivedInternedRef {
    /// The reference type that can be obtained from the archived form
    type Ref: ?Sized;

    /// Get a reference to the archived data
    fn as_archived_ref(&self) -> &Self::Ref;
}

impl ArchivedInternedRef for rkyv::string::ArchivedString {
    type Ref = str;

    fn as_archived_ref(&self) -> &str {
        self.as_str()
    }
}

impl<T> ArchivedInternedRef for rkyv::vec::ArchivedVec<T> {
    type Ref = [T];

    fn as_archived_ref(&self) -> &[T] {
        self.as_slice()
    }
}

/// Trait for comparing a query value against an archived interned value.
///
/// This enables lookups in the archived rodeo by value (the `get` method).
/// The query type may differ from the archived type - for example, you can
/// query with `&[i32]` even though the archived form is `&[i32_le]`.
///
/// # Implementing for Custom Types
///
/// If you're using a custom type with rkyv serialization, you need to implement
/// this trait to enable `get()` lookups in the archived rodeo:
///
/// ```ignore
/// impl ArchivedValueEq<[MyType]> for rkyv::vec::ArchivedVec<ArchivedMyType> {
///     fn archived_eq(&self, query: &[MyType]) -> bool {
///         // Compare archived values with query values
///     }
/// }
/// ```
pub trait ArchivedValueEq<Q: ?Sized> {
    /// Returns true if the archived value equals the query value
    fn archived_eq(&self, query: &Q) -> bool;
}

// String comparison: ArchivedString can be compared with &str
impl ArchivedValueEq<str> for rkyv::string::ArchivedString {
    fn archived_eq(&self, query: &str) -> bool {
        self.as_str() == query
    }
}

// Generic Vec comparison: works for any element type where Archived<T>: PartialEq<T>
// This covers:
// - u8 (archives to itself)
// - All integer types (ArchivedI32: PartialEq<i32>, etc.)
// - Custom types that implement PartialEq<OriginalType> on their archived form
impl<T, AT> ArchivedValueEq<[T]> for rkyv::vec::ArchivedVec<AT>
where
    AT: PartialEq<T>,
{
    fn archived_eq(&self, query: &[T]) -> bool {
        let slice = self.as_slice();
        if slice.len() != query.len() {
            return false;
        }
        slice.iter().zip(query.iter()).all(|(a, b)| a == b)
    }
}

// Implement Archive for RodeoReader by converting to RodeoArchive
impl<T: Internable, K, S> Archive for RodeoReader<T, K, S>
where
    K: Key + Archive + Hash,
    S: BuildHasher,
    Archived<K>: Hash,
    T: Archive,
{
    type Archived = ArchivedRodeoArchive<T, K>;
    type Resolver = <RodeoArchive<T, K> as Archive>::Resolver;

    fn resolve(&self, resolver: Self::Resolver, out: Place<Self::Archived>) {
        // Create a temporary RodeoArchive to resolve
        let strings: Vec<T> = self.strings.iter().map(|s| T::from_ref(*s)).collect();
        let entries: Vec<(K, u64)> = self
            .map
            .iter()
            .map(|(key, _)| {
                let string = &strings[key.into_usize()];
                let hash = hash_value::<T, rkyv::hash::FxHasher64>(string);
                (*key, hash)
            })
            .collect();

        let archive = RodeoArchive {
            strings,
            map: entries,
        };

        // Delegate to RodeoArchive's resolve
        archive.resolve(resolver, out);
    }
}

impl<T: Internable, K, S, Ser> Serialize<Ser> for RodeoReader<T, K, S>
where
    T: Archive + Serialize<Ser>,
    K: Key + Archive + Serialize<Ser> + Hash + Eq,
    T: Archive,
    S: BuildHasher,
    Archived<K>: Hash,
    Ser: Fallible + Writer + Allocator + ?Sized,
    Ser::Error: Source,
{
    fn serialize(&self, serializer: &mut Ser) -> Result<Self::Resolver, Ser::Error> {
        // Convert to RodeoArchive and serialize that
        let strings: Vec<T> = self.strings.iter().map(|s| T::from_ref(*s)).collect();
        let entries: Vec<(K, u64)> = self
            .map
            .iter()
            .map(|(key, _)| {
                let string = &strings[key.into_usize()];
                let hash = hash_value::<T, rkyv::hash::FxHasher64>(string);
                (*key, hash)
            })
            .collect();

        let archive = RodeoArchive {
            strings,
            map: entries,
        };
        archive.serialize(serializer)
    }
}

// Implement Deserialize for RodeoReader by creating a new Rodeo and interning all strings.
// This uses rkyv's Deserialize trait to convert each archived value back to the original type.
impl<T: Internable, K, S, D> Deserialize<RodeoReader<T, K, S>, D> for ArchivedRodeoArchive<T, K>
where
    T: Archive + AsRef<T::Ref>,
    Archived<T>: Deserialize<T, D>,
    K: Archive + Key,
    S: BuildHasher + Default,
    Archived<K>: Deserialize<K, D>,
    D: Fallible + ?Sized,
{
    fn deserialize(&self, deserializer: &mut D) -> Result<RodeoReader<T, K, S>, D::Error> {
        // Create a new Rodeo and intern all the strings
        let mut rodeo = crate::Rodeo::<T, K, S>::with_hasher(S::default());

        // Deserialize each archived value and intern it
        // We need to recreate the strings in the same order to preserve key mappings
        for archived_string in self.strings.iter() {
            let value: T = archived_string.deserialize(deserializer)?;
            rodeo.get_or_intern(value);
        }

        // Convert to RodeoReader
        Ok(rodeo.into_reader())
    }
}

/// A string interner that can be serialized with rkyv for zero-copy deserialization
///
/// This type can be created from a [`Rodeo`] or [`RodeoReader`] and serialized using rkyv.
/// The archived form supports zero-copy access - you can directly query the archived data
/// without deserializing it first.
///
/// # Example
///
/// ```rust
/// use lasso::{Rodeo, RodeoArchive};
/// use rkyv::{util::AlignedVec, Archived, api::high::to_bytes_in};
///
/// let mut rodeo: Rodeo = Rodeo::default();
/// let key = rodeo.get_or_intern("Hello, world!");
///
/// // Convert to an archive-ready format
/// let archive = RodeoArchive::from(rodeo);
///
/// // Serialize with rkyv
/// let mut bytes = AlignedVec::<16>::new();
/// to_bytes_in::<_, rkyv::rancor::Error>(&archive, &mut bytes).unwrap();
///
/// // Access the archived data directly (zero-copy)
/// let archived: &Archived<RodeoArchive<String>> = unsafe { rkyv::access_unchecked(&bytes[..]) };
/// assert_eq!(archived.lookup(&key), "Hello, world!");
/// ```
#[derive(Archive, Serialize, Deserialize, Debug)]
pub struct RodeoArchive<T: Internable, K = Spur> {
    /// The interned strings
    /// Stored as owned Strings for serialization
    strings: Vec<T>,

    /// Mapping from string hashes to keys
    /// Serialized with pre-computed hashes using custom wrapper
    #[rkyv(with = HashMapWithHashes<K>)]
    map: Vec<(K, u64)>, // (key, hash_of_string)
}

impl<T, K> RodeoArchive<T, K>
where
    T: Internable,
    K: Key,
{
    /// Creates a new `RodeoArchive` from a `Rodeo`
    ///
    /// This will allocate owned strings for all interned strings and compute hashes
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn from_rodeo<S>(rodeo: Rodeo<T, K, S>) -> Self
    where
        S: BuildHasher,
    {
        let strings: Vec<T> = rodeo.strings.iter().map(|s| T::from_ref(s)).collect();

        // Create entries with (key, hash) pairs
        // The hash is the hash of the string, not the hash of the key
        let entries: Vec<(K, u64)> = rodeo
            .map
            .into_iter()
            .map(|(key, _)| {
                let string = &strings[key.into_usize()];
                let hash = hash_value::<T, rkyv::hash::FxHasher64>(string);
                (key, hash)
            })
            .collect();

        Self {
            strings,
            map: entries,
        }
    }

    /// Creates a new `RodeoArchive` from a `RodeoReader`
    ///
    /// This will allocate owned strings for all interned strings and compute hashes
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn from_reader<S>(reader: RodeoReader<T, K, S>) -> Self
    where
        S: BuildHasher,
    {
        let strings: Vec<T> = reader.strings.iter().map(|s| T::from_ref(*s)).collect();

        // Create entries with (key, hash) pairs
        let entries: Vec<(K, u64)> = reader
            .map
            .into_iter()
            .map(|(key, _)| {
                let string = &strings[key.into_usize()];
                let hash = hash_value::<T, rkyv::hash::FxHasher64>(string);
                (key, hash)
            })
            .collect();

        Self {
            strings,
            map: entries,
        }
    }

    /// Gets the number of interned strings
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn len(&self) -> usize {
        self.strings.len()
    }

    /// Returns `true` if there are no currently interned strings
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn is_empty(&self) -> bool {
        self.strings.is_empty()
    }
}

impl<T: Internable, K, S> From<Rodeo<T, K, S>> for RodeoArchive<T, K>
where
    K: Key,
    S: BuildHasher,
{
    #[cfg_attr(feature = "inline-more", inline)]
    fn from(rodeo: Rodeo<T, K, S>) -> Self {
        Self::from_rodeo(rodeo)
    }
}

impl<T: Internable, K, S> From<RodeoReader<T, K, S>> for RodeoArchive<T, K>
where
    K: Key,
    S: BuildHasher,
{
    #[cfg_attr(feature = "inline-more", inline)]
    fn from(reader: RodeoReader<T, K, S>) -> Self {
        Self::from_reader(reader)
    }
}

// Implement Debug for ArchivedRodeoArchive
impl<T, K> core::fmt::Debug for ArchivedRodeoArchive<T, K>
where
    T: Internable + Archive,
    K: Archive,
    Archived<K>: core::fmt::Debug,
    Archived<T>: core::fmt::Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("ArchivedRodeoArchive")
            .field("strings", &self.strings)
            .field("map", &self.map)
            .finish()
    }
}

// Implement PartialEq for comparison with RodeoReader in rkyv's compare attribute
impl<T: Internable + Archive, K, S> PartialEq<RodeoReader<T, K, S>> for ArchivedRodeoArchive<T, K>
where
    K: Archive + Key,
    Archived<K>: PartialEq<K> + Key,
    T: Archive,
    Archived<T>: ArchivedValueEq<T::Ref>,
    S: BuildHasher,
{
    fn eq(&self, other: &RodeoReader<T, K, S>) -> bool {
        if self.strings.len() != other.strings.len() {
            return false;
        }

        // Check that all strings match
        for (i, archived_string) in self.strings.iter().enumerate() {
            if !archived_string.archived_eq(other.strings[i]) {
                return false;
            }
        }

        true
    }
}

/// Archived version of RodeoArchive provides zero-copy access
///
/// The `lookup` method returns the archived reference type, which may differ from
/// the original type. For example:
/// - `String` -> `&str` (same)
/// - `Vec<u8>` -> `&[u8]` (same)
/// - `Vec<i32>` -> `&[ArchivedI32]` (archived integers)
impl<T, K> ArchivedRodeoArchive<T, K>
where
    T: Internable + Archive,
    Archived<T>: ArchivedInternedRef,
    K: Archive + Hash,
    Archived<K>: Eq + Hash + Copy + Key,
{
    /// Looks up the archived value associated with a given key
    ///
    /// Returns a reference to the archived form of the interned value.
    /// For `String`, this returns `&str`.
    /// For `Vec<T>`, this returns `&[Archived<T>]`.
    ///
    /// # Panics
    ///
    /// Panics if the key is out of bounds
    ///
    /// # Example
    ///
    /// ```rust
    /// use lasso::{Rodeo, RodeoArchive};
    /// use rkyv::{util::AlignedVec, Archived, api::high::to_bytes_in};
    ///
    /// let mut rodeo: Rodeo = Rodeo::default();
    /// let key = rodeo.get_or_intern("Hello, world!");
    ///
    /// let archive = RodeoArchive::from(rodeo);
    /// let mut bytes = AlignedVec::<16>::new();
    /// to_bytes_in::<_, rkyv::rancor::Error>(&archive, &mut bytes).unwrap();
    ///
    /// let archived: &Archived<RodeoArchive<String>> = unsafe { rkyv::access_unchecked(&bytes[..]) };
    /// assert_eq!(archived.lookup(&key), "Hello, world!");
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn lookup(&self, key: &Archived<K>) -> &<Archived<T> as ArchivedInternedRef>::Ref {
        let index = key.into_usize();
        assert!(index < self.strings.len(), "Key out of bounds");
        self.strings[index].as_archived_ref()
    }

    /// Looks up the archived value for a key, returning `None` if it's out of bounds
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn try_lookup(
        &self,
        key: &Archived<K>,
    ) -> Option<&<Archived<T> as ArchivedInternedRef>::Ref> {
        let index = key.into_usize();
        if index < self.strings.len() {
            Some(self.strings[index].as_archived_ref())
        } else {
            None
        }
    }

    /// Looks up the archived value for a key without bounds checks
    ///
    /// # Safety
    ///
    /// The key must be valid for the current archive
    #[cfg_attr(feature = "inline-more", inline)]
    pub unsafe fn lookup_unchecked(
        &self,
        key: &Archived<K>,
    ) -> &<Archived<T> as ArchivedInternedRef>::Ref {
        let index = key.into_usize();
        unsafe { self.strings.get_unchecked(index).as_archived_ref() }
    }

    /// Returns `true` if the given key exists in the current archive
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn contains_key(&self, key: &Archived<K>) -> bool {
        key.into_usize() < self.strings.len()
    }

    /// Gets the number of interned strings
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn len(&self) -> usize {
        self.strings.len()
    }

    /// Returns `true` if there are no currently interned strings
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn is_empty(&self) -> bool {
        self.strings.is_empty()
    }
}

/// Methods for looking up by value (requires `ArchivedValueEq`)
impl<T, K> ArchivedRodeoArchive<T, K>
where
    T: Internable + Archive,
    Archived<T>: ArchivedValueEq<T::Ref>,
    K: Archive + Hash,
    Archived<K>: Eq + Hash + Copy + Key,
{
    /// Get the key value of a string, returning `None` if it doesn't exist
    ///
    /// Note: This requires computing the hash of the string at query time
    ///
    /// # Example
    ///
    /// ```rust
    /// use lasso::{Rodeo, RodeoArchive};
    /// use rkyv::{util::AlignedVec, Archived, api::high::to_bytes_in};
    ///
    /// let mut rodeo: Rodeo = Rodeo::default();
    /// let key = rodeo.get_or_intern("Hello, world!");
    ///
    /// let archive = RodeoArchive::from(rodeo);
    /// let mut bytes = AlignedVec::<16>::new();
    /// to_bytes_in::<_, rkyv::rancor::Error>(&archive, &mut bytes).unwrap();
    ///
    /// let archived: &Archived<RodeoArchive<String>> = unsafe { rkyv::access_unchecked(&bytes[..]) };
    /// assert_eq!(Some(key), archived.get("Hello, world!"));
    /// ```
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn get(&self, val: &T::Ref) -> Option<Archived<K>> {
        // Hash the string using rkyv's hash function
        let hash = hash_value::<T::Ref, rkyv::hash::FxHasher64>(val);

        // Look up in the archived hashmap using raw entry API
        self.map
            .raw_entry()
            .from_hash(hash, |entry| {
                let index = entry.key.into_usize();
                if index < self.strings.len() {
                    self.strings[index].archived_eq(val)
                } else {
                    false
                }
            })
            .map(|(key, _)| *key)
    }

    /// Returns `true` if the given string has been interned
    #[cfg_attr(feature = "inline-more", inline)]
    pub fn contains(&self, val: &T::Ref) -> bool {
        self.get(val).is_some()
    }
}

impl<T, K> core::ops::Index<Archived<K>> for ArchivedRodeoArchive<T, K>
where
    T: Internable + Archive,
    Archived<T>: ArchivedInternedRef,
    K: Archive + Hash,
    Archived<K>: Eq + Hash + Copy + Key,
{
    type Output = <Archived<T> as ArchivedInternedRef>::Ref;

    #[cfg_attr(feature = "inline-more", inline)]
    fn index(&self, key: Archived<K>) -> &Self::Output {
        self.lookup(&key)
    }
}

/// Custom serialization for the HashMap that uses pre-computed hashes
struct HashMapWithHashes<K>(core::marker::PhantomData<K>);

impl<K> ArchiveWith<Vec<(K, u64)>> for HashMapWithHashes<K>
where
    K: Archive,
{
    type Archived = ArchivedHashMap<Archived<K>, ()>;
    type Resolver = HashMapResolver;

    #[inline]
    fn resolve_with(field: &Vec<(K, u64)>, resolver: Self::Resolver, out: Place<Self::Archived>) {
        ArchivedHashMap::<Archived<K>, ()>::resolve_from_len(
            field.len(),
            (7, 8), // load factor
            resolver,
            out,
        );
    }
}

impl<K, S> SerializeWith<Vec<(K, u64)>, S> for HashMapWithHashes<K>
where
    K: Archive + Serialize<S> + Hash + Eq,
    Archived<K>: Hash,
    S: Fallible + Writer + Allocator + ?Sized,
    S::Error: Source,
{
    #[inline]
    fn serialize_with(
        field: &Vec<(K, u64)>,
        serializer: &mut S,
    ) -> Result<Self::Resolver, S::Error> {
        // Use serialize_from_iter_with_hashes with the pre-computed hashes
        ArchivedHashMap::<Archived<K>, ()>::serialize_from_iter_with_hashes::<_, _, _, K, (), _, S>(
            field.iter().map(|(k, _hash)| (k, &())),
            field.iter().map(|(_, hash)| *hash),
            (7, 8), // load factor
            serializer,
        )
    }
}

impl<K, D> DeserializeWith<ArchivedHashMap<Archived<K>, ()>, Vec<(K, u64)>, D>
    for HashMapWithHashes<K>
where
    K: Archive,
    Archived<K>: Deserialize<K, D> + Key,
    D: Fallible + ?Sized,
{
    #[inline]
    fn deserialize_with(
        field: &ArchivedHashMap<Archived<K>, ()>,
        deserializer: &mut D,
    ) -> Result<Vec<(K, u64)>, D::Error> {
        let mut result = Vec::with_capacity(field.len());
        for (k, _) in field.iter() {
            let key = k.deserialize(deserializer)?;
            // We don't have the original hashes when deserializing from archive
            // This is fine since this type is primarily meant for zero-copy access
            result.push((key, 0));
        }
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Rodeo;
    #[cfg(feature = "no-std")]
    use alloc::string::{String, ToString};
    use rkyv::api::high::to_bytes_in;
    use rkyv::util::AlignedVec;

    #[test]
    fn basic_archive() {
        let mut rodeo: Rodeo = Rodeo::default();
        let hello = rodeo.get_or_intern("Hello");
        let world = rodeo.get_or_intern("World");

        let archive = RodeoArchive::from(rodeo);
        assert_eq!(archive.len(), 2);

        let mut bytes = AlignedVec::<16>::new();
        to_bytes_in::<_, rkyv::rancor::Error>(&archive, &mut bytes).unwrap();
        let archived: &Archived<RodeoArchive<String>> =
            unsafe { rkyv::access_unchecked(&bytes[..]) };

        assert_eq!(archived.len(), 2);
        assert_eq!(archived.lookup(&hello), "Hello");
        assert_eq!(archived.lookup(&world), "World");
    }

    #[test]
    fn archive_get() {
        let mut rodeo: Rodeo = Rodeo::default();
        let hello = rodeo.get_or_intern("Hello");
        rodeo.get_or_intern("World");

        let archive = RodeoArchive::from(rodeo);
        let mut bytes = AlignedVec::<16>::new();
        to_bytes_in::<_, rkyv::rancor::Error>(&archive, &mut bytes).unwrap();
        let archived: &Archived<RodeoArchive<String>> =
            unsafe { rkyv::access_unchecked(&bytes[..]) };

        assert_eq!(archived.get("Hello"), Some(hello));
        assert_eq!(archived.get("World").is_some(), true);
        assert_eq!(archived.get("Missing"), None);
    }

    #[test]
    fn archive_contains() {
        let mut rodeo: Rodeo = Rodeo::default();
        rodeo.get_or_intern("Hello");

        let archive = RodeoArchive::from(rodeo);
        let mut bytes = AlignedVec::<16>::new();
        to_bytes_in::<_, rkyv::rancor::Error>(&archive, &mut bytes).unwrap();
        let archived: &Archived<RodeoArchive<String>> =
            unsafe { rkyv::access_unchecked(&bytes[..]) };

        assert!(archived.contains("Hello"));
        assert!(!archived.contains("Missing"));
    }

    #[test]
    fn archive_from_reader() {
        let mut rodeo: Rodeo = Rodeo::default();
        let key = rodeo.get_or_intern("Test");
        let reader = rodeo.into_reader();

        let archive = RodeoArchive::from(reader);
        let mut bytes = AlignedVec::<16>::new();
        to_bytes_in::<_, rkyv::rancor::Error>(&archive, &mut bytes).unwrap();
        let archived: &Archived<RodeoArchive<String>> =
            unsafe { rkyv::access_unchecked(&bytes[..]) };

        assert_eq!(archived.lookup(&key), "Test");
    }

    #[test]
    fn archive_reader_directly() {
        // Test that RodeoReader implements Archive directly
        let mut rodeo: Rodeo = Rodeo::default();
        let hello = rodeo.get_or_intern("Hello");
        let world = rodeo.get_or_intern("World");
        let reader = rodeo.into_reader();

        // Serialize RodeoReader directly (no need to convert to RodeoArchive)
        let mut bytes = AlignedVec::<16>::new();
        to_bytes_in::<_, rkyv::rancor::Error>(&reader, &mut bytes).unwrap();

        // Access archived data
        let archived: &Archived<RodeoReader<String>> =
            unsafe { rkyv::access_unchecked(&bytes[..]) };

        assert_eq!(archived.len(), 2);
        assert_eq!(archived.lookup(&hello), "Hello");
        assert_eq!(archived.lookup(&world), "World");
        assert_eq!(archived.get("Hello"), Some(hello));
        assert!(archived.contains("World"));
    }

    #[test]
    fn archive_reader_in_struct() {
        use crate::RodeoReader;

        #[derive(Debug, rkyv::Archive, rkyv::Serialize, rkyv::Deserialize)]
        #[rkyv(derive(Debug))]
        struct LanguagePack {
            name: String,
            strings: RodeoReader<String>,
        }

        // Create a language pack with many strings
        let mut rodeo: Rodeo = Rodeo::default();
        let greetings = [
            "Hello", "World", "Goodbye", "Welcome", "Thanks", "Please", "Sorry", "Yes", "No",
            "Maybe", "Help", "Stop", "Go", "Wait", "Continue", "Start", "End", "Begin", "Finish",
            "Complete", "Success", "Error", "Warning", "Info", "Debug",
        ];

        let keys: Vec<_> = greetings.iter().map(|s| rodeo.get_or_intern(s)).collect();

        let pack = LanguagePack {
            name: "English".to_string(),
            strings: rodeo.into_reader(),
        };

        // Serialize the struct
        let mut bytes = AlignedVec::<16>::new();
        to_bytes_in::<_, rkyv::rancor::Error>(&pack, &mut bytes).unwrap();

        // Access archived data
        let archived: &Archived<LanguagePack> = unsafe { rkyv::access_unchecked(&bytes[..]) };

        assert_eq!(archived.name, "English");
        assert_eq!(archived.strings.len(), greetings.len());

        // Verify all strings are accessible
        for (key, expected) in keys.iter().zip(greetings.iter()) {
            assert_eq!(archived.strings.lookup(key), *expected);
            assert_eq!(archived.strings.get(expected), Some(*key));
        }

        // Test some specific lookups
        assert!(archived.strings.contains("Hello"));
        assert!(archived.strings.contains("Error"));
        assert!(!archived.strings.contains("Missing"));
    }

    #[test]
    fn deserialize_reader_in_struct() {
        use crate::RodeoReader;

        #[derive(Debug, rkyv::Archive, rkyv::Serialize, rkyv::Deserialize)]
        #[rkyv(derive(Debug))]
        struct LanguagePack {
            name: String,
            strings: RodeoReader<String>,
        }

        // Create a language pack
        let mut rodeo: Rodeo = Rodeo::default();
        let hello = rodeo.get_or_intern("Hello");
        let world = rodeo.get_or_intern("World");
        let goodbye = rodeo.get_or_intern("Goodbye");

        let pack = LanguagePack {
            name: "Test".to_string(),
            strings: rodeo.into_reader(),
        };

        // Serialize
        let mut bytes = AlignedVec::<16>::new();
        to_bytes_in::<_, rkyv::rancor::Error>(&pack, &mut bytes).unwrap();

        // Deserialize
        let archived: &Archived<LanguagePack> = unsafe { rkyv::access_unchecked(&bytes[..]) };
        let deserialized: LanguagePack =
            rkyv::deserialize::<LanguagePack, rkyv::rancor::Error>(archived).unwrap();

        // Verify the deserialized data
        assert_eq!(deserialized.name, "Test");
        assert_eq!(deserialized.strings.len(), 3);
        assert_eq!(deserialized.strings.resolve(&hello), "Hello");
        assert_eq!(deserialized.strings.resolve(&world), "World");
        assert_eq!(deserialized.strings.resolve(&goodbye), "Goodbye");
        assert!(deserialized.strings.contains("Hello"));
    }
}
