//! Example demonstrating rkyv serialization with custom interned types
//!
//! This example shows:
//! 1. Using rkyv with `Vec<u8>` (bytes) as the interned type
//! 2. Using rkyv with `Vec<i32>` as the interned type
//! 3. Using rkyv with a custom struct type `Vec<Atom>` (like n-grams)
//! 4. Zero-copy access to archived data
//!
//! For custom types with complex archived representations, you need to
//! implement `ArchivedValueEq` for `get()` lookups to work.

use lasso::{Rodeo, RodeoArchive, Spur};
use rkyv::{api::high::to_bytes_in, util::AlignedVec, Archive, Archived, Deserialize, Serialize};

fn main() {
    // Example 1: Interning Vec<u8> (bytes) with rkyv serialization
    // This works because u8 archives to itself (u8 == Archived<u8>)
    bytes_example();

    // Example 2: Interning Vec<i32> with rkyv serialization
    // This also works - lookup returns &[ArchivedI32] (little-endian)
    int_vec_example();

    // Example 3: Interning Vec<Atom> with rkyv serialization
    // This demonstrates custom struct types with their own archived representations
    custom_struct_example();
}

/// Example: Interning byte sequences with rkyv serialization
fn bytes_example() {
    println!("=== Bytes Example ===");

    // Create a rodeo that interns Vec<u8> (byte sequences)
    let mut rodeo: Rodeo<Vec<u8>, Spur<Vec<u8>>> = Rodeo::new();

    // Intern some byte sequences
    let hello_bytes = rodeo.get_or_intern(b"Hello".to_vec());
    let world_bytes = rodeo.get_or_intern(b"World".to_vec());
    let binary_data = rodeo.get_or_intern(vec![0x00, 0xFF, 0x42, 0x13, 0x37]);

    println!("Interned {} byte sequences", rodeo.len());
    println!(
        "hello_bytes key: {:?} -> {:?}",
        hello_bytes,
        rodeo.resolve(&hello_bytes)
    );
    println!(
        "world_bytes key: {:?} -> {:?}",
        world_bytes,
        rodeo.resolve(&world_bytes)
    );
    println!(
        "binary_data key: {:?} -> {:?}",
        binary_data,
        rodeo.resolve(&binary_data)
    );

    // Convert to archive and serialize
    let archive = RodeoArchive::from(rodeo);
    let mut bytes = AlignedVec::<16>::new();
    to_bytes_in::<_, rkyv::rancor::Error>(&archive, &mut bytes).unwrap();

    println!("Serialized to {} bytes", bytes.len());

    // Access the archived data (zero-copy)
    let archived: &Archived<RodeoArchive<Vec<u8>, Spur<Vec<u8>>>> =
        unsafe { rkyv::access_unchecked(&bytes[..]) };

    // Lookup by key - returns &[u8]
    assert_eq!(archived.lookup(&hello_bytes), b"Hello".as_slice());
    assert_eq!(archived.lookup(&world_bytes), b"World".as_slice());
    assert_eq!(
        archived.lookup(&binary_data),
        &[0x00, 0xFF, 0x42, 0x13, 0x37]
    );

    // Lookup by value (get) - works for Vec<u8>
    assert_eq!(archived.get(b"Hello".as_slice()), Some(hello_bytes));
    assert_eq!(archived.get(b"World".as_slice()), Some(world_bytes));
    assert_eq!(archived.get(b"Missing".as_slice()), None);

    println!("All lookups successful!");
    println!();
}

/// Example: Interning integer vectors with rkyv serialization
fn int_vec_example() {
    println!("=== Integer Vector Example ===");

    // Create a rodeo that interns Vec<i32>
    let mut rodeo: Rodeo<Vec<i32>, Spur<Vec<i32>>> = Rodeo::new();

    // Intern some integer sequences (could be n-gram indices, coordinates, etc.)
    let seq1 = rodeo.get_or_intern(vec![1, 2, 3]);
    let seq2 = rodeo.get_or_intern(vec![100, 200, 300, 400]);
    let seq3 = rodeo.get_or_intern(vec![-1, 0, 1]);

    println!("Interned {} integer sequences", rodeo.len());

    // Convert to archive and serialize
    let archive = RodeoArchive::from(rodeo);
    let mut bytes = AlignedVec::<16>::new();
    to_bytes_in::<_, rkyv::rancor::Error>(&archive, &mut bytes).unwrap();

    println!("Serialized to {} bytes", bytes.len());

    // Access the archived data (zero-copy)
    let archived: &Archived<RodeoArchive<Vec<i32>, Spur<Vec<i32>>>> =
        unsafe { rkyv::access_unchecked(&bytes[..]) };

    // Lookup by key - returns &[ArchivedI32] (little-endian integers)
    // We can compare with native integers because ArchivedI32 implements PartialEq<i32>
    let lookup1 = archived.lookup(&seq1);
    let lookup2 = archived.lookup(&seq2);
    let lookup3 = archived.lookup(&seq3);

    assert_eq!(lookup1.len(), 3);
    assert_eq!(lookup1[0], 1);
    assert_eq!(lookup1[1], 2);
    assert_eq!(lookup1[2], 3);

    assert_eq!(lookup2.len(), 4);
    assert_eq!(lookup2[0], 100);

    assert_eq!(lookup3.len(), 3);
    assert_eq!(lookup3[0], -1);

    // Lookup by value (get) - works because we implemented ArchivedValueEq for integer types
    assert_eq!(archived.get([1, 2, 3].as_slice()), Some(seq1));
    assert_eq!(archived.get([100, 200, 300, 400].as_slice()), Some(seq2));
    assert_eq!(archived.get([42, 42, 42].as_slice()), None);

    // contains() also works
    assert!(archived.contains([1, 2, 3].as_slice()));
    assert!(!archived.contains([999, 999].as_slice()));

    println!("All lookups successful!");
    println!();
}

// ============================================================================
// Example 3: Custom struct type
// ============================================================================

/// A simple "atom" type that wraps an index, similar to what you might use
/// in NLP for word indices or in compilers for symbol indices.
///
/// This demonstrates how to use rkyv with custom types.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Archive, Serialize, Deserialize)]
#[rkyv(derive(Debug, Hash, PartialEq, Eq))]
struct Atom {
    /// The index of this atom in some vocabulary
    index: u32,
}

impl Atom {
    fn new(index: u32) -> Self {
        Self { index }
    }
}

// Implement comparison between archived and original Atom.
// This is all you need! The generic ArchivedValueEq impl in lasso will
// automatically work for Vec<Atom> because ArchivedAtom: PartialEq<Atom>.
impl PartialEq<Atom> for ArchivedAtom {
    fn eq(&self, other: &Atom) -> bool {
        self.index == other.index
    }
}

/// Example: Interning n-grams (sequences of atoms) with rkyv serialization
fn custom_struct_example() {
    println!("=== Custom Struct (Atom) Example ===");

    // Create a rodeo that interns Vec<Atom> (n-grams)
    let mut rodeo: Rodeo<Vec<Atom>, Spur<Vec<Atom>>> = Rodeo::new();

    // Intern some n-grams (sequences of word indices)
    let bigram1 = rodeo.get_or_intern(vec![Atom::new(1), Atom::new(2)]);
    let bigram2 = rodeo.get_or_intern(vec![Atom::new(3), Atom::new(4)]);
    let trigram = rodeo.get_or_intern(vec![Atom::new(1), Atom::new(2), Atom::new(3)]);

    println!("Interned {} n-grams", rodeo.len());
    println!("bigram1: {:?}", rodeo.resolve(&bigram1));
    println!("bigram2: {:?}", rodeo.resolve(&bigram2));
    println!("trigram: {:?}", rodeo.resolve(&trigram));

    // Convert to archive and serialize
    let archive = RodeoArchive::from(rodeo);
    let mut bytes = AlignedVec::<16>::new();
    to_bytes_in::<_, rkyv::rancor::Error>(&archive, &mut bytes).unwrap();

    println!("Serialized to {} bytes", bytes.len());

    // Access the archived data (zero-copy)
    let archived: &Archived<RodeoArchive<Vec<Atom>, Spur<Vec<Atom>>>> =
        unsafe { rkyv::access_unchecked(&bytes[..]) };

    // Lookup by key - returns &[ArchivedAtom]
    let lookup1 = archived.lookup(&bigram1);
    assert_eq!(lookup1.len(), 2);
    assert_eq!(lookup1[0].index, 1);
    assert_eq!(lookup1[1].index, 2);

    let lookup2 = archived.lookup(&trigram);
    assert_eq!(lookup2.len(), 3);

    // Lookup by value (get) - works because we implemented ArchivedValueEq
    assert_eq!(archived.get(&[Atom::new(1), Atom::new(2)]), Some(bigram1));
    assert_eq!(archived.get(&[Atom::new(3), Atom::new(4)]), Some(bigram2));
    assert_eq!(
        archived.get(&[Atom::new(1), Atom::new(2), Atom::new(3)]),
        Some(trigram)
    );
    assert_eq!(archived.get(&[Atom::new(99), Atom::new(99)]), None);

    // contains() also works
    assert!(archived.contains(&[Atom::new(1), Atom::new(2)]));
    assert!(!archived.contains(&[Atom::new(999)]));

    println!("All lookups successful!");
    println!();
}
