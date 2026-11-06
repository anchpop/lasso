use lasso::{ArchivedInternedRef, InternableValue, Key, Rodeo, RodeoArchive, RodeoReader};
use rkyv::{Archive, Deserialize, Serialize};
use std::num::NonZeroU32;

// Includes padding as well as the optional fields used by a reading-tagged gram.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Archive, Serialize, Deserialize)]
struct Gram {
    gram: u32,
    sense: Option<NonZeroU32>,
    reading: Option<u32>,
    tag: u8,
}
impl AsRef<Gram> for Gram {
    fn as_ref(&self) -> &Self {
        self
    }
}
impl InternableValue for Gram {}
impl ArchivedInternedRef for ArchivedGram {
    type Ref = Self;
    fn as_archived_ref(&self) -> &Self {
        self
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash, Archive, Serialize, Deserialize)]
#[rkyv(derive(Copy, Clone, Eq, PartialEq, Hash))]
struct Rank(u32);
// Safety: conversions preserve every accepted index exactly.
unsafe impl Key for Rank {
    fn into_usize(self) -> usize {
        self.0 as usize
    }
    fn try_from_usize(i: usize) -> Option<Self> {
        u32::try_from(i).ok().map(Self)
    }
}
// Safety: same mapping, using the archived integer representation.
unsafe impl Key for ArchivedRank {
    fn into_usize(self) -> usize {
        self.0.to_native() as usize
    }
    fn try_from_usize(i: usize) -> Option<Self> {
        u32::try_from(i).ok().map(|i| Self(i.into()))
    }
}

#[test]
fn values_preserve_order_and_archive() {
    let mut rodeo = Rodeo::<Gram, Rank>::with_first_key(Rank(37));
    let values: Vec<_> = (0..1000)
        .map(|i| Gram {
            gram: 1000 - i,
            sense: NonZeroU32::new(i % 3),
            reading: (i % 2 == 0).then_some(i),
            tag: i as u8,
        })
        .collect();
    for (i, &value) in values.iter().enumerate() {
        let key = rodeo.get_or_intern(value);
        assert_eq!(key.into_usize(), i + 37);
        assert_eq!(rodeo.get_or_intern(value), key);
        assert_eq!(rodeo.resolve(&key), &value);
    }
    let resolver = rodeo.clone().into_resolver();
    let reader = rodeo.clone().into_reader();
    let archive = RodeoArchive::from(rodeo);
    let bytes = rkyv::to_bytes::<rkyv::rancor::Error>(&archive).unwrap();
    let archived =
        rkyv::access::<rkyv::Archived<RodeoArchive<Gram, Rank>>, rkyv::rancor::Error>(&bytes)
            .unwrap();
    let restored: RodeoReader<Gram, Rank> =
        rkyv::deserialize::<_, rkyv::rancor::Error>(archived).unwrap();
    for (i, value) in values.iter().enumerate() {
        let key = Rank::try_from_usize(i + 37).unwrap();
        assert_eq!(resolver.resolve(&key), value);
        assert_eq!(reader.resolve(&key), value);
        assert_eq!(restored.resolve(&key), value);
        let archived_key = ArchivedRank::try_from_usize(i + 37).unwrap();
        let decoded: Gram =
            rkyv::deserialize::<_, rkyv::rancor::Error>(archived.resolve(&archived_key)).unwrap();
        assert_eq!(&decoded, value);
    }
}
