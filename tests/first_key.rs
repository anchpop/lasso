use lasso::{ArchivedCompressedRodeoResolver, Key, Rodeo, RodeoArchive, RodeoReader, Spur};

fn key(id: usize) -> Spur {
    Spur::try_from_usize(id).unwrap()
}

fn populated() -> Rodeo {
    let mut rodeo = Rodeo::with_first_key(key(37));
    for i in 0..200 {
        assert_eq!(rodeo.get_or_intern(i.to_string()), key(37 + i));
    }
    assert_eq!(rodeo.get_or_intern_static("0"), key(37));
    rodeo
}

#[test]
fn offset_survives_owned_paths() {
    let rodeo = populated();
    let reader = rodeo.clone().into_reader();
    let resolver = rodeo.clone().into_resolver();
    let via_reader = rodeo.clone().into_reader().into_resolver();
    let zero: Rodeo = (0..200).map(|i| i.to_string()).collect();
    assert_eq!(rodeo, reader);
    assert_eq!(reader, resolver);
    assert_eq!(resolver, via_reader);
    assert_ne!(rodeo, zero);
    assert_ne!(reader, zero);
    assert_ne!(resolver, zero);
    assert_ne!(reader, zero.clone().into_reader());
    assert_ne!(resolver, zero.clone().into_resolver());
    macro_rules! check {
        ($owner:expr) => {{
            let owner = &$owner;
            assert_eq!(owner.len(), 200);
            assert_eq!(owner.resolve(&key(37)), "0");
            assert_eq!(&owner[key(236)], "199");
            assert_eq!(unsafe { owner.resolve_unchecked(&key(38)) }, "1");
            for invalid in [key(0), key(36), key(237)] {
                assert!(!owner.contains_key(&invalid));
                assert!(owner.try_resolve(&invalid).is_none());
                assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(
                    || owner.resolve(&invalid)
                ))
                .is_err());
            }
            assert_eq!(owner.iter().next(), Some((key(37), "0")));
            assert_eq!(owner.iter().next_back(), Some((key(236), "199")));
            assert_eq!(owner.iter().nth_back(198), Some((key(38), "1")));
            assert_eq!(owner.strings().count(), 200);
        }};
    }
    check!(rodeo);
    check!(reader);
    check!(resolver);
    check!(via_reader);
    for i in 0..200 {
        assert_eq!(reader.get(i.to_string()), Some(key(37 + i)));
    }
    let mut cloned = zero;
    cloned.clone_from(&rodeo);
    assert_eq!(cloned, rodeo);
    cloned.clear();
    assert_eq!(cloned.get_or_intern_static("again"), key(37));
    let last = lasso::MicroSpur::<String>::try_from_usize(254).unwrap();
    let mut tiny = Rodeo::<String, lasso::MicroSpur<String>>::with_first_key(last);
    assert_eq!(tiny.get_or_intern("last"), last);
    assert!(tiny.try_get_or_intern("overflow").is_err());
}

#[test]
fn archive_preserves_offset() {
    let rodeo = populated();
    let reader = rodeo.clone().into_reader();
    let archives = [
        RodeoArchive::from_rodeo(rodeo),
        RodeoArchive::from_reader(populated().into_reader()),
    ];
    for bytes in archives
        .iter()
        .map(|a| rkyv::to_bytes::<rkyv::rancor::Error>(a).unwrap())
        .chain([rkyv::to_bytes::<rkyv::rancor::Error>(&reader).unwrap()])
    {
        let archived =
            rkyv::access::<rkyv::Archived<RodeoArchive<String>>, rkyv::rancor::Error>(&bytes)
                .unwrap();
        let first = archived.get("0").unwrap();
        assert_eq!(first.into_usize(), 37);
        assert_eq!(archived.resolve(&first), "0");
        assert_eq!(archived.iter().next(), Some((key(37), "0")));
        assert_eq!(archived.iter().next_back(), Some((key(236), "199")));
        assert_eq!(archived.iter().len(), 200);
        assert!(archived.strings().eq(reader.strings()));
        assert_eq!(&archived[first], "0");
        assert_eq!(unsafe { archived.resolve_unchecked(&first) }, "0");
        assert!(archived == &reader);
        let zero: Rodeo = (0..200).map(|i| i.to_string()).collect();
        assert!(archived != &zero.into_reader());
        for id in [0, 36, 237] {
            let invalid = <rkyv::Archived<Spur> as Key>::try_from_usize(id).unwrap();
            assert!(!archived.contains_key(&invalid));
            assert!(archived.try_resolve(&invalid).is_none());
        }
        let restored: RodeoReader = rkyv::deserialize::<_, rkyv::rancor::Error>(archived).unwrap();
        assert_eq!(restored, reader);
        assert_eq!(restored.get("199"), Some(key(236)));
        let restored: RodeoArchive<String> =
            rkyv::deserialize::<_, rkyv::rancor::Error>(archived).unwrap();
        assert_eq!(restored.len(), 200);
        let bytes = rkyv::to_bytes::<rkyv::rancor::Error>(&restored).unwrap();
        let archived =
            rkyv::access::<rkyv::Archived<RodeoArchive<String>>, rkyv::rancor::Error>(&bytes)
                .unwrap();
        assert_eq!(archived.get("199").unwrap().into_usize(), 236);
    }
}

#[test]
fn compressed_preserves_deduplicated_offset_keys() {
    type E = Spur<()>;
    let mut rodeo = Rodeo::<Vec<E>, Spur>::with_first_key(key(37));
    let elements = [
        E::try_from_usize(0).unwrap(),
        E::try_from_usize(1_000_000).unwrap(),
    ];
    assert_eq!(rodeo.get_or_intern(elements), key(37));
    assert_eq!(rodeo.get_or_intern(elements), key(37));
    assert_eq!(rodeo.get_or_intern([]), key(38));
    let direct = rodeo.clone().into_compressed_resolver();
    let via_reader = rodeo.into_reader().into_compressed_resolver();
    let bytes = rkyv::to_bytes::<rkyv::rancor::Error>(&direct).unwrap();
    assert_eq!(
        bytes.as_slice(),
        rkyv::to_bytes::<rkyv::rancor::Error>(&via_reader)
            .unwrap()
            .as_slice()
    );
    let archived =
        rkyv::access::<ArchivedCompressedRodeoResolver<Spur, Vec<E>>, rkyv::rancor::Error>(&bytes)
            .unwrap();
    let restored: lasso::CompressedRodeoResolver<Spur, Vec<E>> =
        rkyv::deserialize::<_, rkyv::rancor::Error>(archived).unwrap();
    macro_rules! check {
        ($owner:expr) => {{
            let owner = &$owner;
            assert_eq!(owner.len(), 2);
            assert_eq!(
                owner
                    .resolve(&key(37))
                    .map(|element| element.into_usize())
                    .collect::<Vec<_>>(),
                elements.map(Key::into_usize)
            );
            assert_eq!(owner.resolve(&key(38)).count(), 0);
            assert_eq!(
                owner.iter().map(|(k, _)| k).collect::<Vec<_>>(),
                [key(37), key(38)]
            );
            for invalid in [key(0), key(36), key(39)] {
                assert!(!owner.contains_key(&invalid));
                assert!(owner.try_resolve(&invalid).is_none());
            }
        }};
    }
    check!(direct);
    check!(via_reader);
    check!(archived);
    check!(restored);
}

#[cfg(feature = "serialize")]
#[test]
fn serde_preserves_offset() {
    let rodeo = populated();
    let json = serde_json::to_string(&rodeo).unwrap();
    let mut restored: Rodeo = serde_json::from_str(&json).unwrap();
    assert_eq!(restored, rodeo);
    assert_eq!(restored.get_or_intern("next"), key(237));
    let reader = rodeo.clone().into_reader();
    let restored: RodeoReader =
        serde_json::from_str(&serde_json::to_string(&reader).unwrap()).unwrap();
    assert_eq!(restored, reader);
    let resolver = rodeo.into_resolver();
    let restored: lasso::RodeoResolver =
        serde_json::from_str(&serde_json::to_string(&resolver).unwrap()).unwrap();
    assert_eq!(restored, resolver);
}

#[cfg(feature = "multi-threaded")]
#[test]
fn threaded_conversions_stay_zero_based() {
    let threaded = lasso::ThreadedRodeo::default();
    threaded.get_or_intern("0");
    let mut offset = Rodeo::with_first_key(key(37));
    offset.get_or_intern("0");
    assert_ne!(threaded, offset);
    assert_ne!(threaded, offset.clone().into_reader());
    assert_ne!(threaded, offset.into_resolver());
    assert_eq!(threaded.into_reader().iter().next(), Some((key(0), "0")));
    #[cfg(feature = "serialize")]
    {
        let threaded = lasso::ThreadedRodeo::default();
        threaded.get_or_intern("a");
        let json = serde_json::to_string(&threaded).unwrap();
        let restored: lasso::ThreadedRodeo = serde_json::from_str(&json).unwrap();
        assert_eq!(restored.get_or_intern("b"), key(1));
        assert_eq!(restored.into_resolver().resolve(&key(0)), "a");
        let mut invalid = std::collections::HashMap::new();
        invalid.insert("a", key(37));
        let json = serde_json::to_string(&invalid).unwrap();
        assert!(serde_json::from_str::<lasso::ThreadedRodeo>(&json).is_err());
    }
}
