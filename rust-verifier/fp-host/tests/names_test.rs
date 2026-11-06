//! The Rust rejection-name table must be exactly `verifier/src/vf_rejection_names.txt`, in order,
//! with every entry carrying a source pointer and a test-coverage note (TL review A4).

use fp_core::names::REJECTION_NAMES;

const ORIGINAL: &str = include_str!("../../fixtures/vf_rejection_names.txt");

#[test]
fn table_has_the_same_names_in_the_same_order() {
    let want: Vec<&str> = ORIGINAL.lines().filter(|l| !l.trim().is_empty()).collect();
    assert_eq!(want.len(), 304, "the C++ list has 304 entries");
    assert_eq!(REJECTION_NAMES.len(), want.len());
    for (i, (got, expected)) in REJECTION_NAMES.iter().zip(want.iter()).enumerate() {
        assert_eq!(&got.name, expected, "entry {}", i);
        assert!(!got.source.is_empty(), "entry {} has no source", i);
        assert!(!got.tests.is_empty(), "entry {} has no test note", i);
    }
}

#[test]
fn the_named_test_sources_are_recorded() {
    let find = |name: &str| {
        REJECTION_NAMES
            .iter()
            .find(|r| r.name == name)
            .unwrap_or_else(|| panic!("missing rejection name {}", name))
    };
    assert!(
        find("model-statement").tests.contains("commitment_id_test.py"),
        "A4: commitment_id_test.py must be recorded for model-statement"
    );
    for name in ["policy", "statement-range", "statement-required"] {
        assert!(
            find(name).tests.contains("what_a_yes_covers_test.py"),
            "A4: what_a_yes_covers_test.py must be recorded for {}",
            name
        );
    }
    assert!(
        find("forest-calls").tests.contains("known_answers/forest_values.py"),
        "A4: known_answers/forest_values.py must be recorded for forest-calls"
    );
}
