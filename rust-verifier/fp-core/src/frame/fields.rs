//! The fields of a key, leaf or proof file (`blocks/frame/fields.h`): name, offset, length and
//! class, one per `PlanMessage`, contiguous from offset 0.

use alloc::format;
use alloc::string::String;
use alloc::vec::Vec;

use crate::numbers::plan::{MessageKind, Planned};

/// One field of a file (`Field`, fields.h:28-33).
#[derive(Clone, Debug, PartialEq)]
pub struct Field {
    pub name: String,
    pub at: u64,
    pub bytes: u64,
    pub cls: &'static str,
    pub exact: bool,
}

/// What a reader does with a message's bytes (`class_of`, fields.h:35-47).
pub fn class_of(k: MessageKind) -> &'static str {
    match k {
        MessageKind::Scalars | MessageKind::Answers | MessageKind::Columns => "elements",
        MessageKind::Root | MessageKind::Paths => "digest",
        MessageKind::Nonce => "nonce",
        MessageKind::Salts => "salt",
        MessageKind::Head => "words",
    }
}

/// The fields of one part (`fields_of`, fields.h:50-65). A plan with repeats has no places; C++'s
/// `BLK_REQUIRE` ends the process, so this panics with the same text.
pub fn fields_of(p: &Planned, part: u32) -> Vec<Field> {
    let mut v = Vec::new();
    let mut at = 0u64;
    let mut exact = true;
    for m in &p.messages {
        if m.part != part {
            continue;
        }
        assert_eq!(m.count, 1, "fields_of: a plan with repeats has no places");
        let name = if m.where_.is_empty() {
            m.name.clone()
        } else {
            format!("{}: {}", m.where_, m.name)
        };
        v.push(Field { name, at, bytes: m.bytes, cls: class_of(m.kind), exact });
        at += m.bytes;
        if m.expected != m.bytes as f64 {
            exact = false;
        }
    }
    v
}
