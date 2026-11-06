//! Pure output helpers used by the driver and, later, by the stage runner.
//!
//! Ported from `verifier/src/cp_verify.cpp:2560-2595` and `verifier/src/vf_common.h:298-315`.
//! Nothing here writes to a file or a stream; callers own the I/O.

use alloc::format;
use alloc::string::String;

/// Returns the rest of the last line of `out` that begins with `key`, or `""`.
///
/// `cpLineOf()` (`cp_verify.cpp:2569-2580`). The C++ code searches for `"\n" + key` from the
/// end; if that is absent it accepts `key` at the very start. It then returns the bytes up to
/// the next line feed.
pub fn cp_line_of(out: &str, key: &str) -> String {
    let needle = format!("\n{}", key);
    let at = match out.rfind(&needle) {
        Some(at) => at + 1,
        None => {
            if !out.starts_with(key) {
                return String::new();
            }
            0
        }
    };
    let end = out[at..].find('\n').map(|n| at + n).unwrap_or(out.len());
    String::from(&out[at + key.len()..end])
}

/// Returns `": <why>"` when the line before the last `NO: ..` line is `key: <why>`,
/// `entry: <why>` or `proof: <why>`, and `""` otherwise.
///
/// `cpReasonOf()` (`cp_verify.cpp:2583-2595`). The rejection's last lines must not show text
/// read from a file, so `why` may contain only ASCII letters and ` ,.:;'()-`.
pub fn cp_reason_of(out: &str) -> String {
    let no = match out.rfind("\nNO: ") {
        Some(no) if no != 0 => no,
        _ => return String::new(),
    };
    let from = out[..no].rfind('\n').map(|n| n + 1).unwrap_or(0);
    let line = &out[from..no];
    for head in ["key: ", "entry: ", "proof: "] {
        if let Some(why) = line.strip_prefix(head) {
            if why.is_empty() || !why.bytes().all(is_reason_byte) {
                return String::new();
            }
            return format!(": {}", why);
        }
    }
    String::new()
}

/// The bytes that C++ allows in a rejection's reason (`isalpha` under `LC_ALL=C`, plus
/// `" ,.:;'()-"`).
fn is_reason_byte(c: u8) -> bool {
    c.is_ascii_alphabetic() || matches!(c, b' ' | b',' | b'.' | b':' | b';' | b'\'' | b'(' | b')' | b'-')
}

/// `NO: <name>` and its line feed, as `refuse()` prints it (`vf_common.h:56`).
pub fn no_line(name: &str) -> String {
    format!("NO: {}\n", name)
}

/// `NOT CHECKED: <name>` (`cp_verify.cpp:2564`).
pub fn not_checked_line(name: &str) -> String {
    format!("NOT CHECKED: {}\n", name)
}

/// The two lines of `cpNotChecked()` (`cp_verify.cpp:2560-2566`).
///
/// `name` keeps a sub-proof prefix if it has one; only the bare part after the last `:` decides
/// whether the cause may be the machine.
pub fn cp_not_checked_lines(how: &str, name: &str) -> String {
    let bare = name.rsplit(':').next().unwrap_or(name);
    let machine = bare == "internal-stage" || bare == "internal-exception-parFor";
    let head = if machine {
        "the verifier itself failed: nothing has been verified. The cause may be the machine (a want of memory, for one) or the program (a guard that ended a stage has left its line on standard error); what the program causes comes again on the same files"
    } else {
        "a guard of the verifier's own spoke: nothing has been verified, and on the same files the call ends so again"
    };
    format!("{}: {}\n{}", head, how, not_checked_line(name))
}

/// `input-unreadable-<role>: <what> cannot be read: <why>` (`vf_common.h:302-312`).
///
/// `why` is `None` when C++ would print the generic sentence (`errno == 0`: not a regular file,
/// or a short read).
pub fn input_unreadable_line(role: &str, what: &str, why: Option<&str>) -> String {
    match why {
        Some(why) => format!("input-unreadable-{}: {} cannot be read: {}\n", role, what, why),
        None => format!(
            "input-unreadable-{}: {} cannot be read: it is not a regular file, or the read came up short\n",
            role, what
        ),
    }
}

/// What `input-unreadable` prints for each role (`vf_common.h:304-306`).
pub fn role_name(role: &str) -> &'static str {
    match role {
        "policy" => "policy.txt",
        "KL" => "KL.bin",
        "layout" => "layout.txt",
        "key" => "key.bin",
        "entry" => "the entry file",
        "request" => "the request file",
        "y" => "the y file",
        "proof" => "the proof file",
        _ => "an input file",
    }
}
