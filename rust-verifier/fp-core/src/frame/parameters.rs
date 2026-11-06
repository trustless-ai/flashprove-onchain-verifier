//! The frame's lines of the parameter file and its one strict parser, ported from
//! `blocks/frame/parameters.h`.
//!
//! A line is a name and its values, separated by single spaces and ended by a line feed. A value is
//! a decimal number without sign or leading zero; the version is four characters. A blank line, a
//! comment, a carriage return, or anything before the first line is rejected. Every byte of the
//! file enters the configuration digest, which every hash chain's first query contains.
//!
//! Only free choices have a line. The rest is derived (`derive.rs`), and `configure` rejects a file
//! under which a round misses its target. This parser checks syntax, ranges and shapes only.

use alloc::format;
use alloc::string::{String, ToString};
use alloc::vec;
use alloc::vec::Vec;

use crate::consts::PROGRAM_VERSION_WORD;
use crate::head::version_from_text;

/// The largest `n` of a `group` or `stages` line (`MOST_GROUP_LOG_N`, parameters.h:163).
pub const MOST_GROUP_LOG_N: u64 = 32;

/// One stage after the first of a proximity test (`StageChoice`, blocks/numbers/blocks.h:836-839).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct StageChoice {
    pub k: u32,
    pub h: u32,
    pub log_n: u32,
    pub mask_log_n: u32,
}

/// The lines `group <name> J n l nz lz` and `stages <name> k h n nz ..` of one group
/// (`GroupLine`, parameters.h:40-43).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct GroupLine {
    pub log_n: u32,
    pub log_ell: u32,
    pub mask_log_n: u32,
    pub mask_log_ell: u32,
    pub stages: Vec<StageChoice>,
}

/// The frame's lines, in their order (`Parameters`, parameters.h:89-101).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Parameters {
    pub version: u32,
    pub sec: u32,
    pub slots: u64,
    pub answers: u32,
    /// By `ErrorKind` (`FIELD` to `SMALL`, the lines' order) and `Scope`.
    pub work: [[u32; 3]; 5],
    pub salt: u32,
    pub link: GroupLine,
    pub folded: GroupLine,
    pub omega: GroupLine,
    pub own: GroupLine,
    pub once_folded: GroupLine,
    pub once_omega: GroupLine,
    pub once_own: GroupLine,
    pub once_ranges: GroupLine,
    pub ranges_part: u32,
    pub table_rows_log: u32,
    pub table_log_n: u32,
    pub block_log: u32,
    pub table_data: u64,
    pub table_random: u64,
    /// The lines after the frame, on the model and its sub-proofs, unread here.
    pub rest: Vec<u8>,
}

/// Reads a text line by line, keeping only the first failure (`StrictLines`, parameters.h:105-157).
pub struct StrictLines<'a> {
    t: &'a [u8],
    at: usize,
    line: u32,
    why: String,
}

impl<'a> StrictLines<'a> {
    pub fn new(text: &'a [u8]) -> Self {
        StrictLines { t: text, at: 0, line: 0, why: String::new() }
    }

    pub fn ok(&self) -> bool {
        self.why.is_empty()
    }

    pub fn why(&self) -> &str {
        &self.why
    }

    /// `StrictLines::refuse()` (parameters.h:110-112): the first reason wins, with its line number.
    pub fn refuse(&mut self, why: &str) {
        if self.why.is_empty() {
            self.why = format_line(why, self.line);
        }
    }

    /// `StrictLines::numbers()` (parameters.h:117-130). After a failure the result is `count` zeros
    /// (one if `count` is negative), so a caller may index it.
    pub fn numbers(&mut self, head: &str, count: i32) -> Vec<u64> {
        let words = self.words(head, count);
        let mut v = Vec::with_capacity(words.len());
        for w in words {
            let mut x = 0u64;
            if w.is_empty() || w.len() > 15 || (w[0] == b'0' && w.len() > 1) {
                self.refuse("parameter-number-spelling");
            }
            for &c in w {
                if !c.is_ascii_digit() {
                    self.refuse("parameter-number-spelling");
                }
                x = 10 * x + (c - b'0') as u64;
            }
            v.push(x);
        }
        if !self.ok() {
            v = vec![0; if count < 0 { 1 } else { count as usize }];
        }
        v
    }

    /// `StrictLines::words()` (parameters.h:132-149). As there, after a failure the result may have
    /// any length, even zero.
    pub fn words(&mut self, head: &str, count: i32) -> Vec<&'a [u8]> {
        self.line += 1;
        let mut v = Vec::new();
        if !self.ok() {
            return v;
        }
        let Some(end) = self.t[self.at..].iter().position(|&c| c == b'\n') else {
            self.refuse(&format!("parameter-line-missing: {}", head));
            return v;
        };
        let end = self.at + end;
        let l = &self.t[self.at..end];
        self.at = end + 1;
        let hb = head.as_bytes();
        if l.len() < hb.len() + 1 || &l[..hb.len()] != hb || l[hb.len()] != b' ' {
            self.refuse(&format!("parameter-line-order: {}", head));
            return v;
        }
        let mut i = hb.len() + 1;
        loop {
            let j = l[i..].iter().position(|&c| c == b' ').map(|x| i + x);
            let word = match j {
                Some(j) => {
                    let w = &l[i..j];
                    i = j + 1;
                    w
                }
                None => &l[i..],
            };
            if word.is_empty() {
                self.refuse(&format!("parameter-line-blanks: {}", head));
                return v;
            }
            v.push(word);
            if j.is_none() {
                break;
            }
        }
        if count >= 0 && v.len() != count as usize {
            self.refuse(&format!("parameter-line-values: {}", head));
        }
        v
    }

    /// The lines after those read so far (`StrictLines::rest()`, parameters.h:150).
    pub fn rest(&self) -> Vec<u8> {
        self.t[self.at..].to_vec()
    }
}

fn format_line(why: &str, line: u32) -> String {
    let mut s = String::from(why);
    s.push_str(" (line ");
    s.push_str(&line.to_string());
    s.push(')');
    s
}

/// Reads one `group`/`stages` pair (`read_group`, parameters.h:165-177).
fn read_group(inp: &mut StrictLines<'_>, name: &str, g: &mut GroupLine) {
    let a = inp.numbers(&format!("group {}", name), 5);
    g.log_n = a[1] as u32;
    g.log_ell = a[2] as u32;
    g.mask_log_n = a[3] as u32;
    g.mask_log_ell = a[4] as u32;
    if a[0] != 1 || a[1] > MOST_GROUP_LOG_N || a[2] >= a[1] || a[3] > a[1] || a[4] >= a[3] {
        inp.refuse(&format!("parameter-group-shape: {}", name));
    }
    let s = inp.numbers(&format!("stages {}", name), -1);
    if s.len() % 4 != 0 || s.len() > 32 {
        inp.refuse(&format!("parameter-stages-count: {}", name));
        return;
    }
    for i in (0..s.len()).step_by(4) {
        let last = i + 4 == s.len();
        if s[i] > 8 || s[i + 1] > s[i] || s[i + 2] > MOST_GROUP_LOG_N || s[i + 3] > s[i + 2]
            || (if last { s[i] != 0 } else { s[i] == 0 })
        {
            inp.refuse(&format!("parameter-stages-shape: {}", name));
            return;
        }
        g.stages.push(StageChoice {
            k: s[i] as u32,
            h: s[i + 1] as u32,
            log_n: s[i + 2] as u32,
            mask_log_n: s[i + 3] as u32,
        });
    }
}

/// Reads the frame's lines (`read_parameters`, parameters.h:181-235). Only syntax, ranges and
/// shapes are checked; whether the parameters reach their target is `derive`/`configure`'s work.
pub fn read_parameters(text: &[u8], p: &mut Parameters) -> Result<(), String> {
    *p = Parameters::default();
    let mut inp = StrictLines::new(text);
    let v = inp.words("version", 1);
    p.version = match v.first() {
        Some(w) => version_from_text(w),
        None => 0,
    };
    if inp.ok() && p.version != PROGRAM_VERSION_WORD {
        inp.refuse("version-unknown");
    }

    let one = |inp: &mut StrictLines<'_>, name: &str, lo: u64, hi: u64| -> u64 {
        let x = inp.numbers(name, 1)[0];
        if x < lo || x > hi {
            inp.refuse(&format!("parameter-range: {}", name));
        }
        x
    };
    p.sec = one(&mut inp, "sec", 1, 256) as u32;
    let _reading = one(&mut inp, "reading", 1, 1);
    let _rowcost = one(&mut inp, "rowcost", 1, 1);
    p.slots = one(&mut inp, "slots", 1, 1u64 << 20);
    if p.slots & p.slots.wrapping_sub(1) != 0 {
        inp.refuse("parameter-range: slots");
    }
    p.answers = one(&mut inp, "answers", 1, 1) as u32;
    let _record = one(&mut inp, "record", 1, 1);
    let kind = ["work field", "work sample", "work closeness", "work positions", "work smallness"];
    for (k, name) in kind.iter().enumerate() {
        let w = inp.numbers(name, 3);
        for s in 0..3 {
            p.work[k][s] = w[s] as u32;
            if w[s] > 58 || w[s] >= p.sec as u64 {
                inp.refuse(&format!("parameter-range: {}", name));
            }
        }
    }
    p.salt = one(&mut inp, "salt", 40, 64) as u32;
    if p.salt % 8 != 0 {
        inp.refuse("parameter-range: salt");
    }
    let _listed = one(&mut inp, "listed", 0, 0);
    read_group(&mut inp, "link", &mut p.link);
    read_group(&mut inp, "folded", &mut p.folded);
    read_group(&mut inp, "omega", &mut p.omega);
    read_group(&mut inp, "own", &mut p.own);
    read_group(&mut inp, "once-folded", &mut p.once_folded);
    read_group(&mut inp, "once-omega", &mut p.once_omega);
    read_group(&mut inp, "once-own", &mut p.once_own);
    read_group(&mut inp, "once-ranges", &mut p.once_ranges);
    p.ranges_part = one(&mut inp, "ranges-part", 1, 40) as u32;
    if inp.ok()
        && (p.own.log_n != p.omega.log_n
            || p.own.log_ell != p.omega.log_ell
            || p.once_own.log_n != p.once_omega.log_n
            || p.once_own.log_ell != p.once_omega.log_ell)
    {
        inp.refuse("parameter-own-code");
    }
    if inp.ok()
        && (p.folded.mask_log_n != p.omega.mask_log_n
            || p.folded.mask_log_ell != p.omega.mask_log_ell
            || p.once_folded.mask_log_n != p.once_omega.mask_log_n
            || p.once_folded.mask_log_ell != p.once_omega.mask_log_ell)
    {
        inp.refuse("parameter-one-mask-code");
    }
    let t = inp.numbers("table", 6);
    p.table_rows_log = t[0] as u32;
    p.table_log_n = t[1] as u32;
    p.table_data = t[2];
    p.table_random = t[3];
    p.block_log = t[5] as u32;
    if inp.ok()
        && (t[0] > 20
            || t[1] > 32
            || t[2] == 0
            || t[2] + t[3] >= (1u64 << t[1])
            || t[4] != 0
            || t[5] > 40
            || t[5] < t[0])
    {
        inp.refuse("parameter-table-shape");
    }
    p.rest = inp.rest();
    if inp.ok() {
        Ok(())
    } else {
        Err(inp.why().to_string())
    }
}

/// `polWord()` (`verifier/src/cp_verify.cpp:281-305`): the value of one line after the frame's lines,
/// read strictly. A whole parameter file that `read_parameters` rejects and that begins with
/// `"version "` gives `None` (the caller rejects it elsewhere); any other text is scanned whole, as
/// the C++ test tools do.
pub fn pol_word_u64(whole: &[u8], name: &str) -> Option<u64> {
    let mut frame = Parameters::default();
    let framed = read_parameters(whole, &mut frame).is_ok();
    if !framed && whole.starts_with(b"version ") {
        return None;
    }
    let pol: &[u8] = if framed { &frame.rest } else { whole };
    let nb = name.as_bytes();
    let mut a = 0usize;
    while a < pol.len() {
        let e = pol[a..].iter().position(|&c| c == b'\n').map(|x| a + x).unwrap_or(pol.len());
        if e - a > nb.len() + 1 && &pol[a..a + nb.len()] == nb && pol[a + nb.len()] == b' ' {
            let v = &pol[a + nb.len() + 1..e];
            if v.len() > 10 {
                return None;
            }
            let mut x = 0u64;
            for &c in v {
                if !c.is_ascii_digit() {
                    return None;
                }
                x = 10 * x + (c - b'0') as u64;
            }
            return Some(x);
        }
        a = e + 1;
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample() -> Vec<u8> {
        let mut s = String::new();
        s.push_str("version H821\n");
        s.push_str("sec 100\n");
        s.push_str("reading 1\n");
        s.push_str("rowcost 1\n");
        s.push_str("slots 4\n");
        s.push_str("answers 1\n");
        s.push_str("record 1\n");
        for k in ["field", "sample", "closeness", "positions", "smallness"] {
            s.push_str(&format!("work {} 0 0 0\n", k));
        }
        s.push_str("salt 48\n");
        s.push_str("listed 0\n");
        for name in [
            "link", "folded", "omega", "own", "once-folded", "once-omega", "once-own",
            "once-ranges",
        ] {
            s.push_str(&format!("group {} 1 8 4 7 3\n", name));
            s.push_str(&format!("stages {} 4 3 8 7 2 1 6 5 0 0 0 0\n", name));
        }
        s.push_str("ranges-part 6\n");
        s.push_str("table 12 16 100 8 0 16\n");
        s.push_str("rest line\n");
        s.into_bytes()
    }

    #[test]
    fn parses_the_frame_and_keeps_the_rest() {
        let mut p = Parameters::default();
        assert_eq!(read_parameters(&sample(), &mut p), Ok(()));
        assert_eq!(p.version, PROGRAM_VERSION_WORD);
        assert_eq!(p.sec, 100);
        assert_eq!(p.slots, 4);
        assert_eq!(p.link.log_n, 8);
        assert_eq!(p.link.stages.len(), 3);
        assert_eq!(p.link.stages[2], StageChoice { k: 0, h: 0, log_n: 0, mask_log_n: 0 });
        assert_eq!(p.table_rows_log, 12);
        assert_eq!(p.rest, b"rest line\n".to_vec());
    }

    #[test]
    fn rejects_a_leading_blank_or_wrong_version() {
        let mut p = Parameters::default();
        assert_eq!(
            read_parameters(b" version H821\n", &mut p),
            Err("parameter-line-order: version (line 1)".to_string())
        );
        let mut q = sample();
        q[8] = b'7';
        assert_eq!(read_parameters(&q, &mut p), Err("version-unknown (line 1)".to_string()));
    }

    #[test]
    fn pol_word_reads_only_after_the_frame() {
        let mut t = sample();
        t.extend_from_slice(b"C 256\nsT 4\n");
        assert_eq!(pol_word_u64(&t, "C"), Some(256));
        assert_eq!(pol_word_u64(&t, "sT"), Some(4));
        // A line of the frame is not read a second time from the rest.
        assert_eq!(pol_word_u64(&t, "sec"), None);
        let mut bad = t.clone();
        bad[8] = b'7';
        assert_eq!(pol_word_u64(&bad, "C"), None);
    }

    #[test]
    fn rejects_a_number_with_a_leading_zero() {
        let mut q = sample();
        let at = q.windows(5).position(|w| w == b"sec 1").unwrap();
        q[at + 4] = b'0';
        assert!(read_parameters(&q, &mut Parameters::default()).is_err());
    }
}
