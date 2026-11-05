//! S5/S6 host: execute the guest in SP1 (execution only, no proving) and check its public output
//! against `fp-host`, the S3 reference.
//!
//! The guest's private input is what a `cp_verify` call reads from its five paths: the
//! configuration folder's `policy.txt`, `layout.txt` and `KL.bin`, the ivk folder's `key.bin` and
//! the leaf file that the proof names, and the request, y and proof files; then the commitment ID.
//! Each byte string is written with `SP1Stdin::write`, the length-prefixed serialization that the
//! guest reads with `sp1_zkvm::io::read`.
//!
//! Everything comes from the configuration file (`--config`, default
//! `zkvm/config/flashprove.json`): the ELF, the input paths, the fp-host binary. If a vkey record
//! exists, this host also requires the ELF to be the one the record was generated from.
//!
//! The guest commits, in order: the 128-byte `FPV1` public-values block, the report text, and the
//! call status. This host reads all three, rebuilds the expected block from `fp-host`'s stdout and
//! the same input files, and requires the two to be byte-identical.

use std::path::{Path, PathBuf};

use fp_hostlib as hostlib;
use fp_hostlib::{hex, Config};
use sp1_core_executor::{ExecutionReport, SP1CoreOpts};
use sp1_sdk::blocking::{Elf, Prover, ProverClient};

fn fail(msg: &str) -> ! {
    eprintln!("host-exec: {msg}");
    std::process::exit(1)
}

struct Args {
    config: PathBuf,
    root: PathBuf,
    elf: Option<PathBuf>,
    /// S5a-3: `--part <0|1|2|3>` runs one stage only (0 is the whole call).
    part: u32,
}

fn parse_args() -> Args {
    let mut root = None;
    let mut config = None;
    let mut elf = None;
    let mut part = 0u32;
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--root" => root = Some(PathBuf::from(args.next().unwrap_or_else(|| fail("--root needs a value")))),
            "--config" => config = Some(PathBuf::from(args.next().unwrap_or_else(|| fail("--config needs a value")))),
            "--elf" => elf = Some(PathBuf::from(args.next().unwrap_or_else(|| fail("--elf needs a value")))),
            "--part" => {
                part = args
                    .next()
                    .unwrap_or_else(|| fail("--part needs a value"))
                    .parse()
                    .unwrap_or_else(|_| fail("--part takes 0, 1, 2 or 3"));
                if part > 3 {
                    fail("--part takes 0, 1, 2 or 3");
                }
            }
            "-h" | "--help" => {
                println!("usage: host-exec [--root DIR] [--config FILE] [--elf FILE] [--part 0|1|2|3]");
                std::process::exit(0)
            }
            other => fail(&format!("unknown argument {other:?}; see --help")),
        }
    }
    let root = root.unwrap_or_else(|| {
        let cwd = std::env::current_dir().unwrap_or_else(|e| fail(&format!("cannot read the current directory: {e}")));
        hostlib::find_root(&cwd).unwrap_or_else(|e| fail(&format!("{e:#}")))
    });
    let config = config.unwrap_or_else(|| hostlib::default_config_path(&root));
    Args { config, root, elf, part }
}

fn load_elf(root: &Path, config: &Config, override_path: Option<PathBuf>) -> (PathBuf, Vec<u8>) {
    let path = override_path.unwrap_or_else(|| hostlib::elf_path(root, config));
    let bytes = std::fs::read(&path)
        .unwrap_or_else(|e| fail(&format!("cannot read the ELF {}: {e}", path.display())));
    (path, bytes)
}

/// S5a-3: the execute report's opcode counts, most frequent first.
fn print_opcodes(report: &ExecutionReport, total: u64) {
    let mut rows: Vec<(String, u64)> = report
        .opcode_counts
        .iter()
        .map(|(op, c)| (op.to_string(), *c))
        .collect();
    rows.sort_by(|a, b| b.1.cmp(&a.1));
    println!(
        "host-exec: opcode distribution: {} kinds, {} cycles",
        rows.len(),
        total
    );
    let mut shown = 0u64;
    for (name, c) in rows.iter().take(20) {
        shown += *c;
        println!(
            "host-exec:   {:<8} {:>12} {:6.2}%",
            name,
            c,
            100.0 * *c as f64 / total as f64
        );
    }
    if rows.len() > 20 {
        println!(
            "host-exec:   {:<8} {:>12} {:6.2}%",
            "other",
            total - shown,
            100.0 * (total - shown) as f64 / total as f64
        );
    }
}

fn main() {
    let args = parse_args();
    let config = hostlib::load_config(&args.config)
        .unwrap_or_else(|e| fail(&format!("{e:#}")));
    let inputs = hostlib::load_inputs(&args.root, &config)
        .unwrap_or_else(|e| fail(&format!("{e:#}")));
    let (elf_path, elf) = load_elf(&args.root, &config, args.elf);

    let record_path = hostlib::vkey_record_path(&args.root, &config)
        .unwrap_or_else(|e| fail(&format!("{e:#}")));
    if !record_path.is_file() {
        fail(&format!(
            "{} is missing; run `gen-vkey --update` first",
            record_path.display()
        ));
    }
    let record = hostlib::load_vkey_record(&args.root, &config)
        .unwrap_or_else(|e| fail(&format!("{e:#}")));
    record
        .check_elf(&elf_path, &elf)
        .unwrap_or_else(|e| fail(&format!("{e:#}")));
    println!(
        "host-exec: sp1 circuit {}, guest ELF {} ({} bytes, sha256 {})",
        sp1_sdk::SP1_CIRCUIT_VERSION,
        elf_path.display(),
        elf.len(),
        fp_hostlib::sha256_hex(&elf)
    );
    println!("host-exec: vkey {}", record.sp1.vkey_bytes32);

    let expected_digest = inputs.input_digest();
    println!("host-exec: input digest 0x{}", hex(&expected_digest));

    // The guest reads `part` after the commitment ID (S5a-3's stage selector).
    let mut stdin = inputs.stdin();
    stdin.write(&args.part);

    let client = ProverClient::builder().cpu().build();
    let started = std::time::Instant::now();
    let (mut public, report) = client
        .execute(Elf::from(elf), stdin)
        .run()
        .unwrap_or_else(|e| fail(&format!("SP1 execute failed: {e}")));
    let elapsed = started.elapsed().as_secs_f64();

    // The guest's commit order: the raw 128-byte FPV1 block, the report, the status.
    let mut guest_pv = [0u8; fp_pv::PV_LEN];
    public.read_slice(&mut guest_pv);
    let out: String = public.read();
    let status: i32 = public.read();

    let cycles = report.total_instruction_count();
    let shard_size = SP1CoreOpts::default().shard_size as u64;
    let shards = cycles.div_ceil(shard_size);
    println!("host-exec: execute {elapsed:.2} s, guest exit code {}, status {status}", report.exit_code);
    println!("host-exec: total cycles {cycles}");
    println!(
        "host-exec: shards {shards} (estimate ceil(cycles / shard_size), shard_size {shard_size}; \
         the executor also splits at the trace-area thresholds)"
    );
    println!("host-exec: syscalls {}", report.total_syscall_count());
    println!(
        "host-exec: memory {} addresses touched, {} bytes of execution record",
        report.touched_memory_addresses,
        report.total_record_size()
    );
    print_opcodes(&report, cycles);
    println!("host-exec: public output ({} bytes):", out.len());
    print!("{out}");
    if !out.ends_with('\n') {
        println!();
    }
    if args.part != 0 {
        println!(
            "host-exec: partial run (part {}: {}), no consistency comparison",
            args.part,
            match args.part {
                1 => "key",
                2 => "leaf",
                _ => "request",
            }
        );
        return;
    }

    let values = fp_pv::Values::decode(&guest_pv)
        .unwrap_or_else(|| fail("the guest's first public value is not a valid FPV1 block"));
    println!(
        "host-exec: public values FPV1 verdict={} status={} result-v1-status={} id=0x{} input=0x{} result=0x{}",
        fp_pv::verdict::name(values.verdict),
        values.call_status,
        values.result_v1_status,
        hex(&values.commitment_id),
        hex(&values.input_digest),
        hex(&values.result_v1_digest)
    );
    if values.input_digest != expected_digest {
        fail("the guest's input digest does not match the files on disk");
    }

    // The S3 reference: `fp-host` on the same five paths, with the same ID and -q.
    let reference = hostlib::run_fp_host(&args.root, &config, &inputs)
        .unwrap_or_else(|e| fail(&format!("{e:#}")));
    let reference_out = reference.stdout.as_str();
    // fp-host exits with the reference verifier's own status for the verdict; the committed call
    // status comes from the report text. They are independent readings and must agree.
    let status_ok = i32::from(values.call_status) == reference.status;
    println!(
        "host-exec: fp-host exit status {}, committed call status {}{}",
        reference.status,
        values.call_status,
        if status_ok { "" } else { " (DIFFERS)" }
    );
    let want_result = reference_out
        .lines()
        .find(|l| l.starts_with("result-v1 "))
        .unwrap_or_else(|| fail("fp-host printed no result-v1 line"));
    let want_yes = reference_out.lines().last() == Some("YES");
    let got_result = out
        .lines()
        .find(|l| l.starts_with("result-v1 "))
        .unwrap_or_else(|| fail("the guest's public output has no result-v1 line"));
    let got_yes = out.lines().last() == Some("YES");

    let result_ok = got_result == want_result;
    let yes_ok = got_yes == want_yes;
    println!(
        "host-exec: result-v1 {}",
        if result_ok { "IDENTICAL" } else { "DIFFERS" }
    );
    if !result_ok {
        println!("  fp-host: {want_result}");
        println!("  guest:   {got_result}");
    }
    println!(
        "host-exec: YES {}",
        if yes_ok { "IDENTICAL" } else { "DIFFERS" }
    );

    // The public values that fp-host's own stdout implies, from the same input files.
    let expected_pv = hostlib::expected_public_values(&inputs, reference_out);
    let pv_ok = guest_pv == expected_pv;
    println!(
        "host-exec: public values {}",
        if pv_ok {
            "IDENTICAL to fp-host".to_string()
        } else {
            format!(
                "DIFFER (guest 0x{}, fp-host 0x{})",
                hex(&guest_pv),
                hex(&expected_pv)
            )
        }
    );

    if !(result_ok && yes_ok && pv_ok && status_ok) {
        fail("the guest's public output does not match fp-host");
    }
    if status != 0 {
        fail(&format!("the guest ended with status {status}, expected 0"));
    }
    println!(
        "host-exec: PASS (public values, result-v1, YES and the call status match fp-host; vkey {} matches the ELF)",
        record.sp1.vkey_bytes32
    );
}
