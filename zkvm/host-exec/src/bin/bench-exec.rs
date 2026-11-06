//! The benchmark host: executes the `bench` guest with (mode, n) and prints the cycle count.
//!
//! Usage: bench-exec <mode> <n>
//! The guest ELF defaults to the `bench` binary that `cargo prove build -p bench` writes; set
//! BENCH_ELF to override.

use std::fs;
use std::path::PathBuf;

use sp1_sdk::blocking::{Elf, Prover, ProverClient, SP1Stdin};

fn fail(msg: &str) -> ! {
    eprintln!("bench-exec: {msg}");
    std::process::exit(1)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mode: u32 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or_else(|| {
        fail("usage: bench-exec <mode> <n>")
    });
    let n: u64 = args
        .get(2)
        .and_then(|s| s.parse().ok())
        .unwrap_or_else(|| fail("usage: bench-exec <mode> <n>"));
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let zkvm = manifest.parent().expect("zkvm/host-exec has a parent").to_path_buf();
    let elf_path = match std::env::var("BENCH_ELF") {
        Ok(p) => PathBuf::from(p),
        Err(_) => zkvm
            .join("target")
            .join("elf-compilation")
            .join("riscv64im-succinct-zkvm-elf")
            .join("release")
            .join("bench"),
    };
    let elf = fs::read(&elf_path)
        .unwrap_or_else(|e| fail(&format!("cannot read {}: {e}", elf_path.display())));
    let mut stdin = SP1Stdin::new();
    stdin.write(&mode);
    stdin.write(&n);
    let client = ProverClient::builder().cpu().build();
    let started = std::time::Instant::now();
    let (mut public, report) = client
        .execute(Elf::from(elf), stdin)
        .run()
        .unwrap_or_else(|e| fail(&format!("SP1 execute failed: {e}")));
    let elapsed = started.elapsed().as_secs_f64();
    let sink: u64 = public.read();
    let h: [u64; 8] = public.read();
    let _n: u64 = public.read();
    println!(
        "bench: mode={mode} n={n} cycles={} exit={} elapsed={elapsed:.2}s sink={sink:016x} h0={:016x} h7={:016x}",
        report.total_instruction_count(),
        report.exit_code,
        h[0],
        h[7]
    );
}
