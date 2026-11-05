//! B1: generate the SP1 vkey for the configured guest ELF and record it with the ELF's hash.
//!
//! Nothing about the program is hard-coded: the ELF path, the record path and the program name
//! come from the configuration file. A program update therefore changes the configuration and,
//! with `--update`, the record — not this tool or any other source file.
//!
//! ```text
//! gen-vkey [--root DIR] [--config FILE] [--update | --check | --check-elf]
//! ```
//!
//! * default: print the record as JSON (and a summary on stderr; this runs SP1 `setup`).
//! * `--update`: write it to `program.vkey_record`.
//! * `--check`: rebuild the record with SP1 `setup` and compare; exit 1 on any difference.
//! * `--check-elf`: compare only the ELF's SHA-256 and size with the record, without `setup`.
//!   The vkey is a function of the ELF, so this is the routine check; `--check` re-derives it.

use std::fs;
use std::path::{Path, PathBuf};

use anyhow::{anyhow, Context, Result};
use fp_hostlib as hostlib;
use sp1_sdk::blocking::{Elf, Prover, ProverClient};
use sp1_sdk::ProvingKey;

struct Args {
    root: PathBuf,
    config: PathBuf,
    update: bool,
    check: bool,
    check_elf: bool,
}

fn parse_args() -> Result<Args> {
    let mut root = None;
    let mut config = None;
    let mut update = false;
    let mut check = false;
    let mut check_elf = false;
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--root" => root = Some(PathBuf::from(args.next().context("--root needs a value")?)),
            "--config" => config = Some(PathBuf::from(args.next().context("--config needs a value")?)),
            "--update" => update = true,
            "--check" => check = true,
            "--check-elf" => check_elf = true,
            "-h" | "--help" => {
                println!(
                    "usage: gen-vkey [--root DIR] [--config FILE] [--update | --check | --check-elf]"
                );
                std::process::exit(0);
            }
            other => return Err(anyhow!("unknown argument {other:?}; see --help")),
        }
    }
    if [update, check, check_elf].iter().filter(|&&on| on).count() > 1 {
        return Err(anyhow!(
            "--update, --check and --check-elf are mutually exclusive"
        ));
    }
    let root = match root {
        Some(root) => root,
        None => hostlib::find_root(&std::env::current_dir()?)?,
    };
    let config = config.unwrap_or_else(|| hostlib::default_config_path(&root));
    Ok(Args { root, config, update, check, check_elf })
}

fn build(root: &Path, config: &hostlib::Config) -> Result<hostlib::VkeyRecord> {
    let elf_path = hostlib::elf_path(root, config);
    let elf = fs::read(&elf_path)
        .with_context(|| format!("cannot read the ELF {}", elf_path.display()))?;
    eprintln!(
        "gen-vkey: ELF {} ({} bytes, sha256 {})",
        elf_path.display(),
        elf.len(),
        hostlib::sha256_hex(&elf)
    );
    let client = ProverClient::builder().cpu().build();
    let pk = client
        .setup(Elf::from(elf.clone()))
        .map_err(|e| anyhow!("SP1 setup failed: {e}"))?;
    Ok(hostlib::VkeyRecord::from_elf(
        root,
        config.program.name.clone(),
        &elf_path,
        &elf,
        pk.verifying_key(),
    ))
}

fn main() {
    if let Err(error) = run() {
        eprintln!("gen-vkey: {error:#}");
        std::process::exit(1);
    }
}

fn run() -> Result<()> {
    let args = parse_args()?;
    let config = hostlib::load_config(&args.config)?;

    if args.check_elf {
        let elf_path = hostlib::elf_path(&args.root, &config);
        let elf = fs::read(&elf_path)
            .with_context(|| format!("cannot read the ELF {}", elf_path.display()))?;
        let existing = hostlib::load_vkey_record(&args.root, &config)?;
        existing.check_elf(&elf_path, &elf)?;
        println!(
            "gen-vkey: MATCH (ELF sha256 {}, size {}, vkey {})",
            existing.program.elf_sha256, existing.program.elf_size, existing.sp1.vkey_bytes32
        );
        return Ok(());
    }

    let record = build(&args.root, &config)?;
    eprintln!(
        "gen-vkey: sp1 circuit {}, sdk {}, vkey {}",
        record.sp1.circuit_version, record.sp1.sdk_version, record.sp1.vkey_bytes32
    );

    let path = hostlib::vkey_record_path(&args.root, &config)?;
    if args.check {
        let existing = hostlib::load_vkey_record(&args.root, &config)?;
        if existing == record {
            println!("gen-vkey: MATCH ({} equals the current ELF)", path.display());
            return Ok(());
        }
        eprintln!("gen-vkey: the record DIFFERS from the current ELF");
        eprintln!("  recorded: {}", serde_json::to_string_pretty(&existing)?);
        eprintln!("  rebuilt:  {}", serde_json::to_string_pretty(&record)?);
        std::process::exit(1);
    }

    if args.update {
        record.write(&path)?;
        println!(
            "gen-vkey: wrote {} (vkey {}, ELF sha256 {})",
            path.display(),
            record.sp1.vkey_bytes32,
            record.program.elf_sha256
        );
    } else {
        println!("{}", serde_json::to_string_pretty(&record)?);
    }
    Ok(())
}
