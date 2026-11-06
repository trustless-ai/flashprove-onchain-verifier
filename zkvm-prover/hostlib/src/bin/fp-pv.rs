//! B2: inspect and recompute the `FPV1` public-values block outside the zkVM.
//!
//! ```text
//! fp-pv manifest [--root DIR] [--config FILE] [--check FILE]
//! fp-pv expected [--root DIR] [--config FILE] [--fp-host-output FILE] [--json]
//! fp-pv decode (--hex HEX | --file FILE) [--json]
//! fp-pv bundle   [--root DIR] [--config FILE] [--fp-host-output FILE] (--proof-hex HEX | --proof-file FILE)
//! fp-pv check    [--root DIR] [--config FILE] [--fp-host-output FILE] (--pv-hex HEX | --pv-file FILE)
//! ```
//!
//! `manifest` prints the frozen description of the call's input files (names, sizes, SHA-256
//! values, the leaf number and the canonical bundle digest) with root-relative paths. With
//! `--check FILE` it compares the files on disk with a recorded manifest, ignoring paths, so the
//! provider and the client can agree on the exact inputs before proving.
//!
//! `expected` runs `fp-host` on the configured inputs (unless its stdout is supplied) and prints
//! the block those files imply: the commitment ID, the verdict, and the SHA-256 digests of the
//! canonical inputs and the `result-v1` line. `bundle` ABI-encodes `(publicValues, proof)` — the
//! wrapper's `proof` argument — so the anvil interface test can use a placeholder proof byte
//! string without any Solidity-side encoding.

use std::fs;
use std::path::PathBuf;

use anyhow::{anyhow, bail, Context, Result};
use fp_hostlib as hostlib;
use fp_pv::Values;

fn usage() -> ! {
    eprintln!(
        "usage:\n  fp-pv manifest [--root DIR] [--config FILE] [--check FILE]\n  fp-pv expected [--root DIR] [--config FILE] [--fp-host-output FILE] [--json]\n  fp-pv decode (--hex HEX | --file FILE) [--json]\n  fp-pv bundle [--root DIR] [--config FILE] [--fp-host-output FILE] (--proof-hex HEX | --proof-file FILE)\n  fp-pv check [--root DIR] [--config FILE] [--fp-host-output FILE] (--pv-hex HEX | --pv-file FILE)"
    );
    std::process::exit(2)
}

fn parse_hex(text: &str) -> Result<Vec<u8>> {
    let text = text.trim();
    let text = text.strip_prefix("0x").unwrap_or(text);
    if text.len() % 2 != 0 || !text.is_ascii() {
        bail!("not an even number of hex digits");
    }
    let bytes = text.as_bytes();
    let mut out = Vec::with_capacity(text.len() / 2);
    for i in 0..text.len() / 2 {
        let hi = (bytes[2 * i] as char).to_digit(16).context("not hex")?;
        let lo = (bytes[2 * i + 1] as char).to_digit(16).context("not hex")?;
        out.push(((hi << 4) | lo) as u8);
    }
    Ok(out)
}

fn print_json(value: &serde_json::Value) -> Result<()> {
    println!("{}", serde_json::to_string_pretty(value)?);
    Ok(())
}

fn values_json(values: &Values) -> serde_json::Value {
    serde_json::json!({
        "pv_hex": format!("0x{}", hostlib::hex(&values.encode())),
        "schema": "FPV1",
        "verdict": fp_pv::verdict::name(values.verdict),
        "verdict_code": values.verdict,
        "call_status": values.call_status,
        "result_v1_status": values.result_v1_status,
        "commitment_id": format!("0x{}", hostlib::hex(&values.commitment_id)),
        "input_hash": format!("0x{}", hostlib::hex(&values.input_digest)),
        "output_hash": format!("0x{}", hostlib::hex(&values.result_v1_digest)),
    })
}

struct Common {
    root: PathBuf,
    config: PathBuf,
    fp_host_output: Option<PathBuf>,
}

fn expected_values(common: &Common) -> Result<(hostlib::Inputs, Values, [u8; fp_pv::PV_LEN])> {
    let config = hostlib::load_config(&common.config)?;
    let inputs = hostlib::load_inputs(&common.root, &config)?;
    let stdout = match &common.fp_host_output {
        Some(path) => fs::read_to_string(path)
            .with_context(|| format!("cannot read {}", path.display()))?,
        None => {
            let output = hostlib::run_fp_host(&common.root, &config, &inputs)?;
            if output.status != 0 {
                bail!(
                    "fp-host exited {}: {}",
                    output.status,
                    output.stderr.trim()
                );
            }
            output.stdout
        }
    };
    let encoded = hostlib::expected_public_values(&inputs, &stdout);
    let values = Values::decode(&encoded).expect("the encoder produces a valid block");
    Ok((inputs, values, encoded))
}

fn main() {
    if let Err(error) = run() {
        eprintln!("fp-pv: {error:#}");
        std::process::exit(1);
    }
}

fn run() -> Result<()> {
    let mut args = std::env::args().skip(1);
    let Some(command) = args.next() else { usage() };
    match command.as_str() {
        "manifest" => {
            let mut root = None;
            let mut config = None;
            let mut check = None;
            while let Some(arg) = args.next() {
                match arg.as_str() {
                    "--root" => root = Some(PathBuf::from(args.next().context("--root needs a value")?)),
                    "--config" => config = Some(PathBuf::from(args.next().context("--config needs a value")?)),
                    "--check" => check = Some(PathBuf::from(args.next().context("--check needs a value")?)),
                    other => bail!("unknown argument {other:?}"),
                }
            }
            let root = root.unwrap_or(hostlib::find_root(&std::env::current_dir()?)?);
            let config = config.unwrap_or_else(|| hostlib::default_config_path(&root));
            let config = hostlib::load_config(&config)?;
            let inputs = hostlib::load_inputs(&root, &config)?;
            let manifest = inputs.manifest(&root);
            match check {
                None => print_json(&serde_json::to_value(manifest)?),
                Some(path) => {
                    let text = fs::read_to_string(&path)
                        .with_context(|| format!("cannot read {}", path.display()))?;
                    let stored: hostlib::InputManifest = serde_json::from_str(&text)
                        .with_context(|| format!("cannot parse {}", path.display()))?;
                    manifest.compare(&stored)?;
                    println!(
                        "fp-pv: MATCH ({} files, leaf {}, input digest 0x{})",
                        manifest.files.len(),
                        manifest.entry_number,
                        manifest.input_digest
                    );
                    Ok(())
                }
            }
        }
        "expected" => {
            let mut json = false;
            let mut root = None;
            let mut config = None;
            let mut fp_host_output = None;
            while let Some(arg) = args.next() {
                match arg.as_str() {
                    "--root" => root = Some(PathBuf::from(args.next().context("--root needs a value")?)),
                    "--config" => config = Some(PathBuf::from(args.next().context("--config needs a value")?)),
                    "--fp-host-output" => fp_host_output =
                        Some(PathBuf::from(args.next().context("--fp-host-output needs a value")?)),
                    "--json" => json = true,
                    other => bail!("unknown argument {other:?}"),
                }
            }
            let root = root.unwrap_or(hostlib::find_root(&std::env::current_dir()?)?);
            let config = config.unwrap_or_else(|| hostlib::default_config_path(&root));
            let common = Common { root, config, fp_host_output };
            let (inputs, values, _) = expected_values(&common)?;
            if json {
                print_json(&values_json(&values))?;
            } else {
                println!("input_digest=0x{}", hostlib::hex(&inputs.input_digest()));
                println!("pv=0x{}", hostlib::hex(&values.encode()));
                println!("verdict={}", fp_pv::verdict::name(values.verdict));
                println!("call_status={}", values.call_status);
                println!("result_v1_status={}", values.result_v1_status);
                println!("commitment_id=0x{}", hostlib::hex(&values.commitment_id));
                println!("input_hash=0x{}", hostlib::hex(&values.input_digest));
                println!("output_hash=0x{}", hostlib::hex(&values.result_v1_digest));
            }
            Ok(())
        }
        "decode" => {
            let mut hex = None;
            let mut file = None;
            let mut json = false;
            while let Some(arg) = args.next() {
                match arg.as_str() {
                    "--hex" => hex = Some(args.next().context("--hex needs a value")?),
                    "--file" => file = Some(PathBuf::from(args.next().context("--file needs a value")?)),
                    "--json" => json = true,
                    other => bail!("unknown argument {other:?}"),
                }
            }
            let bytes = match (hex, file) {
                (Some(hex), None) => parse_hex(&hex)?,
                (None, Some(path)) => fs::read(&path)
                    .with_context(|| format!("cannot read {}", path.display()))?,
                _ => bail!("give exactly one of --hex and --file"),
            };
            let values = Values::decode(&bytes)
                .ok_or_else(|| anyhow!("the bytes are not a valid FPV1 block"))?;
            if json {
                print_json(&values_json(&values))
            } else {
                println!("verdict={}", fp_pv::verdict::name(values.verdict));
                println!("call_status={}", values.call_status);
                println!("result_v1_status={}", values.result_v1_status);
                println!("commitment_id=0x{}", hostlib::hex(&values.commitment_id));
                println!("input_hash=0x{}", hostlib::hex(&values.input_digest));
                println!("output_hash=0x{}", hostlib::hex(&values.result_v1_digest));
                Ok(())
            }
        }
        "bundle" => {
            let mut root = None;
            let mut config = None;
            let mut fp_host_output = None;
            let mut proof_hex = None;
            let mut proof_file = None;
            while let Some(arg) = args.next() {
                match arg.as_str() {
                    "--root" => root = Some(PathBuf::from(args.next().context("--root needs a value")?)),
                    "--config" => config = Some(PathBuf::from(args.next().context("--config needs a value")?)),
                    "--fp-host-output" => fp_host_output =
                        Some(PathBuf::from(args.next().context("--fp-host-output needs a value")?)),
                    "--proof-hex" => proof_hex = Some(args.next().context("--proof-hex needs a value")?),
                    "--proof-file" => proof_file = Some(PathBuf::from(args.next().context("--proof-file needs a value")?)),
                    other => bail!("unknown argument {other:?}"),
                }
            }
            let root = root.unwrap_or(hostlib::find_root(&std::env::current_dir()?)?);
            let config = config.unwrap_or_else(|| hostlib::default_config_path(&root));
            let common = Common { root, config, fp_host_output };
            let (_, _, encoded) = expected_values(&common)?;
            let proof = match (proof_hex, proof_file) {
                (Some(hex), None) => parse_hex(&hex)?,
                (None, Some(path)) => fs::read(&path)
                    .with_context(|| format!("cannot read {}", path.display()))?,
                _ => bail!("give exactly one of --proof-hex and --proof-file"),
            };
            let bundle = hostlib::abi_encode_bundle(&encoded, &proof);
            println!("0x{}", hostlib::hex(&bundle));
            Ok(())
        }
        "check" => {
            let mut root = None;
            let mut config = None;
            let mut fp_host_output = None;
            let mut pv_hex = None;
            let mut pv_file = None;
            while let Some(arg) = args.next() {
                match arg.as_str() {
                    "--root" => root = Some(PathBuf::from(args.next().context("--root needs a value")?)),
                    "--config" => config = Some(PathBuf::from(args.next().context("--config needs a value")?)),
                    "--fp-host-output" => fp_host_output =
                        Some(PathBuf::from(args.next().context("--fp-host-output needs a value")?)),
                    "--pv-hex" => pv_hex = Some(args.next().context("--pv-hex needs a value")?),
                    "--pv-file" => pv_file = Some(PathBuf::from(args.next().context("--pv-file needs a value")?)),
                    other => bail!("unknown argument {other:?}"),
                }
            }
            let root = root.unwrap_or(hostlib::find_root(&std::env::current_dir()?)?);
            let config = config.unwrap_or_else(|| hostlib::default_config_path(&root));
            let common = Common { root, config, fp_host_output };
            let (_, values, expected) = expected_values(&common)?;
            let got = match (pv_hex, pv_file) {
                (Some(hex), None) => parse_hex(&hex)?,
                (None, Some(path)) => fs::read(&path)
                    .with_context(|| format!("cannot read {}", path.display()))?,
                _ => bail!("give exactly one of --pv-hex and --pv-file"),
            };
            if got.len() < fp_pv::PV_LEN {
                bail!("the supplied block is {} bytes, shorter than {}", got.len(), fp_pv::PV_LEN);
            }
            let got_values = Values::decode(&got)
                .ok_or_else(|| anyhow!("the supplied bytes are not a valid FPV1 block"))?;
            if got[..fp_pv::PV_LEN] == expected {
                println!(
                    "fp-pv: MATCH (verdict {}, id 0x{})",
                    fp_pv::verdict::name(values.verdict),
                    hostlib::hex(&values.commitment_id)
                );
                Ok(())
            } else {
                println!("fp-pv: MISMATCH");
                println!("  expected 0x{}", hostlib::hex(&expected));
                println!("  supplied 0x{}", hostlib::hex(&got[..fp_pv::PV_LEN]));
                println!("  supplied verdict {}", fp_pv::verdict::name(got_values.verdict));
                std::process::exit(1);
            }
        }
        "-h" | "--help" => usage(),
        other => {
            eprintln!("fp-pv: unknown command {other:?}");
            usage()
        }
    }
}
