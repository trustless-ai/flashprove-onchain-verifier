//! B4: the prover driver. CPU, CUDA and mock backends behind one configuration.
//!
//! ```text
//! fp-prover prove [--root DIR] [--config FILE] [--plan] [--mock]
//!                 [--mode cpu|cuda|mock] [--proof-mode groth16|plonk|compressed|core]
//!                 [--out DIR]
//! ```
//!
//! * The ELF, the input paths and the default mode come from the configuration file.
//! * `mode` defaults to `cuda` (the handoff default); `cpu` and `mock` are available locally.
//!   A build without the `cuda` feature refuses `mode = "cuda"` with instructions; build the GPU
//!   machine's binary with `--features cuda`.
//! * `--plan` validates the configuration, the ELF hash and the vkey record, prints what would be
//!   proved, and stops before `setup` or proving.
//! * `--mock` runs the whole pipeline (setup, execute, a mock proof, local verify, all output
//!   files) without a real proof. It still executes the guest, so a smoke configuration should
//!   point at small inputs.
//!
//! Outputs, in `prover.output_dir` (default `out/zkvm/proof`):
//!   proof.bin             the SP1 proof, bincode-serialized (`SP1ProofWithPublicValues::save`)
//!   proof.bytes           the on-chain proof bytes (Plonk and Groth16 only)
//!   public_values.bin     the raw public values (FPV1 block || report || status)
//!   public_values.hex     the same, 0x-prefixed
//!   pv.bin                the first 128 bytes (the FPV1 block)
//!   bundle.bin            abi.encode(publicValues, proofBytes), the wrapper's `proof` argument
//!                         (Plonk and Groth16 only)
//!   bundle.hex            the same, 0x-prefixed
//!   summary.json          ELF hash, vkey, input digest, verdict, sizes, elapsed

use std::fs;
use std::path::PathBuf;
use std::time::Instant;

use anyhow::{anyhow, bail, Context, Result};
use fp_hostlib as hostlib;
use sp1_sdk::blocking::{Elf, ProveRequest, Prover, ProverClient, SP1Stdin};
use sp1_sdk::{HashableKey, ProvingKey, SP1ProofWithPublicValues};

#[derive(Clone, Copy, Debug)]
enum ProofMode {
    Core,
    Compressed,
    Plonk,
    Groth16,
}

impl ProofMode {
    fn parse(text: &str) -> Result<Self> {
        match text {
            "core" => Ok(Self::Core),
            "compressed" => Ok(Self::Compressed),
            "plonk" => Ok(Self::Plonk),
            "groth16" => Ok(Self::Groth16),
            other => bail!(
                "unknown proof mode {other:?}; expected groth16, plonk, compressed or core"
            ),
        }
    }

    fn name(self) -> &'static str {
        match self {
            Self::Core => "core",
            Self::Compressed => "compressed",
            Self::Plonk => "plonk",
            Self::Groth16 => "groth16",
        }
    }

    fn on_chain(self) -> bool {
        matches!(self, Self::Plonk | Self::Groth16)
    }
}

struct Args {
    root: PathBuf,
    config: PathBuf,
    plan: bool,
    mock: bool,
    mode: Option<String>,
    proof_mode: Option<String>,
    out: Option<PathBuf>,
}

fn parse_args() -> Result<Args> {
    let mut root = None;
    let mut config = None;
    let mut plan = false;
    let mut mock = false;
    let mut mode = None;
    let mut proof_mode = None;
    let mut out = None;
    let mut args = std::env::args().skip(1);
    let Some(command) = args.next() else {
        bail!("usage: fp-prover prove [--root DIR] [--config FILE] [--plan] [--mock] [--mode cpu|cuda|mock] [--proof-mode groth16|plonk|compressed|core] [--out DIR]")
    };
    if command != "prove" {
        bail!("unknown command {command:?}; the only command is `prove`");
    }
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--root" => root = Some(PathBuf::from(args.next().context("--root needs a value")?)),
            "--config" => config = Some(PathBuf::from(args.next().context("--config needs a value")?)),
            "--plan" | "--dry-run" => plan = true,
            "--mock" => mock = true,
            "--mode" => mode = Some(args.next().context("--mode needs a value")?),
            "--proof-mode" => proof_mode = Some(args.next().context("--proof-mode needs a value")?),
            "--out" => out = Some(PathBuf::from(args.next().context("--out needs a value")?)),
            "-h" | "--help" => {
                println!("usage: fp-prover prove [--root DIR] [--config FILE] [--plan] [--mock] [--mode cpu|cuda|mock] [--proof-mode groth16|plonk|compressed|core] [--out DIR]");
                std::process::exit(0);
            }
            other => bail!("unknown argument {other:?}"),
        }
    }
    let root = match root {
        Some(root) => root,
        None => hostlib::find_root(&std::env::current_dir()?)?,
    };
    let config = config.unwrap_or_else(|| hostlib::default_config_path(&root));
    Ok(Args { root, config, plan, mock, mode, proof_mode, out })
}

struct Job {
    output_dir: PathBuf,
    elf_path: PathBuf,
    elf: Vec<u8>,
    stdin: SP1Stdin,
    input_digest: [u8; 32],
    record: hostlib::VkeyRecord,
    proof_mode: ProofMode,
    mock: bool,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("fp-prover: {error:#}");
        std::process::exit(1);
    }
}

fn run() -> Result<()> {
    let args = parse_args()?;
    let config = hostlib::load_config(&args.config)?;
    let inputs = hostlib::load_inputs(&args.root, &config)?;
    let elf_path = hostlib::elf_path(&args.root, &config);
    let elf = fs::read(&elf_path)
        .with_context(|| format!("cannot read the ELF {}", elf_path.display()))?;
    let record = hostlib::load_vkey_record(&args.root, &config)?;
    record.check_elf(&elf_path, &elf)?;

    let mode = if args.mock {
        "mock".to_string()
    } else {
        args.mode.unwrap_or_else(|| config.prover.mode.clone())
    };
    if !matches!(mode.as_str(), "cpu" | "cuda" | "mock") {
        bail!("unknown prover mode {mode:?}; expected cpu, cuda or mock");
    }
    let proof_mode = ProofMode::parse(
        &args
            .proof_mode
            .unwrap_or_else(|| config.prover.proof_mode.clone()),
    )?;
    let output_dir = args
        .out
        .unwrap_or_else(|| hostlib::resolve(&args.root, &config.prover.output_dir));

    let input_digest = inputs.input_digest();
    println!(
        "fp-prover: ELF {} ({} bytes, sha256 {})",
        elf_path.display(),
        elf.len(),
        record.program.elf_sha256
    );
    println!("fp-prover: vkey {}", record.sp1.vkey_bytes32);
    println!(
        "fp-prover: sp1 circuit {}, sdk {}",
        record.sp1.circuit_version, record.sp1.sdk_version
    );
    println!("fp-prover: input digest 0x{}", hostlib::hex(&input_digest));
    println!(
        "fp-prover: mode {mode}, proof mode {}, output {}",
        proof_mode.name(),
        output_dir.display()
    );
    if mode == "mock" {
        println!(
            "fp-prover: MOCK backend: the output is not a real proof and is not verifiable on chain"
        );
    } else if proof_mode.on_chain() {
        println!(
            "fp-prover: {} is verifiable by the SP1 verifier contract",
            proof_mode.name()
        );
    } else {
        println!(
            "fp-prover: {} is NOT an on-chain proof mode; the ERC-8274 wrapper needs groth16 or plonk",
            proof_mode.name()
        );
    }

    if args.plan {
        let plan = serde_json::json!({
            "elf": elf_path.display().to_string(),
            "elf_sha256": record.program.elf_sha256,
            "elf_size": elf.len(),
            "vkey": record.sp1.vkey_bytes32,
            "circuit_version": record.sp1.circuit_version,
            "sdk_version": record.sp1.sdk_version,
            "mode": mode,
            "proof_mode": proof_mode.name(),
            "on_chain": proof_mode.on_chain(),
            "input_digest": format!("0x{}", hostlib::hex(&input_digest)),
            "output_dir": output_dir.display().to_string(),
            "proof_bundle": if proof_mode.on_chain() { "wrapper-ready" } else { "off-chain-only" },
        });
        println!("{}", serde_json::to_string_pretty(&plan)?);
        println!("fp-prover: PLAN ONLY (no setup, no proving)");
        return Ok(());
    }

    let job = Job {
        output_dir,
        elf_path,
        elf,
        stdin: inputs.stdin(),
        input_digest,
        record,
        proof_mode,
        mock: mode == "mock",
    };
    match mode.as_str() {
        "cpu" => run_with(ProverClient::builder().cpu().build(), job),
        "mock" => run_with(ProverClient::builder().mock().build(), job),
        "cuda" => {
            #[cfg(feature = "cuda")]
            {
                run_with(ProverClient::builder().cuda().build(), job)
            }
            #[cfg(not(feature = "cuda"))]
            {
                let _ = job;
                bail!(
                    "this binary was built without the `cuda` feature; on the GPU machine build \
                     `cargo build --release -p fp-hostlib --bin fp-prover --features cuda`, or \
                     choose --mode cpu / --mode mock locally"
                )
            }
        }
        _ => unreachable!(),
    }
}

fn run_with<P: Prover>(prover: P, job: Job) -> Result<()> {
    let Job { output_dir, elf_path, elf, stdin, input_digest, record, proof_mode, mock } = job;

    println!("fp-prover: setup ...");
    let started = Instant::now();
    let pk = prover
        .setup(Elf::from(elf))
        .map_err(|e| anyhow!("SP1 setup failed: {e}"))?;
    let vkey = pk.verifying_key();
    let got = vkey.bytes32();
    if got != record.sp1.vkey_bytes32 {
        bail!(
            "setup produced vkey {}, but the vkey record holds {}; regenerate the record with \
             `gen-vkey --update`",
            got,
            record.sp1.vkey_bytes32
        );
    }
    println!("fp-prover: setup {:.1} s, vkey checked", started.elapsed().as_secs_f64());

    println!("fp-prover: proving ({}) ...", proof_mode.name());
    let prove_started = Instant::now();
    let request = prover.prove(&pk, stdin);
    let proof: SP1ProofWithPublicValues = match proof_mode {
        ProofMode::Core => request.core().run(),
        ProofMode::Compressed => request.compressed().run(),
        ProofMode::Plonk => request.plonk().run(),
        ProofMode::Groth16 => request.groth16().run(),
    }
    .map_err(|e| anyhow!("proving failed: {e}"))?;
    let prove_secs = prove_started.elapsed().as_secs_f64();
    // `SP1ProofWithPublicValues::bytes` panics for core and compressed proofs: only Plonk and
    // Groth16 have the on-chain byte encoding the SP1 verifier contract accepts.
    let size = if proof_mode.on_chain() {
        format!("{} bytes", proof.bytes().len())
    } else {
        "no on-chain byte encoding".to_string()
    };
    println!(
        "fp-prover: proof in {prove_secs:.1} s, {size}, sp1 {}",
        proof.sp1_version
    );

    prover
        .verify(&proof, vkey, None)
        .map_err(|e| anyhow!("the proof did not verify locally: {e}"))?;
    println!("fp-prover: verified locally");

    save(
        &SaveJob { output_dir, elf_path, input_digest, record, proof_mode, mock },
        &proof,
        prove_secs,
    )
}

struct SaveJob {
    output_dir: PathBuf,
    elf_path: PathBuf,
    input_digest: [u8; 32],
    record: hostlib::VkeyRecord,
    proof_mode: ProofMode,
    mock: bool,
}

fn save(job: &SaveJob, proof: &SP1ProofWithPublicValues, prove_secs: f64) -> Result<()> {
    let out = &job.output_dir;
    fs::create_dir_all(out).with_context(|| format!("cannot create {}", out.display()))?;

    proof
        .save(out.join("proof.bin"))
        .with_context(|| format!("cannot save {}", out.join("proof.bin").display()))?;

    let public_values = proof.public_values.as_slice();
    // The guest commits the raw block first, with no length prefix.
    if public_values.len() < fp_pv::PV_LEN {
        bail!(
            "the public values are {} bytes, shorter than the {} byte FPV1 block",
            public_values.len(),
            fp_pv::PV_LEN
        );
    }
    let pv = &public_values[..fp_pv::PV_LEN];
    let values = fp_pv::Values::decode(pv)
        .ok_or_else(|| anyhow!("the first public value is not a valid FPV1 block"))?;
    if values.input_digest != job.input_digest {
        bail!(
            "the guest committed input digest 0x{}, but the host computed 0x{}",
            hostlib::hex(&values.input_digest),
            hostlib::hex(&job.input_digest)
        );
    }

    // Only Plonk and Groth16 have the on-chain byte encoding; `bytes()` panics for core and
    // compressed proofs, which stay off-chain.
    let proof_bytes = job.proof_mode.on_chain().then(|| proof.bytes());
    let bundle = proof_bytes
        .as_ref()
        .map(|bytes| hostlib::abi_encode_bundle(public_values, bytes));

    fs::write(out.join("public_values.bin"), public_values)?;
    fs::write(
        out.join("public_values.hex"),
        format!("0x{}\n", hostlib::hex(public_values)),
    )?;
    fs::write(out.join("pv.bin"), pv)?;
    if let Some(bytes) = &proof_bytes {
        fs::write(out.join("proof.bytes"), bytes)?;
    }
    if let Some(bundle) = &bundle {
        fs::write(out.join("bundle.bin"), bundle)?;
        fs::write(out.join("bundle.hex"), format!("0x{}\n", hostlib::hex(bundle)))?;
    }

    let summary = serde_json::json!({
        "schema": "fp-sp1-proof/v1",
        "program": job.record.program.name,
        "elf": job.elf_path.display().to_string(),
        "elf_sha256": job.record.program.elf_sha256,
        "elf_size": job.record.program.elf_size,
        "vkey": job.record.sp1.vkey_bytes32,
        "circuit_version": job.record.sp1.circuit_version,
        "sdk_version": job.record.sp1.sdk_version,
        "sp1_version": proof.sp1_version,
        "proof_mode": job.proof_mode.name(),
        "backend": if job.mock { "mock" } else { "sp1" },
        "on_chain": job.proof_mode.on_chain() && !job.mock,
        "proof_bytes": proof_bytes.as_ref().map(Vec::len),
        "public_values_bytes": public_values.len(),
        "bundle_bytes": bundle.as_ref().map(Vec::len),
        "input_digest": format!("0x{}", hostlib::hex(&values.input_digest)),
        "commitment_id": format!("0x{}", hostlib::hex(&values.commitment_id)),
        "verdict": fp_pv::verdict::name(values.verdict),
        "call_status": values.call_status,
        "output_hash": format!("0x{}", hostlib::hex(&values.result_v1_digest)),
        "proof_seconds": prove_secs,
    });
    fs::write(
        out.join("summary.json"),
        serde_json::to_string_pretty(&summary)? + "\n",
    )?;

    println!(
        "fp-prover: public values 0x{} (verdict {}, id 0x{}, {} bytes)",
        hostlib::hex(pv),
        fp_pv::verdict::name(values.verdict),
        hostlib::hex(&values.commitment_id),
        public_values.len()
    );
    match (&proof_bytes, &bundle) {
        (Some(bytes), Some(bundle)) => println!(
            "fp-prover: on-chain proof {} bytes, bundle {} bytes",
            bytes.len(),
            bundle.len()
        ),
        _ => println!(
            "fp-prover: no on-chain artifacts for this proof mode (proof.bin and the public values only)"
        ),
    }
    println!("fp-prover: wrote {}", out.display());
    Ok(())
}
