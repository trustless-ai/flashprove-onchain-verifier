//! Host-side support for the SP1 toolchain around the FlashProve verifier.
//!
//! Everything is configuration-driven: the ELF, the vkey record, the input paths, the prover mode,
//! the output directory and the chain parameters come from a JSON file (`fp-sp1-config/v1`).
//! Paths in the file are relative to the repository root; the root is found by walking up from the
//! current directory until a directory holds both `AGENTS.md` and `zkvm/`, or passed on the
//! command line.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{bail, Context, Result};
use serde::{Deserialize, Serialize};

pub const CONFIG_SCHEMA: &str = "fp-sp1-config/v1";
pub const VKEY_SCHEMA: &str = "fp-vkey/v1";
/// Kept in sync with `zkvm/Cargo.lock` by `tests::sdk_version_matches_lockfile`.
pub const SP1_SDK_VERSION: &str = "6.10.0";

// ---------------------------------------------------------------------------------------------
// Configuration

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Config {
    pub schema: String,
    pub program: ProgramConfig,
    pub inputs: InputsConfig,
    /// `fp-host` binary used as the reference; defaults to the debug build in the repository.
    #[serde(default)]
    pub fp_host: Option<String>,
    #[serde(default)]
    pub prover: ProverConfig,
    #[serde(default)]
    pub chain: Option<ChainConfig>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProgramConfig {
    #[serde(default)]
    pub name: Option<String>,
    /// Guest ELF to prove. A path relative to the repository root.
    pub elf: String,
    /// Where `gen-vkey` writes (and everyone else reads) the ELF hash and vkey.
    #[serde(default)]
    pub vkey_record: Option<String>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct InputsConfig {
    /// The configuration folder: `policy.txt`, `layout.txt`, `KL.bin`.
    pub config_dir: String,
    /// The ivk folder: `key.bin` and `leaf/<n>.bin`.
    pub ivk_dir: String,
    pub request: String,
    pub y: String,
    pub proof: String,
    pub id_file: String,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProverConfig {
    /// `cuda` (the default for the handoff) or `cpu`.
    #[serde(default = "default_prover_mode")]
    pub mode: String,
    /// `groth16` (on-chain), `plonk`, `compressed` or `core`.
    #[serde(default = "default_proof_mode")]
    pub proof_mode: String,
    #[serde(default = "default_output_dir")]
    pub output_dir: String,
}

impl Default for ProverConfig {
    fn default() -> Self {
        Self {
            mode: default_prover_mode(),
            proof_mode: default_proof_mode(),
            output_dir: default_output_dir(),
        }
    }
}

fn default_prover_mode() -> String {
    "cuda".to_string()
}
fn default_proof_mode() -> String {
    "groth16".to_string()
}
fn default_output_dir() -> String {
    "out/zkvm/proof".to_string()
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ChainConfig {
    #[serde(default = "default_rpc_url")]
    pub rpc_url: String,
    /// The deployed SP1 verifier (or the mock's address after the anvil script deploys it).
    #[serde(default)]
    pub sp1_verifier: Option<String>,
    /// The SP1 program vkey bound in the verifier's metadata; when absent, the vkey record's.
    #[serde(default)]
    pub program_vkey: Option<String>,
    pub commitment_id: String,
    /// Verdict names, e.g. `["YES"]` or `["YES", "WITHIN_LIMITS"]`.
    #[serde(default = "default_accepted_verdicts")]
    pub accepted_verdicts: Vec<String>,
    #[serde(default = "default_true")]
    pub require_status_zero: bool,
    /// Authorized agents as 32-byte hex values (an EVM address left-padded to bytes32).
    #[serde(default)]
    pub authorized_agents: Vec<String>,
}

fn default_rpc_url() -> String {
    "http://127.0.0.1:8545".to_string()
}
fn default_accepted_verdicts() -> Vec<String> {
    vec!["YES".to_string()]
}
fn default_true() -> bool {
    true
}

// ---------------------------------------------------------------------------------------------
// Paths and loading

/// Walks up from `start` for the repository root (a directory holding `AGENTS.md` and `zkvm/`).
pub fn find_root(start: &Path) -> Result<PathBuf> {
    for dir in start.ancestors() {
        if dir.join("zkvm-prover").is_dir() && dir.join("rust-verifier").is_dir() {
            return Ok(dir.to_path_buf());
        }
    }
    bail!(
        "cannot find the repository root from {}: no ancestor holds both zkvm-prover/ and rust-verifier/",
        start.display()
    )
}

pub fn resolve(root: &Path, path: &str) -> PathBuf {
    let path = Path::new(path);
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        root.join(path)
    }
}

pub fn default_config_path(root: &Path) -> PathBuf {
    root.join("config").join("flashprove.json")
}

pub fn load_config(path: &Path) -> Result<Config> {
    let text = fs::read_to_string(path)
        .with_context(|| format!("cannot read the configuration {}", path.display()))?;
    let config: Config = serde_json::from_str(&text)
        .with_context(|| format!("cannot parse the configuration {}", path.display()))?;
    if config.schema != CONFIG_SCHEMA {
        bail!(
            "configuration schema is {:?}, expected {:?}",
            config.schema,
            CONFIG_SCHEMA
        );
    }
    Ok(config)
}

pub fn elf_path(root: &Path, config: &Config) -> PathBuf {
    resolve(root, &config.program.elf)
}

pub fn vkey_record_path(root: &Path, config: &Config) -> Result<PathBuf> {
    match &config.program.vkey_record {
        Some(path) => Ok(resolve(root, path)),
        None => bail!("the configuration does not name a vkey record (`program.vkey_record`)"),
    }
}

pub fn fp_host_path(root: &Path, config: &Config) -> PathBuf {
    match &config.fp_host {
        Some(path) => resolve(root, path),
        None => root
            .join("rust-verifier")
            .join("target")
            .join("debug")
            .join("fp-host"),
    }
}

// ---------------------------------------------------------------------------------------------
// Inputs

/// The ten values the guest reads, in the guest's order, plus the paths they came from.
pub struct Inputs {
    pub policy: Vec<u8>,
    pub layout: Vec<u8>,
    pub kl: Vec<u8>,
    pub key: Vec<u8>,
    pub entry: Vec<u8>,
    pub entry_number: u32,
    pub request: Vec<u8>,
    pub y: Vec<u8>,
    pub proof: Vec<u8>,
    pub id: String,

    pub config_dir: PathBuf,
    pub ivk_dir: PathBuf,
    pub entry_path: PathBuf,
    pub request_path: PathBuf,
    pub y_path: PathBuf,
    pub proof_path: PathBuf,
    pub id_path: PathBuf,
}

fn read(path: &Path) -> Result<Vec<u8>> {
    fs::read(path).with_context(|| format!("cannot read {}", path.display()))
}

/// Reads the five paths of the reference call. The leaf number is the third word of the proof
/// header (`cpProofHead`, cp_verify.cpp:3365-3374); the leaf file is `ivk/leaf/<n>.bin`.
pub fn load_inputs(root: &Path, config: &Config) -> Result<Inputs> {
    let config_dir = resolve(root, &config.inputs.config_dir);
    let ivk_dir = resolve(root, &config.inputs.ivk_dir);
    let request_path = resolve(root, &config.inputs.request);
    let y_path = resolve(root, &config.inputs.y);
    let proof_path = resolve(root, &config.inputs.proof);
    let id_path = resolve(root, &config.inputs.id_file);

    let policy = read(&config_dir.join("policy.txt"))?;
    let layout = read(&config_dir.join("layout.txt"))?;
    let kl = read(&config_dir.join("KL.bin"))?;
    let key = read(&ivk_dir.join("key.bin"))?;
    let proof = read(&proof_path)?;
    let request = read(&request_path)?;
    let y = read(&y_path)?;
    let id = String::from_utf8(read(&id_path)?)
        .with_context(|| format!("{} is not UTF-8", id_path.display()))?
        .trim()
        .to_string();
    if fp_pv::hex_decode_32(&id).is_none() {
        bail!(
            "the commitment ID in {} is not 64 hex digits: {:?}",
            id_path.display(),
            id
        );
    }
    if proof.len() < 12 {
        bail!(
            "the proof {} is shorter than its 12-byte header",
            proof_path.display()
        );
    }
    let entry_number = u32::from_le_bytes(proof[8..12].try_into().unwrap());
    let entry_path = ivk_dir.join("leaf").join(format!("{entry_number}.bin"));
    let entry = read(&entry_path)?;

    Ok(Inputs {
        policy,
        layout,
        kl,
        key,
        entry,
        entry_number,
        request,
        y,
        proof,
        id,
        config_dir,
        ivk_dir,
        entry_path,
        request_path,
        y_path,
        proof_path,
        id_path,
    })
}

impl Inputs {
    pub fn bundle(&self) -> fp_pv::InputBundle<'_> {
        fp_pv::InputBundle {
            policy: &self.policy,
            layout: &self.layout,
            kl: &self.kl,
            key: &self.key,
            entry: &self.entry,
            entry_number: self.entry_number,
            request: &self.request,
            y: &self.y,
            proof: &self.proof,
            id: &self.id,
        }
    }

    #[must_use]
    pub fn input_digest(&self) -> [u8; 32] {
        fp_pv::input_digest(&self.bundle())
    }

    /// The stdin the guest reads: `SP1Stdin::write` in the guest's order.
    #[must_use]
    pub fn stdin(&self) -> sp1_sdk::blocking::SP1Stdin {
        let mut stdin = sp1_sdk::blocking::SP1Stdin::new();
        stdin.write(&self.policy);
        stdin.write(&self.layout);
        stdin.write(&self.kl);
        stdin.write(&self.key);
        stdin.write(&self.entry);
        stdin.write(&self.entry_number);
        stdin.write(&self.request);
        stdin.write(&self.y);
        stdin.write(&self.proof);
        stdin.write(&self.id);
        stdin
    }

    /// The frozen description of this call's input files. Paths are relative to the repository
    /// root, so a manifest recorded on one machine can be checked on another.
    pub fn manifest(&self, root: &Path) -> InputManifest {
        let files: [(&str, std::path::PathBuf, &[u8]); 9] = [
            ("policy", self.config_dir.join("policy.txt"), &self.policy),
            ("layout", self.config_dir.join("layout.txt"), &self.layout),
            ("kl", self.config_dir.join("KL.bin"), &self.kl),
            ("key", self.ivk_dir.join("key.bin"), &self.key),
            ("entry", self.entry_path.clone(), &self.entry),
            ("request", self.request_path.clone(), &self.request),
            ("y", self.y_path.clone(), &self.y),
            ("proof", self.proof_path.clone(), &self.proof),
            ("id", self.id_path.clone(), self.id.as_bytes()),
        ];
        InputManifest {
            schema: INPUT_MANIFEST_SCHEMA.to_string(),
            entry_number: self.entry_number,
            input_digest: hex(&self.input_digest()),
            files: files
                .into_iter()
                .map(|(name, path, bytes)| FileEntry {
                    name: name.to_string(),
                    path: relative(root, &path),
                    size: bytes.len() as u64,
                    sha256: hex(&fp_pv::sha256(bytes)),
                })
                .collect(),
        }
    }
}

/// The schema of a frozen input manifest (`fp-input-manifest/v1`).
pub const INPUT_MANIFEST_SCHEMA: &str = "fp-input-manifest/v1";

fn relative(root: &Path, path: &Path) -> String {
    path.strip_prefix(root)
        .unwrap_or(path)
        .display()
        .to_string()
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct InputManifest {
    pub schema: String,
    pub entry_number: u32,
    pub input_digest: String,
    pub files: Vec<FileEntry>,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FileEntry {
    pub name: String,
    pub path: String,
    pub size: u64,
    pub sha256: String,
}

impl InputManifest {
    /// Fails unless a stored manifest describes the same call: the leaf number, the bundle digest
    /// and every file's name, size and SHA-256. Paths are not compared, so a manifest frozen on
    /// the machine that holds the call also fits the prover's copy elsewhere.
    pub fn compare(&self, stored: &InputManifest) -> Result<()> {
        if stored.schema != INPUT_MANIFEST_SCHEMA {
            bail!(
                "the manifest schema is {:?}, expected {INPUT_MANIFEST_SCHEMA:?}",
                stored.schema
            );
        }
        if self.entry_number != stored.entry_number {
            bail!(
                "the manifest names leaf {}, but the proof header names leaf {}",
                stored.entry_number,
                self.entry_number
            );
        }
        if self.input_digest != stored.input_digest {
            bail!(
                "the input digest is 0x{}, but the manifest records 0x{}",
                self.input_digest,
                stored.input_digest
            );
        }
        if self.files.len() != stored.files.len() {
            bail!(
                "the manifest has {} files, but this call has {}",
                stored.files.len(),
                self.files.len()
            );
        }
        for (i, want) in stored.files.iter().enumerate() {
            if stored.files[..i].iter().any(|f| f.name == want.name) {
                bail!("the manifest names the file {:?} twice", want.name);
            }
            let Some(got) = self.files.iter().find(|f| f.name == want.name) else {
                bail!("the manifest names a file {:?} that this call does not have", want.name);
            };
            if got.size != want.size || got.sha256 != want.sha256 {
                bail!(
                    "{}: this call has {} bytes, sha256 {}, but the manifest records {} bytes, sha256 {}",
                    want.name,
                    got.size,
                    got.sha256,
                    want.size,
                    want.sha256
                );
            }
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------------------------
// The fp-host reference

pub struct FpHostOutput {
    pub stdout: String,
    pub stderr: String,
    pub status: i32,
}

pub fn run_fp_host(root: &Path, config: &Config, inputs: &Inputs) -> Result<FpHostOutput> {
    let fp_host = fp_host_path(root, config);
    if !fp_host.is_file() {
        bail!(
            "{} is missing; build it with `cargo build -p fp-host` in rust-verifier/",
            fp_host.display()
        );
    }
    let output = Command::new(&fp_host)
        .arg(&inputs.config_dir)
        .arg(&inputs.ivk_dir)
        .arg(&inputs.request_path)
        .arg(&inputs.y_path)
        .arg(&inputs.proof_path)
        .arg("-id")
        .arg(&inputs.id)
        .arg("-q")
        .output()
        .with_context(|| format!("cannot run {}", fp_host.display()))?;
    Ok(FpHostOutput {
        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        status: output.status.code().unwrap_or(-1),
    })
}

/// The public values that `fp-host`'s stdout implies, from the same values the guest has.
#[must_use]
pub fn expected_public_values(inputs: &Inputs, fp_host_stdout: &str) -> [u8; fp_pv::PV_LEN] {
    fp_pv::from_report(fp_host_stdout, &inputs.id, inputs.input_digest())
}

// ---------------------------------------------------------------------------------------------
// Vkey record

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct VkeyRecord {
    pub schema: String,
    pub program: RecordProgram,
    pub sp1: RecordSp1,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct RecordProgram {
    #[serde(default)]
    pub name: Option<String>,
    pub elf_path: String,
    pub elf_sha256: String,
    pub elf_size: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct RecordSp1 {
    pub sdk_version: String,
    pub circuit_version: String,
    /// The on-chain `programVKey` (`SP1VerifyingKey::bytes32`).
    pub vkey_bytes32: String,
    /// The 32-byte Poseidon2 digest (`SP1VerifyingKey::hash_bytes`).
    pub vkey_hash_bytes: String,
    /// The digest as eight 32-bit words, big-endian in the key.
    pub vkey_hash_u32: Vec<u32>,
}

impl VkeyRecord {
    pub fn from_elf(root: &Path, name: Option<String>, elf_path: &Path, elf: &[u8], key: &sp1_sdk::SP1VerifyingKey) -> Self {
        use sp1_sdk::HashableKey;
        let path = elf_path
            .strip_prefix(root)
            .map_or_else(|_| elf_path.display().to_string(), |p| p.display().to_string());
        Self {
            schema: VKEY_SCHEMA.to_string(),
            program: RecordProgram {
                name,
                elf_path: path,
                elf_sha256: hex(&fp_pv::sha256(elf)),
                elf_size: elf.len() as u64,
            },
            sp1: RecordSp1 {
                sdk_version: SP1_SDK_VERSION.to_string(),
                circuit_version: sp1_sdk::SP1_CIRCUIT_VERSION.to_string(),
                vkey_bytes32: key.bytes32(),
                vkey_hash_bytes: format!("0x{}", hex(&key.hash_bytes())),
                vkey_hash_u32: key.hash_u32().to_vec(),
            },
        }
    }

    pub fn write(&self, path: &Path) -> Result<()> {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)
                .with_context(|| format!("cannot create {}", parent.display()))?;
        }
        let mut text = serde_json::to_string_pretty(self)?;
        text.push('\n');
        fs::write(path, text).with_context(|| format!("cannot write {}", path.display()))
    }

    /// Fails unless the ELF on disk is the one this record was generated from.
    pub fn check_elf(&self, elf_path: &Path, elf: &[u8]) -> Result<()> {
        let got = hex(&fp_pv::sha256(elf));
        if got != self.program.elf_sha256 {
            bail!(
                "the ELF {} has SHA-256 {}, but {} records {}; regenerate the vkey record with \
                 `gen-vkey --update` after a program change",
                elf_path.display(),
                got,
                self.program.elf_path,
                self.program.elf_sha256
            );
        }
        Ok(())
    }
}

pub fn load_vkey_record(root: &Path, config: &Config) -> Result<VkeyRecord> {
    let path = vkey_record_path(root, config)?;
    let text = fs::read_to_string(&path)
        .with_context(|| format!("cannot read the vkey record {}", path.display()))?;
    let record: VkeyRecord = serde_json::from_str(&text)
        .with_context(|| format!("cannot parse the vkey record {}", path.display()))?;
    if record.schema != VKEY_SCHEMA {
        bail!(
            "vkey record schema is {:?}, expected {:?}",
            record.schema,
            VKEY_SCHEMA
        );
    }
    Ok(record)
}

/// The program vkey the contracts bind: the configuration's value when set, else the record's.
pub fn program_vkey(root: &Path, config: &Config) -> Result<String> {
    if let Some(vkey) = config.chain.as_ref().and_then(|c| c.program_vkey.clone()) {
        return Ok(vkey);
    }
    Ok(load_vkey_record(root, config)?.sp1.vkey_bytes32)
}

/// The accepted-verdict bit mask: bit `code` is set for each accepted verdict name.
pub fn accepted_verdict_mask(names: &[String]) -> Result<u16> {
    let mut mask = 0u16;
    for name in names {
        let code = match name.as_str() {
            "YES" => 1u8,
            "WITHIN_LIMITS" => 2,
            "NO" => 3,
            "NOT_A_VERIFICATION" => 4,
            "NOT_CHECKED" => 5,
            other => bail!("unknown verdict {other:?}; expected YES, WITHIN_LIMITS, NO, NOT_A_VERIFICATION or NOT_CHECKED"),
        };
        mask |= 1 << code;
    }
    Ok(mask)
}

// ---------------------------------------------------------------------------------------------
// Proof bundle ABI

/// `abi.encode(bytes publicValues, bytes proofBytes)` — the wrapper's `proof` argument.
///
/// The layout: two head words (offsets 0x40 and 0x40 + 32 + padded(publicValues)), then each
/// length-prefixed byte string padded to a multiple of 32 bytes.
#[must_use]
pub fn abi_encode_bundle(public_values: &[u8], proof: &[u8]) -> Vec<u8> {
    fn pad32(n: usize) -> usize {
        n.div_ceil(32) * 32
    }
    let pv_padded = pad32(public_values.len());
    let proof_offset = 0x40 + 32 + pv_padded;
    let mut out = Vec::with_capacity(proof_offset + 32 + pad32(proof.len()));
    out.extend_from_slice(&word(0x40));
    out.extend_from_slice(&word(proof_offset));
    out.extend_from_slice(&word(public_values.len()));
    out.extend_from_slice(public_values);
    out.resize(out.len() + (pv_padded - public_values.len()), 0);
    out.extend_from_slice(&word(proof.len()));
    out.extend_from_slice(proof);
    out.resize(out.len() + (pad32(proof.len()) - proof.len()), 0);
    out
}

fn word(value: usize) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[24..].copy_from_slice(&(value as u64).to_be_bytes());
    out
}

pub fn hex(bytes: &[u8]) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        use std::fmt::Write;
        let _ = write!(out, "{byte:02x}");
    }
    out
}

pub fn sha256_hex(bytes: &[u8]) -> String {
    hex(&fp_pv::sha256(bytes))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sdk_version_matches_lockfile() {
        let lock = fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join("../Cargo.lock"))
            .expect("zkvm/Cargo.lock");
        let mut lines = lock.lines();
        let mut found = None;
        while let Some(line) = lines.next() {
            if line == "name = \"sp1-sdk\"" {
                let version = lines.next().unwrap_or_default();
                found = Some(version.trim().to_string());
                break;
            }
        }
        assert_eq!(
            found.as_deref(),
            Some(format!("version = \"{SP1_SDK_VERSION}\"").as_str())
        );
    }

    #[test]
    fn abi_encoding_of_two_short_bytes() {
        let encoded = abi_encode_bundle(&[0xaa], &[0xbb]);
        assert_eq!(encoded.len(), 192);
        assert_eq!(encoded[31], 0x40);
        assert_eq!(encoded[63], 0x80);
        assert_eq!(encoded[95], 1);
        assert_eq!(encoded[96], 0xaa);
        assert_eq!(encoded[159], 1);
        assert_eq!(encoded[160], 0xbb);
        assert!(encoded[97..127].iter().all(|&b| b == 0));
        assert!(encoded[161..].iter().all(|&b| b == 0));
    }

    #[test]
    fn abi_encoding_of_a_full_block() {
        let pv = [7u8; 128];
        let proof = [9u8; 33];
        let encoded = abi_encode_bundle(&pv, &proof);
        // 64 head + (32 + 128) public values + (32 + 64) proof
        assert_eq!(encoded.len(), 64 + 160 + 96);
        assert_eq!(&encoded[64 + 32..64 + 32 + 128], &pv);
        assert_eq!(encoded[64 + 32 + 128 + 31], 33);
        assert_eq!(&encoded[64 + 32 + 128 + 32..][..33], &proof);
    }

    #[test]
    fn loads_the_accepted_example_from_the_configuration() {
        let root = find_root(Path::new(env!("CARGO_MANIFEST_DIR"))).expect("repository root");
        let config = load_config(&default_config_path(&root)).expect("the main configuration");
        let inputs = load_inputs(&root, &config).expect("the accepted example");
        assert_eq!(inputs.entry_number, 0, "the fixture's leaf number");
        assert_eq!(inputs.id.len(), 64, "the fixture's commitment ID");
        assert_eq!(
            inputs.bundle().proof.len(),
            inputs.proof.len(),
            "the bundle borrows the loaded proof"
        );
        let manifest = inputs.manifest(&root);
        assert_eq!(manifest.files.len(), 9);
        assert_eq!(manifest.input_digest.len(), 64);
        assert_eq!(manifest.schema, INPUT_MANIFEST_SCHEMA);
        for file in &manifest.files {
            assert!(
                !Path::new(&file.path).is_absolute(),
                "the manifest path {:?} must be root-relative",
                file.path
            );
        }
    }

    #[test]
    fn manifest_roundtrip_and_compare() {
        let root = find_root(Path::new(env!("CARGO_MANIFEST_DIR"))).expect("repository root");
        let config = load_config(&default_config_path(&root)).expect("the main configuration");
        let inputs = load_inputs(&root, &config).expect("the accepted example");
        let manifest = inputs.manifest(&root);

        let text = serde_json::to_string(&manifest).expect("serialize");
        let stored: InputManifest = serde_json::from_str(&text).expect("deserialize");
        manifest.compare(&stored).expect("a manifest must match itself");

        let mut changed = stored;
        changed.files[0].sha256 = "00".repeat(32);
        assert!(manifest.compare(&changed).is_err(), "a changed file hash was accepted");

        let mut changed: InputManifest = serde_json::from_str(&text).expect("deserialize");
        changed.entry_number += 1;
        assert!(manifest.compare(&changed).is_err(), "a changed leaf number was accepted");

        let mut changed: InputManifest = serde_json::from_str(&text).expect("deserialize");
        changed.input_digest = "11".repeat(32);
        assert!(manifest.compare(&changed).is_err(), "a changed bundle digest was accepted");
    }

    #[test]
    fn verdict_mask() {
        let names = vec!["YES".to_string()];
        assert_eq!(accepted_verdict_mask(&names).unwrap(), 1 << 1);
        let names = vec!["YES".to_string(), "WITHIN_LIMITS".to_string()];
        assert_eq!(accepted_verdict_mask(&names).unwrap(), (1 << 1) | (1 << 2));
        assert!(accepted_verdict_mask(&["MAYBE".to_string()]).is_err());
    }
}
