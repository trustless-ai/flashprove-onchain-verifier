# The S4 negative controls

`scripts/parity_negative.sh` runs every case below against the C++ reference (`cp_verify`) and the
Rust host (`fp-host`) with the same arguments and compares stdout (only the stage headings' seconds
are normalized), stderr and the exit status. It also checks each case's expected exit status and
last line, and writes `record.tsv` in this folder.

The files are made deterministically from the stored fixtures, so this folder holds no large copies:

| Case family | Made from | Mutation |
|---|---|---|
| `key_header` | `fixtures/ivk/key.bin` | byte 0 (the tag word `CPIK`) XOR 1 |
| `key_middle` | `fixtures/ivk/key.bin` | byte 500000 XOR 1 |
| `leaf_header` | `fixtures/ivk/leaf/0.bin` | byte 0 XOR 1 |
| `leaf_middle` | `fixtures/ivk/leaf/0.bin` | byte 500000 XOR 1 |
| `proof_tag` | `fixtures/example.proof` | byte 0 (the tag word `CPPF`) XOR 1 |
| `proof_version` | `fixtures/example.proof` | byte 4 (the version word) XOR 1 |
| `proof_middle` | `fixtures/example.proof` | byte 2000000 XOR 1 |
| `kl_short` | `fixtures/config/KL.bin` | the first 20 bytes (5 words; the digest reads 8) |
| `kl_odd` | `fixtures/config/KL.bin` | one byte appended (a length that is no multiple of 4) |
| `config-gap` / `config-loose` / `config-logprob` / `config-another` | `fixtures/config/policy.txt` | the `C`, `theta`, `cap` and `sT` lines |
| request and y variants | `fixtures/example.req`, `fixtures/example.y` | `r`/`e`, one token turned, one word short or long, an odd/empty file, another y |

`record.tsv` has one line per case: the case's name, the C++ exit status, the last line of stdout,
and the arguments (with `<work>` for the temporary work folder and `<fixtures>` for this worktree's
fixtures folder).
