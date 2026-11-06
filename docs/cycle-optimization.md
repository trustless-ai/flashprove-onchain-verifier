# Cycle optimization report: compile-level optimization of the SP1 guest

optimization round 1 changes only the guest's compile configuration. No `.rs` business code and no BLAKE2b
implementation was touched; the C++ sources are untouched.

## 1. Method

- The baseline run debug-executor run took 4,672 s per execute, too slow to iterate. `host-exec` was rebuilt
  with `--release` (`cargo build --release -p host-exec`, 2m13s); the release executor runs the same
  guest in about 322–542 s depending on machine load. **The executor's build does not change the
  cycle count**: the release executor reproduced baseline run's 32,385,267,062 exactly.
- Each experiment is one `cargo prove build -p guest --binaries guest` (plus the experiment's
  `--rustflags`), then one `target/release/host-exec` execute. The host prints the total cycles and
  compares `result-v1` and `YES` with `fp-host`; every measured variant passes that gate.
- The ELF's SHA-256 is recorded: an unchanged hash proves the variant's binary is identical, so its
  cycle count cannot differ.

## 2. The initial state

- `zkvm/Cargo.toml` had no `[profile.release]`. Cargo's release defaults therefore applied:
  `opt-level = 3`, `lto = false`, `codegen-units = 16`, `panic = "unwind"`.
- `sp1-build 6.10.0` always passes these rustflags to the guest build:
  `-C passes=lower-atomic`, `-C link-arg=--image-base=2013265920`, `-C panic=abort`,
  `--cfg getrandom_backend="custom"`,
  `-C llvm-args=-misched-prera-direction=bottomup`,
  `-C llvm-args=-misched-postra-direction=bottomup`.
- The target spec (`rustc --print target-spec-json -Z unstable-options --target
  riscv64im-succinct-zkvm-elf`) has `"features": "+m"` and `"panic-strategy": "abort"`.
  So the multiply extension is already enabled and panics already abort.

## 3. Experiments

| Step | Configuration change | Guest ELF (bytes / SHA-256) | Total cycles | Δ vs previous | Δ vs baseline | Consistency |
|---|---|---|---|---|---|---|
| 0 | none (cargo release defaults) | 3,207,568 / `6644c05a…` | 32,385,267,062 | — | — | PASS |
| 2 | `opt-level = 3` explicit | 3,207,568 / `6644c05a…` (identical) | 32,385,267,062 | 0 | 0 | PASS |
| 3 | `+ lto = "fat"`, `codegen-units = 1` | 2,832,504 / `4fc33452…` | 29,959,850,047 | −2,425,417,015 (−7.49%) | −7.49% | PASS |
| 4 | `+ panic = "abort"` | 2,832,504 / `77c1984a…` | 29,959,850,047 | 0 | −7.49% | PASS |
| 5 | target features: none added | unchanged (no rebuild) | 29,959,850,047 | 0 | −7.49% | n/a |
| 6 | `--rustflags="-Cllvm-args=-inline-threshold=1000"` | 12,194,968 / `8b841981…` | 27,176,326,759 | −2,783,523,288 (−9.29%) | −16.09% | PASS |
| final | `lto = "fat"`, `codegen-units = 1`, the LLVM flag (the two no-op lines removed) | 12,194,968 / `ce966b26…` | see §5 | — | — | see §5 |

Execute wall-clock varied with machine load (542.57 s, 381.30 s, 530.08 s, 482.82 s, 323.13 s) while
the cycle counts repeated exactly; wall-clock is not the metric.

## 4. Attribution

- **`lto = "fat"` + `codegen-units = 1` is the first real win: −7.49%.** Before it, `fp-core` was a
  separate codegen unit with no cross-crate inlining. The ELF also shrank from 3.21 MB to 2.83 MB.
- **The LLVM inlining threshold adds another −9.29% (total −16.09%).** Passing
  `-C llvm-args=-inline-threshold=1000` through `cargo prove build --rustflags` makes LLVM inline
  much more aggressively; the ELF grows 4.3× (2.83 MB → 12.19 MB), but the executed instruction
  count falls. This is the experiment that the cycle optimization task book asked for: the cycle count is
  sensitive to the LLVM pass configuration, and the knob is landable through `--rustflags`
  (note the value must be attached: `--rustflags="-Cllvm-args=..."`; a space after `-C` makes rustc
  read an unknown codegen option).
- **`opt-level = 3` is already the default**: the ELF and the cycles are bit-for-bit identical.
- **`panic = "abort"` changes nothing**: `sp1-build` already passes `-C panic=abort`, and the target
  spec sets the abort strategy; the explicit profile line only changed a metadata byte in the ELF
  (the cycles stayed identical), so it was reverted.
- **No target feature can be added.** The target spec declares `features = "+m"` and `+m` is
  already enabled. `rustc --print target-features` lists other RISC-V features (`+a`, `+c`, …), but
  the SP1 target is RV64IM: its core does not include them, so enabling them is outside the
  declared ISA and was not attempted.

The final build command (reproducible):

```sh
cd zkvm
cargo prove build -p guest --binaries guest --rustflags="-Cllvm-args=-inline-threshold=1000"
# zkvm/Cargo.toml: [profile.release] lto = "fat", codegen-units = 1
```

## 5. Acceptance

The final configuration (`[profile.release] lto = "fat"`, `codegen-units = 1`, and
`--rustflags="-Cllvm-args=-inline-threshold=1000"`) executes the accepted example in
**27,176,326,759 cycles**, against the baseline run baseline of **32,385,267,062**: **−5,208,940,303 cycles,
−16.09%**. The run ends with `guest exit code 0`, `status 0`, and the consistency gate:
`host-exec: result-v1 IDENTICAL`, `host-exec: YES IDENTICAL`, `host-exec: PASS (result-v1 and YES
are byte-identical to fp-host)`. The final ELF is 12,194,968 bytes, SHA-256 `ce966b26…` (the
final rebuild differs from Step 6's `8b841981…` only in metadata; its cycle count is identical).

No `.rs` file changed: the only working-tree change of optimization round 1 is `zkvm/Cargo.toml`. The C++ sources
are untouched.

# optimization round 2: the BLAKE2b soft implementation

Scope: the two BLAKE2b sites of `fp-core` — `hash/earlier.rs`'s `f2b::F` path and
`hash/modes.rs`'s `compress64` path — both of which call the single compression
`hash/blake2b.rs::f`. No C++ source and no protocol semantics were changed.

## 1. Reading the code (Step 1)

The current implementation was read first, before any edit:

- `blake2b.rs::f` works on 64-bit words already; the 32-bit wrappers (`earlier_hash_c`,
  `compress`) convert each call (16 + 16 words), a small per-compression overhead.
- The rotations use `u64::rotate_right`. The RV64IM target has no rotate instruction; rustc lowers
  `rotate_right` to a funnel shift (`fshr`), and LLVM lowers that to shifts + or. Writing
  `(x >> n) | (x << (64 - n))` by hand is the same code.
- `g` is `#[inline(always)]`; `f` is `#[inline]`. The twelve rounds are a runtime loop
  (`for r in 0..12`), and inside it `m[SIGMA[r][2 * i]]` is a dynamic, double-indexed lookup: the
  SIGMA row and the message word are not compile-time constants unless the loop is unrolled.
- `IV` and `SIGMA` are `const` arrays; `v` is a 16-word local with dynamic indices (`v[a]`, …).
- There were no explicit unrolling pragmas.

Hypotheses for the hot spots: the un-unrolled round loop and the dynamic SIGMA/message indices;
everything else (word width, rotations, inline hints) already looked reasonable.

## 2. Microbenchmarks (Step 2)

`zkvm/bench` is an independent SP1 guest with four modes (`0` current fp-core `f`, `1` handwritten
unrolled with explicit shifts, `2` `blake2b_simd 1.0.5` (no_std, portable path, one-block hash),
`3` the same unrolled code with `rotate_right`). It performs `n` compressions of one 128-byte block;
the cycles-per-compression figure subtracts the `n = 0` execution (~9.2k cycles) and divides by
`n = 4096`. `zkvm/host-exec/src/bin/bench-exec.rs` executes it. The bench ELF was built with the
optimization round 1 final profile and `-Cllvm-args=-inline-threshold=1000`, so the comparison matches the
production build.

| Mode | Implementation | `n = 0` cycles | `n = 4096` cycles | Cycles per compression |
|---|---|---|---|---|
| 0 | current `fp-core::hash::blake2b::f` | 9,219 | 12,112,937 | **2,955.0** |
| 1 | handwritten, unrolled, explicit shifts | 9,221 | 9,315,377 | **2,272.0** |
| 2 | `blake2b_simd` 1.0.5 (no_std), 1-block hash | 9,222 | 8,189,013 | **1,997.0** |
| 3 | handwritten, unrolled, `rotate_right` | 9,223 | 9,270,318 | **2,261.0** |

- **Equivalence evidence**: modes 0, 1 and 3 commit identical public values after 4,096
  compressions (`sink=269ed10c9428e2c1`, `h0=a431fa3dc99b5208`, `h7=3400bdd87529d1ef`). Mode 2 is
  a cost reference only: `blake2b_simd` exposes the standard BLAKE2b hash, not the verifier's custom
  counter/tweak, so it cannot replace `f` directly.
- **The stated premise is refuted**: the current compression costs **2,955 cycles**, not ~238k.
  The verifier performs 136,088 compressions (`q_V`); at ~2,955 cycles each that is about
  **0.40G of the 27.18G total (1.5%)**. Most of the guest's cycles are in the verifier's own
  planning and checking code (big-integer arithmetic, allocation, plans), not in BLAKE2b.
- **Best equivalent implementation**: the unrolled compression (mode 3, `rotate_right`), 2,261
  cycles, 23.5% faster than the current one. Mode 1 (explicit shifts) is statistically the same
  (2,272; the difference is noise). `blake2b_simd` is faster per compression (1,997) but needs a
  third-party crate in fp-core and does not expose the tweak API; it is not usable as a drop-in.

The whole-call projection of integrating the unrolled version is
136,088 × (2,955 − 2,261) ≈ **94M cycles, about 0.35%** of the optimization round 1 total.

## 3. Replacement (Step 3)

**Selected**: the hand-written unrolled compression (`rotate_right` form, mode 3). It is
bit-equivalent to the current compression on the benchmark's 4,096 compressions and 23.5% cheaper
per compression. It is written by us, so no third-party crate enters `fp-core` and no dependency
decision is needed.

**Not selected**: `blake2b_simd 1.0.5`. It is the fastest candidate per compression (1,997), but it
would be a new dependency of `fp-core` (only `libm` is approved there) and it exposes the standard
BLAKE2b hash — not the verifier's custom counter/tweak — so it cannot be the `f` that `f2b` and
`compress64` call. It stays a cost reference in `zkvm/bench`.

The change: in `fp-core/src/hash/blake2b.rs`, `f`'s round loop became twelve unrolled
`rounds!` calls; `g` now takes the round's two message words and the four state indices, so every
array index is a compile-time constant. `SIGMA`, `IV`, the counters and the public API are
unchanged; `compress64`, `compress`, `earlier_hash_f` and all callers are untouched.

The measured whole-call effect and the full regression follow.

## 4. Acceptance (optimization round 2)

With the unrolled compression in `fp-core`, the same accepted example executes in
**27,079,048,885 cycles**, against the optimization round 1 final 27,176,326,759: **−97,277,874 cycles (−0.36%)**,
and against the original baseline run baseline 32,385,267,062: **−16.39%**. The consistency gate passes
(`result-v1 IDENTICAL`, `YES IDENTICAL`), the guest exits 0, and the ELF is 12,165,856 bytes.

The measured saving matches the projection (136,088 × 694 ≈ 94M cycles): the small whole-call
effect is not a failure of the new compression; it is the direct consequence of BLAKE2b being only
about 1.5% of this call's cycles.

The full regression is green: `cargo test --workspace` **229 passed, 0 failed**;
`scripts/parity.sh` **31 passed, 0 failed**; `scripts/parity_e2e.sh` **3 passed, 0 failed**;
`scripts/parity_negative.sh` **70 passed, 0 failed** (rejection-name checklist 11/11).

## 5. What the numbers say

- The optimization round 2 premise "the current compression costs ~238k cycles" came from dividing the call's
  total by `q_V`. The microbenchmark shows the compression itself costs 2,955 cycles; the call's
  136,088 compressions are ~0.40G of 27.18G cycles (1.5%).
- The verifier's remaining ~26.8G cycles are its own planning and checking code: the exact
  big-integer arithmetic (`Big`/`Real`), allocation and the large plan structures. The next
  meaningful step, if the PM authorizes one, is to profile that code, not BLAKE2b.
- The benchmark harness is kept: `zkvm/bench` (four modes) and
  `zkvm/host-exec/src/bin/bench-exec.rs`; it can measure any future compression change against the
  same protocol.

# optimization round 3: profiling the verifier's own code

## Step 0: localization

The instruments: `host-exec` now prints the execute report's full opcode distribution (top 20 plus
"other"), and takes `--part 0|1|2|3` (whole call / key alone / leaf alone / request alone). The
guest gained a `part` input; a partial run executes one stage and commits its text, and `host-exec`
skips the consistency comparison for it. The full run still passes the gate. All changes are in
`zkvm/` only; no `fp-core` and no C++ change in this step.

Full call with the instruments: **27,055,820,319 cycles**, `result-v1`/`YES` IDENTICAL. (This is the
new measured baseline for optimization round 3; it differs from optimization round 2's 27,079,048,885 by a code-layout shift of
the instrumented guest.)

### Opcode distribution (whole call)

| Opcode | Cycles | Share | | Opcode | Cycles | Share |
|---|---|---|---|---|---|---|
| add | 3,819,218,385 | 14.12% | | beq | 698,642,841 | 2.58% |
| addi | 3,490,021,164 | 12.90% | | bne | 676,091,903 | 2.50% |
| sub | 2,414,953,211 | 8.93% | | mulhu | 504,601,414 | 1.87% |
| and | 2,111,775,807 | 7.81% | | lui | 417,181,068 | 1.54% |
| sll | 1,936,498,578 | 7.16% | | bltu | 386,310,842 | 1.43% |
| ld | 1,823,290,774 | 6.74% | | lwu | 301,863,665 | 1.12% |
| srl | 1,791,639,825 | 6.62% | | xor | 270,595,368 | 1.00% |
| sltu | 1,544,485,031 | 5.71% | | bgeu | 263,058,852 | 0.97% |
| sd | 1,511,831,884 | 5.59% | | auipc | 239,974,342 | 0.89% |
| or | 1,002,133,828 | 3.70% | | other | 1,106,567,209 | 4.09% |
| mul | 745,084,328 | 2.75% | | | | |

Grouped: arithmetic/logic (`add`, `addi`, `sub`, `and`, `sll`, `srl`, `or`, `sltu`, `xor`) **~68%**;
loads and stores (`ld`, `sd`, `lwu`) **~13.5%**; branches ~7.5%; `mul`/`mulhu` ~4.6%; address
materialisation (`lui`, `auipc`) ~2.4%. There are no `div`/`rem` in the top 20.

### The three stages, measured separately

| Part | Total cycles | Share of the full call | Opcode notes |
|---|---|---|---|
| key | 5,716,271,928 | 21.1% | addi 15.9%, add 11.6%, srl/sll 8.3/8.3%, and 7.0%, ld/sd 6.2/5.8% |
| leaf | 5,562,665,955 | 20.6% | addi 15.5%, add 12.1%, sll/srl 8.2/8.1%, and 7.1%, ld/sd 6.0/5.7% |
| request | 15,875,165,332 | 58.7% | add 15.8%, sub 11.3%, addi 10.9%, and 8.3%, sltu 8.1%, ld 7.2%, sd 5.5%, mul 3.2%, mulhu 2.6% |

The three parts sum to 27,154,103,215 against the full call's 27,055,820,319; the 98,282,896
difference is about twice the per-execution prefix (guest start-up plus reading the private input,
~49M each), with the call assembly negligible.

**Caveat**: every partial run also performs the shared `setup()` (policy scan, layout, shape plans,
`configure`); the full call performs it three times (once per stage). The measured ratios are
therefore not pure stage-body shares, and the key/leaf parts, which are almost equal (5.72G vs
5.56G), mix the same setup with two similar table checks.

### Preliminary hypothesis

1. **Exact big-integer arithmetic (`Big`/`Real`) is the largest head.** Arithmetic/logic is ~68% and
   loads/stores ~13.5%, with `mul`/`mulhu` ~4.6% and no division in the top 20: this is the
   limb-by-limb shape of the ported `Big`/`Real` operations, their comparisons, and the
   `Vec<u32>`/`Vec<u64>` traffic they cause. BLAKE2b is only ~1.5% (optimization round 2), so this is the
   verifier's own analysis and checking code, not hashing.
2. **Allocation and copying** show up as the ~13.5% of loads/stores plus the address materialisation
   (~2.4%): `Big`/`Real`/`Bound` are `Vec`-backed, cloned freely in plans, accounting and printed
   figures. `format!`-built strings contribute here too.
3. **The repeated setup** is unmeasured on its own. It is included in every partial run and paid
   three times in the full call; it builds all shapes and plans (`build_links`, the layer/head
   plans, the attention plans). Its size decides whether caching it across the three stages is the
   first thing to do.

### Step 1 candidates (for the TL's ordering)

- **Measure setup alone** (a plan-only/spy path in fp-core, or one more `part` mode that stops after
  `setup`): decisive for a reuse-across-stages optimization, which would otherwise be blind.
- **`Big`/`Real` fast paths**: inline storage for one- and two-limb values instead of a heap `Vec`,
  `u64`/`u128` fast paths in add/sub/mul/compare, inlining the hot element-wise loops.
- **Allocation/copy reduction**: `with_capacity`, buffer reuse, fewer `clone`s of `Big`/`Real`/
  `Binding`s in plan construction and accounting, and fewer `format!` allocations in the printed
  paths.

The instruments (`--part`, the opcode dump) stay in `zkvm/` for the next rounds.

## Step 1a: function-level profile

### Plan A: not compilable on this toolchain

The task book's plan A requires a guest-side cycle counter (`extern "C" { fn cycle_count() -> u64; }`
provided by the guest as a `sp1_zkvm::syscall_cycle_count` wrapper). **SP1 6.10.0 has no such
syscall.** The complete syscall list of `sp1-core-executor` 6.10.0 is: `HALT`, `WRITE`, the
unconstrained enter/exit, the precompiles (`SHA_EXTEND`, `SHA_COMPRESS`, `ED_ADD`, `ED_DECOMPRESS`,
`KECCAK_PERMUTE`), `COMMIT`, `COMMIT_DEFERRED_PROOFS`, `HINT_LEN`, `HINT_READ`, `MPROTECT`,
`SIG_RETURN`, `HINT_MPROTECT_FLUSH`, `DUMP_ELF`, and the two profiler-symbol calls. There is no
cycle-count call, so the `extern` symbol cannot be implemented without inline assembly, which the
red line forbids.

The only guest-visible timing mechanism is the executor's **cycle tracker**: a guest that writes
`cycle-tracker-report-start:<name>` / `cycle-tracker-report-end:<name>` lines to stdout gets
per-region cycles in `ExecutionReport::cycle_tracker`, with the SDK's `profiling` feature enabled.
That is a viable plan A' (feature-gated `fp-core` instrumentation, guest-provided writer, no
assembly), but every instrumented entry/exit costs a `WRITE` syscall; on the hottest functions
(millions of calls) the instrumentation would dominate and distort the measurement. Whether to
spend a run on A' (coarse functions only) is the TL's call.

### Plan B: host-side sampling (done)

`fp-host` was built with `--release` and run on the accepted example (2.70 s, native release);
macOS `sample` attached at 1 ms in three runs, 3,123 samples in total, sorted by self time ("top of
stack"). Command:

```sh
./target/release/fp-host <config> <ivk> <req> <y> <proof> -id <ID> -q &
sample $! 3 -mayDie -file /tmp/sample_fp.txt
```

| Symbol (fp-core unless noted) | Self samples | Share | Est. guest cycles (share × 27.06G) |
|---|---|---|---|
| `field::ext::<E as Mul>::mul` | 634 | 20.30% | ~5.49G |
| `nanov2_free` (allocator) | 317 | 10.15% | n/a (bump allocator in the guest) |
| `iop::tensor::Tensor::folded_slice_into` | 297 | 9.51% | ~2.57G |
| `numbers::real::Big::divmod` | 280 | 8.97% | ~2.43G |
| `free` (allocator) | 164 | 5.25% | n/a |
| `platform_memmove` | 163 | 5.22% | ~1.41G |
| `nanov2_malloc` (allocator) | 134 | 4.29% | n/a |
| `nanov2_calloc` (allocator) | 125 | 4.00% | n/a |
| `malloc_zone_malloc` (allocator) | 95 | 3.04% | n/a |
| `numbers::real::Big::shr` | 81 | 2.59% | ~0.70G |
| `malloc_zone_calloc` (allocator) | 69 | 2.21% | n/a |
| `verifier::common::eq_tab` | 68 | 2.18% | ~0.59G |
| `iop::tensor::Tensor::add_to` | 67 | 2.15% | ~0.58G |
| `madvise` (allocator) | 66 | 2.11% | n/a |
| `numbers::real::Big::mul` | 56 | 1.79% | ~0.48G |
| `platform_memset` | 50 | 1.60% | ~0.43G |
| `numbers::real::Big::shl` | 40 | 1.28% | ~0.35G |
| `DYLD-STUB$$free` (allocator) | 36 | 1.15% | n/a |
| `tree::tree::TreeValues::put` | 32 | 1.02% | ~0.28G |
| `iop::tensor::spread` | 32 | 1.02% | ~0.28G |
| `verifier::smallness::HTailF2::tile_self_test` | 31 | 0.99% | ~0.27G |
| `hash::blake2b::f` | 30 | 0.96% | ~0.26G |
| `numbers::real::Big::isqrt` | 25 | 0.80% | ~0.22G |
| `verifier::smallness::HTailF2::fold_sums` | 24 | 0.77% | ~0.21G |
| `numbers::real::Real::cut` | 21 | 0.67% | ~0.18G |
| allocator `realloc` paths | ~63 | ~2.0% | n/a |

Grouped: **allocator ~34%** (malloc/free/calloc/realloc/madvise — mostly absent in the guest's bump
allocator), **field extension multiplication 20.3%**, **tensor copying ~18%** (`folded_slice_into`,
`add_to`, `spread`, plus `platform_memmove`/`memset`), **`Big` arithmetic ~15.4%** (`divmod`, `shr`,
`mul`, `shl`, `isqrt`), `eq_tab` 2.2%, **BLAKE2b 0.96%**.

Caveats: native self time is not guest cycles; inlining in the guest's LTO build groups these
bodies differently, and the guest's allocator is a bump allocator (no `free` cost, but `Vec` growth
copies remain). The ranked families, not the exact percentages, are the usable signal.

### Proposed Step 1b order (for the TL)

1. **Allocation/copy reduction in the hot paths** (transferable part of the 34% + memmove/memset):
   `with_capacity`, buffer reuse, fewer `clone`s (the samples show `Vec<PlanRound>::clone`), and a
   look at `Tensor::folded_slice_into`/`add_to`/`spread` for avoidable copies.
2. **`E::mul`** (20.3%): a dedicated cubic-extension multiplication path with fewer temporaries and
   forced inline; must stay algebraically identical (the four gates check it).
3. **`Big::divmod`/`shr`/`mul`/`shl`** (~15%): fast paths for one- and two-limb operands (the usual
   case), reduce `Vec` reallocation in the divide loop.
4. **Misc**: `eq_tab`, `TreeValues::put`, `HTF2` loops.

The exact shares are evidence that the earlier "BLAKE2b/compute" hypotheses were wrong: allocation
and copying dominate natively, and field/big-integer arithmetic is the pure-compute core.

### Step 1b item 1: E::mul by Karatsuba (measured, reverted)

- **Change**: the cubic extension's product computed with six field multiplications (three
  coordinate products plus three products of coordinate sums, then reconstruction) instead of the
  three `dot3` calls (nine products summed lazily, three reductions); `#[inline(always)]`.
- **Gates**: `parity_field.sh` PASS, `parity_e2e.sh` 3/3, `cargo test --lib` 149 — algebraically
  identical.
- **Full execute**: **30,538,990,976 cycles** against 27,055,820,319: **+3,483,170,657 (+12.87%)**.
  The consistency gate still passes.
- **Reverted.** Reason: `dot3` sums three 64×64 products before its single 192-bit reduction (one
  `reduce128` per coefficient); Karatsuba saves three products but needs six individually reduced
  products, and on RV64IM a reduction is ~10 instructions against 2 `mul` instructions per product.
  The lazy-reduction schoolbook is the better shape on this target.
- **Revert check**: the rebuilt guest ELF is bit-identical to the pre-change one (SHA-256
  `9955586d5a34e9a9…`), so the 27,055,820,319 baseline stands without a rerun.

### Step 1b item 2: allocation and copying (kept, −0.68%)

- **Change**: `Tensor::folded_slice_into` now folds **in place**: the write region of each level
  lies below every later read, so `cur[a + low_half*b] = zero + (one - zero) * x` can overwrite
  the first half of `cur` directly. The per-level copy back from the caller's `room`
  (`cur.clear(); cur.extend_from_slice(&room[..half])`) is gone. The `room` parameter stays for the
  C++-shaped API (and is unused by the new loop). Values are unchanged.
- **Gates**: `cargo test --workspace` **229 passed**; `scripts/parity_base.sh` **37 passed**
  (including the IOP/tensor vectors); full execute **26,872,664,302 cycles** against 27,055,820,319:
  **−183,156,017 (−0.68%)**; `result-v1`/`YES` IDENTICAL.
- **Kept.**
- **Other item-2 sites assessed**: `Tensor::add_to` and `spread` already write through a
  caller-reused `room` and allocate nothing per call (`Form::add_to` reuses one room across its
  tensors); `Plan::finish`'s `Vec<PlanRound>::clone` is ~0.2% of the native samples and removing it
  would change the builder API for no measured benefit; the other `Vec::new()` sites in
  `smallness.rs` are one-time structure construction. The remaining allocation traffic in the
  guest is the bump allocator plus growth copies, not per-call tensor garbage.

### Step 1b item 3: Big-arithmetic fast paths (kept, −0.91%)

- **Change** (`fp-core/src/numbers/real.rs`, four contained specialisations; no representation
  change):
  1. `Big::divmod`: when both operands fit one 64-bit word, do a native `u64` divide/modulo
     instead of the limb loop (and the Knuth normalisation). The division-by-zero `assert` stays
     first, so the contract is unchanged.
  2. `Big::mul`: one-limb × one-limb operands multiply as `u64` and go through `from_u64` instead
     of allocating a two-limb zeroed result and running the carry loop.
  3. `Big::shr`: `n == 0` returns `self.clone()` (the generic path rebuilt the limbs); a value
     that fits `u64` with `n < 64` shifts as `u64`.
  4. `Big::divmod` multi-limb path: when the normalisation shift `s` is zero (the divisor's top
     limb already has its high bit set) the divisor is borrowed instead of copied through
     `shl(0)`; one `Vec` allocation per divide disappears.
- **Not changed**: `shl` already returns a clone for `n == 0`, and its generic path is what a
  `u64 << n` fast path would have to do anyway once the result exceeds 64 bits (build up to three
  limbs). The remaining divide-loop allocations (`u = a.shl(s)` and the per-digit `t` buffer) are
  structural; the measured result below already includes the reduced allocation traffic.
- **Gates**: `cargo test --workspace` **229 passed**; `scripts/parity_numbers.sh` **PASS**
  (the number vectors cover the division/multiplication/shift edge cases directly); full execute
  **26,628,389,161 cycles** against 26,872,664,302: **−244,275,141 (−0.91%)**; `result-v1`/`YES`
  IDENTICAL; consistency PASS. Guest ELF SHA-256
  `34abfffdfa9aad5f5a84188c8ed75357a181d124ef574ece2592d4c127e3ad7d`, 12,236,152 bytes.
- **Kept.** This is the largest single-step gain so far in optimization round 3 and confirms the sampling
  attribution (`Big` ~15% of native samples, small operands dominate): the savings come from
  avoiding allocation and long-division machinery on values that fit a machine word.

### Step 1b item 4: miscellaneous hot spots (kept, −0.24%)

- **Change** (four sites, none touching a protocol value):
  1. `verifier::common::eq_tab`: the `2^len` table is built in one pre-sized buffer and each
     doubling level is filled from the **back** (`t.resize(2*nt, E::zero())`, then `c` descending
     writes `t[2c]`/`t[2c+1]`). A column's writes land at or above its own index, so a descending
     walk still reads the level's inputs; the output order matches the C++ loop. One allocation
     per table instead of `len`, and no copy of each level into a fresh `Vec`.
  2. `tree::TreeValues::put`: `BTreeMap::entry` — one search instead of a `get` plus an `insert`
     on a miss. The clash/fresh bookkeeping is unchanged.
  3. `HTailF2::fold_sums`: `gx`/`gv` are filled with `with_capacity` + `push` instead of zeroing
     `vec![E::zero(); k]` and overwriting every entry; the signed sums are reduced **once**,
     `fred_diff(p, n) = fred(p + (P << 32) - n)`, instead of twice (`fred(p) - fred(n)`). The
     addend is a multiple of the modulus and exceeds any accumulator (the sums are below
     `tau * 2^64`, and the verifier's `tau ≤ 256`), so it stays inside `u128` and the canonical
     result is identical.
  4. `HTailF2::tile_self_test`: the `want` rows hold `&'static str` names instead of `String`,
     removing four heap strings per call.
- **Gates**: `cargo test --workspace` **229 passed**; `scripts/parity.sh` **31/31**;
  `scripts/parity_e2e.sh` **3/3**; `scripts/parity_negative.sh` **70/70** (rejection names 11/11);
  `scripts/parity_base.sh` **37 passed** (including the fp-core no_std scan). Full execute
  **26,564,072,573 cycles** against 26,628,389,161: **−64,316,588 (−0.24%)**; `result-v1`/`YES`
  IDENTICAL; consistency PASS. Guest ELF SHA-256
  `6dc288ea8d13da3162b0f6df0e13295ff03deae694a9ba21f7816320280bc6d3`, 12,228,360 bytes.
- **Kept.** The size of the gain matches the sampled shares of the four sites (about 4% combined,
  part of it allocator traffic); the loop bodies of `tile_self_test`/`fold_sums` themselves moved
  little, as expected.

## optimization round 3 summary

| Step | Cycles | Δ vs previous | Δ vs instrumented baseline |
|---|---|---|---|
| Step 0-1a baseline (part input, instrumented) | 27,055,820,319 | — | — |
| item 1: `E::mul` Karatsuba (reverted) | 30,538,990,976 | +3,483,170,657 (+12.87%) | +12.87% |
| item 2: `Tensor::folded_slice_into` in place | 26,872,664,302 | −183,156,017 (−0.68%) | −0.68% |
| item 3: `Big` fast paths | 26,628,389,161 | −244,275,141 (−0.91%) | −1.58% |
| item 4: miscellaneous hot spots | **26,564,072,573** | −64,316,588 (−0.24%) | **−1.82%** |

- **Final accepted optimization round 3 state: 26,564,072,573 cycles.**
  - against the optimization round 2 accepted 27,079,048,885: **−514,976,312 (−1.90%)**;
  - against the instrumented optimization round 3 baseline 27,055,820,319: **−491,747,746 (−1.82%)**;
  - against the baseline run baseline 32,385,267,062: **−5,821,194,489 (−17.97%)**.
- **Consistency**: full execute on the accepted example, `result-v1` and `YES` byte-identical to
  `fp-host`; status 0; `build=93afdaf5…` unchanged.
- **Acceptance gates (final tree)**: `cargo test --workspace` 229 passed; `parity.sh` 31/31;
  `parity_e2e.sh` 3/3; `parity_negative.sh` 70/70 with the rejection-name checklist 11/11;
  `parity_base.sh` 37 passed including the fp-core no_std scan.
- **Method notes that generalize**: (a) the accepted gains came from removing allocation and
  copying around the arithmetic (items 2–4), not from changing the algebra; (b) the one algebraic
  rewrite (Karatsuba `E::mul`) lost 12.87%, because on RV64IM a lazy 3-product/1-reduction `dot3`
  beats six reduced products; (c) the sampled attribution (Big ~15%, E::mul ~20%, allocator ~34%,
  tensor copies ~18%) predicted the sign and rough size of every accepted step.
