<!-- SPDX-License-Identifier: Apache-2.0 -->

# TxVerify

TxVerify verifies compiled production GPU kernels by splitting the conditions a proof rests on
into two parts. A shared **core** holds the rules that the PTX manual states clearly, with
conservative readings where it is vague. A condition that a kernel needs beyond the core becomes
an **assumption** of that kernel, listed in its theorem for a person to review. Lean checks the
proof. For every launch and input that meet a kernel's precondition, its theorem `correct` states
four properties under the core and the kernel's assumptions:

* **safe**: no execution has undefined behaviour, in particular no data race;
* **progress**: an execution that cannot grow has every thread exited and all asynchronous work
  finished;
* **terminates**: one bound covers the counted events of every execution (failed polls are not
  counted);
* **result**: after a complete execution, memory satisfies the specification, over the reals.

Each kernel also proves that a complete execution and a final memory satisfying the
postcondition exist. `Tests/Kernel/Statements.lean` checks all theorem statements and that they use only
Lean's three standard axioms.

## What to review

The proofs are checked by Lean. A reader who wants to trust a theorem reviews three things:

1. **The core** (`Core/`): the rules of the model, each with the PTX ISA passage or other evidence
   it rests on, the interpretations (`EXT-` notes) where the manual leaves a choice, and the assumption
   constructors a kernel may use. The [core reference](docs/core/README.md) presents every
   concept and rule in reading order, generated from the Lean comments.
   [Core/README.md](Core/README.md) is the review guide and the index of all rules.
2. **The specification** of a kernel: `Kernels/<K>/Spec.lean` (the program, `Pre` and `Post`).
3. **The assumptions** of a kernel: `Kernels/<K>/Assumptions.lean`, each limited to the
   instruction forms or sites it names. Each `Theorem.lean` also lists the interpretations its
   statement depends on, and `Tools/reading_uses.py` checks that list.

## Proved kernels

All kernels target `sm_100a`.

| Kernel | PTX instructions | What it exercises | Assumptions |
| --- | ---: | --- | --- |
| `AddOne` | 9 | one load, add and store per thread | none |
| `CopyDynamic`, `CopyLdg`, `RowSum`, `BlockSum` | 16–31 | loads and stores, a loop, a CTA barrier | `CopyLdg`: read-only `ld.global.nc` at one site; sums: exact `add.f32` |
| `TmaCopy` | 18 | a bulk copy completing on an mbarrier | none |
| `TcGemm` | 60 | Tensor Memory and one `tcgen05` MMA | none |
| `RmsNorm` | 295 | TIRx RMSNorm: persistent loop, warp shuffles | exact arithmetic, approximate math as exact |
| `Fp16Gemm8192` | 1,097 | TIRx production FP16 GEMM: 2-CTA MMA, TMA ring, cluster launch control ([README](Kernels/Fp16Gemm8192/README.md)) | 3 |
| `FlashAttn4Fwd` | 4,897 | FlashAttention-4 forward with symbolic shapes ([README](Kernels/FlashAttn4Fwd/README.md)) | 8 |
| `FlashMlaSparseDecodeH64` | 3,612 | FlashMLA sparse decode, 64 heads, paged FP8 KV cache with top-k indices ([README](Kernels/FlashMlaSparseDecodeH64/README.md)) | 11 |
| `InklingRelDecode` | 2,856 | Inkling 2 Small relative-attention decode (Gluon), symbolic batch and splits ([README](Kernels/InklingRelDecode/README.md)) | 11 |
| `TmlFa4Fwd` | 9,206 | tml-fa4 SM100 forward (CuTeDSL), paged KV with relative bias ([README](Kernels/TmlFa4Fwd/README.md)) | 10 |

Kernels built from an upstream project record its repository, commit and toolchain in a
manifest; no upstream source is vendored. The small kernels are compiled from the `.cu` file next
to their PTX or are hand-written and checked by `ptxas`.

## Layout

| Path | Content |
| --- | --- |
| `Core/` | the model and all trusted content |
| `Lemmas/` | the generic proof library, checked by Lean |
| `Kernels/<K>/` | PTX, `Spec.lean`, `Assumptions.lean`, `Theorem.lean`, generated `Flow/`, `Proof/` |
| `Tests/`, `tests/` | litmus and sanity tests in Lean; Python checks and the proof-structure lint |
| `Tools/` | PTX parser and Lean exporter, generators, contract and document checks |
| `docs/` | the [core reference](docs/core/README.md) |

A proof may be organized in any way that Lean accepts; only the core, the specification and the
assumptions are trusted. The proofs here share one style: generated flow tables, a thread layer
with one site machine per warp role, a protocol layer for cross-thread hand-offs, and the four
conclusions. `tests/test_proof_lint.py` checks that style for the kernels that opt into it
(`FRAMEWORK_KERNELS`), and checks every kernel for `sorry` and new axioms.

## Scope

The core covers about 160 of the roughly 190 instructions in the PTX ISA 9.5 manual; an
instruction form without a rule is rejected explicitly, so a kernel that uses one cannot be
proved. The core leaves out `wgmma`, the texture and surface instructions, the video
instructions, `wmma`, and function calls and stack allocation. Relaxed lock-free reasoning is out
of scope. The supported fragment is listed in the [core reference](docs/core/README.md) and in
[Core/README.md](Core/README.md).

## Build and check

Lean 4.35.0 with Mathlib v4.35.0. The Python tools use only the standard library.

```bash
lake exe cache get
Tools/build.sh                                  # lake --wfail build, serialized
lake env lean Tests/Kernel/Statements.lean             # theorem statements and axioms
lake env lean Tests/Kernel/Contract.lean               # contract text (rerun after comment-only edits)
TXVERIFY_BUILD=1 env -u PYTHONPATH python3 -m pytest -q -p no:cacheprovider tests
python3 Tools/contract_index.py --check         # rule index in Core/README.md
python3 Tools/coredoc.py --check                # docs/core is current
python3 Tools/reading_uses.py --lean            # interpretation disclosures
pre-commit run --all-files                      # text checks, quotes, lint
```

The quote check needs the PTX ISA text: set `TXVERIFY_PTX_SPEC=<path>`.
