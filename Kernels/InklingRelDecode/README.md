# Inkling 2 Small relative-attention decode (Gluon), symbolic batch and splits

The kernel is `_rel_verify_kernel` of the Inkling 2 Small decode path in vLLM. This directory
holds its frozen PTX, the Lean decoding of that PTX, the specification, the kernel assumptions and
the proof that the PTX meets the specification. [Theorem.lean](Theorem.lean) states `correct`
(safe, makes progress, terminates and stores the output of `Post`), `completed_execution` and
`realizable_result` for every launch that satisfies `Pre` ([Spec.lean](Spec.lean)), under the
kernel assumptions `Assumptions.all` ([Assumptions.lean](Assumptions.lean), with the software
`exp2` template in [Assumptions/Exp2Template.lean](Assumptions/Exp2Template.lean), the numeric
readings in [Assumptions/Numerics.lean](Assumptions/Numerics.lean) and the read-only inputs in
[Assumptions/InputReadOnly.lean](Assumptions/InputReadOnly.lean)). `Theorem.lean` also lists the readings of the specification that
the result depends on.

Status of the proof: complete. The three theorems of `Theorem.lean` (`correct`,
`completed_execution`, `realizable_result`) take `Pre` as their only hypothesis besides the kernel
assumptions in the statement, and depend only on the axioms `propext`, `Classical.choice` and
`Quot.sound`. `Tests/Kernel/Statements.lean` checks their statements and axioms.

## Verification target

- Source: vLLM pull request 67325, commit `d664cd1e96052857aea2aa844eeba571c24758b4`,
  `vllm/models/inkling2/ops/attention.py`, the Gluon kernel `_rel_verify_kernel` for `sm_100a`
  (Apache-2.0). The commit and the file hash are recorded in [manifest.json](manifest.json).
- The program that is verified is that commit with the two synchronization fixes of
  [ptx-build/attention-sync.patch](ptx-build/attention-sync.patch): the softmax warps wait for
  `o_done` in every iteration `i > 0` (PTX ISA 9.5 section 9.7.15.16.5.1), and the epilogue waits
  for `o_final` before the `num_iters` branch. The unpatched kernel is not covered by the theorem.
- [rel_verify_sm100a.ptx](rel_verify_sm100a.ptx): the 2856 instructions that Triton 3.8.0 and
  `ptxas` of CUDA 13.2.51 produce from the patched kernel. Its SHA256,
  `85f2300c5126b67afaae007417017e15ed02aec959f6e799396a2d05508ac895`, is recorded in the
  manifest. No PTX text is rewritten after the compiler.
- [Ptx.lean](Ptx.lean) is generated from the PTX by `Tools/export_lean.py`.
  [Data/Decoded.lean](Data/Decoded.lean) is the Core decoder's output on it, and
  [Audit/Decode.lean](Audit/Decode.lean) checks by kernel reduction that the Core decoder
  produces exactly that program. [Data/TensorMaps.lean](Data/TensorMaps.lean) states the tensor
  map of the launch.

## Fixed configuration

The compile-time constants are those of `config` in the manifest: 12 query heads over 2 KV heads
(group 6), head dimension 128, `BLOCK_M = 64`, `BLOCK_N = FA_BLOCK = 128`, `PAGE = 64`,
`REL = 1024`, `REL_PAD = 1280`, `STAGES = 3`, the full-attention layer (`IS_LOCAL = False`) with
`FUSE_GATE = False` and `DRAFT = False`, bf16 inputs, f32 accumulation. The local-window, gated
and draft specializations compile to other PTX programs and are separate verification targets.

The launch has grid `(num_splits, 2, batch)`, 256 threads per CTA (8 warps), no cluster, 213340
bytes of dynamic shared memory and 512 Tensor Memory columns per CTA (`tcgen05.*.cta_group::1`).
Warps 0 to 3 form the default partition (prologue, query load, softmax, epilogue), warp 6 loads the
paged key-value cache with `cp.async.bulk.tensor.2d` through the tensor map `kv_desc`, warp 7
issues the `tcgen05.mma` and warps 4 and 5 are idle.

The symbolic parameters (`Params` in `Spec.lean`) are the batch, `num_splits`, the token count,
`cu_seqlens_q`, `seq_lens`, the page table, the cache view (`page_rows`, `head_rows`, `head_cols`,
the slot stride) and the strides, `softmax_scale`, and the values of the bf16 inputs.

## What is proved

For every launch that satisfies `Pre`:

- safety: no execution of the model is undefined (no data race, no misuse of a barrier,
  mbarrier, Tensor Memory or `setmaxnreg`, no memory fault);
- progress and termination: every maximal fair run completes;
- the result: each CTA `(split, kv_head, request)` stores, for the valid rows of its 6 query heads
  and up to 10 query tokens (rows 60 to 63 are padding), the f32 partial output `OPart` and the
  log2 normalizer `LsePart` of its key blocks `split, split + num_splits, ...`, as `Post` states;
  every global byte outside the two output arrays keeps its launch value. The combine kernel that
  merges the splits is outside this kernel.

A key `k` of a request is visible to token `tok` when `k <= past + tok`. A key in a block with
relative logits (`n >= n_bias`) adds the relative logit `rel[token, head, k - rel_base]`. The
weight of a visible key is `2 ^ (c * (scale * S + bias))`, where `c` is the f32 constant
`0f3FB8AA3B` that the PTX multiplies by (the f32 value nearest `log2 e`), and `Post` states
exactly that with base-2 exponentials.

## The precondition

`Pre` ([Spec.lean](Spec.lean)) describes only the launch and the memory at launch, not the
execution. It fixes the grid, block and cluster shape; the scalar parameters and the pointer
parameters of the kernel; the tensor map `kv_desc` and its allocation; the ranges of the sizes
(`batch < 2^16`, the 32-bit index arithmetic of the kernel, at most 10 query tokens per request);
the shared-memory window; that the bf16 inputs, the integer arrays and the output arrays have
the stated contents and allocation and are disjoint; and that every box the kernel loads lies
inside the cache view with a 16-byte aligned start, so no out-of-bounds fill is used. The
cache rows that a last block loads beyond `seq_lens` must be finite bf16 values, because a
non-finite value would reach the output through the product with a zero weight. The launch must also meet the six obligations of
EXT-LAUNCH; in particular the kernel is compiled for programmatic dependent launch, and the
theorem covers a launch that is not a dependent grid and has no dependent grid running at the same
time.

## The assumptions

The kernel's own assumptions (`Assumptions.all`) read approximate or rounding instructions as
exact functions so that the theorem can state the exact attention. The hardware's rounding and
approximation error is therefore not part of the result. They are:

- `idealArith`: the `kind::f16` MMAs with bf16 inputs and an f32 accumulator, the `.f32` and
  `.f32x2` arithmetic and the floating comparisons are exact real operations.
- `approx`: `ex2.approx.ftz.f32` and `rcp.approx.ftz.f32` are the exact `2 ^ x` and `1 / x`.
- `swExp2`: the 16 instances of the software `exp2` sequence are the exact `2 ^ x`.
- `lg2Exact`, `divFullExact`, `negExact`, `bf16Exact`: one `lg2.approx.ftz.f32`, one
  `div.full.f32`, one `neg.f32`, and the `cvt.f32.bf16` and `cvt.rn.bf16x2.f32` instructions are
  read as exact. The kernel rounds the probabilities to bf16 before the second MMA; the theorem
  does not model that rounding.
- `commitOrder`, `pollAgree`, `setMaxNRegSync`: two `tcgen05.commit` sites complete in order, the
  six mbarrier poll branches keep the lanes of a warp together, and the `setmaxnreg.inc 256` at the
  head of the worker dispatch loop needs no warpgroup synchronization.
- `inputReadOnly`: the kernel does not write its input tensors, and a plain `ld.global` at its 203
  global loads returns the launch content.

`Theorem.lean` states each assumption with the instruction sites it covers, and lists the readings
of the Core model (the EXT notes of `Core/`) that the statement depends on.

## Proof structure

All proofs are under [Proof/](Proof/), a layered tree. `Proof/Top/Correct.lean` proves
`Top.correct`, and `Proof/Correct.lean` derives the three public theorems of `Theorem.lean` from it.

- Roles (`Proof/Startup`, `Prologue`, `Softmax`, `Epilogue`, `Dispatch`, `Loader`, `Mma`): one
  machine per warp role that follows the code of the role state by state, with its `Export/`
  facts as the only thing other layers import. The tables of the control flow, the code and the
  sites ([Flow/](Flow/), [Gen/](Gen/)) are generated by `Tools/flow_gen.py` and
  `Tools/code_table.py`.
- Common (`Proof/Common`): what the roles share, and the tracking of every thread.
- Interface and library (`Proof/Iface`, `Proof/Lib`): the facts the upper layers read about the
  consistent executions, and the pure lemmas under them.
- Protocol (`Proof/Protocol`): the mbarrier rings of the key-value slots, the S, P and O hand-offs
  in Tensor Memory, the named barriers, the allocation, the values and the exit.
- Top (`Proof/Top`): safety (`Top/Safe`), progress (`Top/Prog`), the bound of every thread
  (`Top/Bound`) and the values stored (`Top/Result`), combined into
  `Correct kernel Assumptions.all L mem0 (Post P mem0)` with no hypothesis other than `Pre`.

## Check it

From the repository root, with the toolchain of `lean-toolchain`:

```bash
Tools/build.sh Kernels.InklingRelDecode.Theorem   # the theorems and everything they use
Tools/build.sh Tests.Kernel.Statements           # the statements mention only reviewed modules
python3 Tools/reading_uses.py --lean              # the readings listed in Theorem.lean
```

`Tests/Kernel/Statements.lean` fails the build unless the proof of each theorem uses only the
axioms `propext`, `Classical.choice` and `Quot.sound` and its statement mentions only definitions
of `Core/`, `Spec.lean`, `Ptx.lean`, `Assumptions.lean` and `Assumptions/`, the decoded program
and the tensor map, and the Lean and Mathlib libraries.

## Regenerate the PTX

The frozen PTX is reproduced byte for byte without a GPU by the scripts of
[ptx-build/](ptx-build/) (see its README): the pinned `attention.py`, the patch, Triton 3.8.0 and
the `ptxas` of CUDA 13.2.51, built through `ptx-build/ns_run.sh`. The scripts generate PTX and no
proof. After regenerating, `Ptx.lean`, `Data/Decoded.lean`, `Flow/` and `Audit/Decode*.lean` are
regenerated from it with the tools in `Tools/`.
