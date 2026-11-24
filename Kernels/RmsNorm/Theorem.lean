-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.Correct
public import Lemmas.Kernel.Existence

@[expose] public section

/-!
# Total correctness of the compiled RMSNorm kernel

For every launch satisfying `Pre`, all consistent executions are safe, every maximal execution
completes, event counts are bounded, and final memory satisfies `Post`. The kernel has 152 CTAs of
256 threads and processes arbitrary admissible batch sizes with a persistent row loop. Both warp
reductions, all three barriers, and shared-memory reuse between rows are included. Numerical results
are exact reals under the kernel's two numerical assumptions, `idealArith` and `exactApprox`.
`decode_eq` checks the compiled PTX listing. -/

namespace PTX.Kernels.RmsNorm
open PTX

/-! ## Readings this result depends on

These results hold for the executions of the Core model (`Consistent`); besides the kernel
assumptions in the statement they rely on the following readings and obligations, each
documented beside its rule (see `Core/README.md`):

- EXT-ISA, EXT-IMPORT: `ptxas` and the hardware implement the PTX ISA; the Lean source is
  the compiled PTX.
- EXT-ADDR-WRAP (THREAD-ADDR): the `[reg+immOff]` address sum is taken modulo the address width
  (`2^64` global, `2^32` shared).
- EXT-LAUNCH, with its six launch obligations (no aliases, pointer state spaces, immutable tensor
  maps, Tensor Memory requested by co-resident CTAs, no conflicting outside access and no
  PDL-dependent launch, no multimem addresses): the launch description is the real one. No
  conflicting outside access: while the kernel runs, no other agent reads or writes the memory
  the kernel writes, and no other agent writes the memory it reads or that `Post` constrains.
- EXT-VECTOR-ELEM (THREAD-ACCESS): in the kernel's `ld`/`st` with `.v2`/`.v4`, element `j` is the
  scalar operation on the bytes at `base + j·size` and carries register `j` of the vector operand;
  the elements of one access are unordered among themselves (§8.2.4, MEM-PROGRAM-ORDER).
- EXT-BAR-ZERO-COUNT (THREAD-BAR), the half "a count equal to the CTA size makes every thread of the
  CTA a participant": the kernel's `bar.sync` has an explicit count of 256 = `.maxntid` = the CTA
  size, and is read as the omitted-count form.
- EXT-FAIR (CORRECT-FAIR): `progress` and `terminates` are statements about
  the model; that a real run is a `FairRun` (fair scheduling, eventual completion of
  asynchronous operations) is taken from the CUDA programming guide, not from PTX, and is not
  proved here (the termination-transfer gap).
- EXT-SHARED (PROG-DECODE): the kernel's `.shared` variables lie at the decoder's offsets from
  `Launch.sharedBase`.
- EXT-WARP (PROG-CTA-WARP): a warp is 32 consecutive threads of a CTA.
- EXT-BAR-PARTICIPANTS (ERR-BARRIER-MISMATCH): listed because the kernel has `bar.sync`; warps are
  compared at a barrier generation by barrier name and count, not by source position.
- EXT-ENDIAN (MEM-BYTE): multi-byte values and packed pairs are stored little-endian, low half
  first.
- EXT-OBJECT-ORDER (MEM-OBJECT-ORDER-CAUSALITY): the operations on one CTA barrier (CTA and barrier
  ID) are totally ordered consistently with causality, not derived from PTX.
- EXT-ENABLES-OBJECT (MEM-OBJECT-ORDER-CAUSALITY): an operation that exists only because a record of
  an object was observed (a poll that succeeded, a barrier that returned) is not placed before that
  record in the object's order, not derived from PTX.
- EXT-STAGE-ORDER (MEM-OBJECT-ORDER-CAUSALITY): an operation's issue precedes its completion, not
  derived from PTX.
- EXT-CVTA (THREAD-MOVE): the generic address of a global allocation is its global address; the
  kernel uses the host pointers it is passed directly as the global addresses of `ld.global` and
  `st.global` (it executes no `cvta`).
- EXT-BAR-PARTICIPANTS (ERR-BARRIER-MISMATCH): for an aligned barrier with a count, "all threads in
  CTA" means its participants; the kernel's count is the CTA size (256), so the participants are
  all threads and the reading agrees with the text.
- EXT-IEEE754 (THREAD-FLOAT-IEEE): an instruction with a rounding modifier computes the exact
  result of its operands and rounds it as IEEE 754 specifies (rounding directions, infinity and
  NaN arithmetic, the sign of an exact zero, invalid operations and overflow); the manual's own
  overrides (`.ftz`, `.sat`, `.relu`, `.satfinite`, the unspecified NaN) take precedence, and the
  rules come from IEEE 754-2008/2019, not from PTX.
- EXT-FLOAT-BITS (THREAD-BITS): under the ideal-arithmetic assumption a result is a real number
  that may not be representable in its format; where its bits are read, they are that number
  rounded to nearest, ties to even.
- `Assumptions.idealArith` and `Assumptions.exactApprox`, in the statement: the five floating
  forms `add.ftz.f32`, `fma.rn.ftz.f32`, `mul.rz.ftz.f32x2`, `cvt.f32.f16` and
  `cvt.rn.f16x2.f32` are exact real arithmetic; the kernel's one `div.approx.ftz.f32` and one
  `rsqrt.approx.ftz.f32` are the exact `a / b` and `1 / sqrt a`.
-/

/-- Total correctness over all consistent event executions, under `idealArith` and `exactApprox`. -/
theorem correct {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) :
    Correct kernel [Assumptions.idealArith, Assumptions.exactApprox] L mem0 (Post P mem0) :=
  Proof.correct hpre

/-- The correctness theorem is non-vacuous: its model admits a completed execution. -/
theorem completed_execution {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) :
    ∃ X, Consistent L kernel [Assumptions.idealArith, Assumptions.exactApprox] mem0 X ∧
      Complete L X :=
  (correct hpre).complete_exists (Proof.valid hpre)
    (by simp [Assumptions.idealArith, Assumption.idealReal, Assumptions.exactApprox,
      Assumption.approxExact])

/-- A completed execution and output satisfying this kernel's postcondition exist. -/
theorem realizable_result {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) :
    ∃ X mf, Consistent L kernel [Assumptions.idealArith, Assumptions.exactApprox] mem0 X ∧
      Complete L X ∧
      IsFinal L mem0 X mf ∧ Post P mem0 mf :=
  (correct hpre).output_exists (Proof.valid hpre)
    (by simp [Assumptions.idealArith, Assumption.idealReal, Assumptions.exactApprox,
      Assumption.approxExact])

end PTX.Kernels.RmsNorm
