-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.BlockSum.Proof.Correct
public import Lemmas.Kernel.Existence

@[expose] public section

namespace PTX.Kernels.BlockSum
open PTX

variable {L : Launch} {A B : Nat} {x : Nat → ℝ} {mem0 : Mem0}

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
- EXT-FAIR (CORRECT-FAIR): `progress` and `terminates` are statements about
  the model; that a real run is a `FairRun` (fair scheduling, eventual completion of
  asynchronous operations) is taken from the CUDA programming guide, not from PTX, and is not
  proved here (the termination-transfer gap).
- EXT-CVTA (THREAD-MOVE): `cvta.to.global` of a global allocation's generic address is the same
  address.
- EXT-SHARED (PROG-DECODE): the kernel's `.shared` variables lie at the decoder's offsets from
  `Launch.sharedBase`.
- EXT-WARP (PROG-CTA-WARP): a warp is 32 consecutive threads of a CTA.
- EXT-BAR-PARTICIPANTS (ERR-BARRIER-MISMATCH): listed because the kernel has `bar.sync`; warps are
  compared at a barrier generation by barrier name and count, not by source position.
- EXT-OBJECT-ORDER (MEM-OBJECT-ORDER-CAUSALITY): the operations on one CTA barrier (CTA and barrier
  ID) are totally ordered consistently with causality, not derived from PTX.
- EXT-STAGE-ORDER (MEM-OBJECT-ORDER-CAUSALITY): an operation's issue precedes its completion, not
  derived from PTX.
- EXT-ENDIAN (MEM-BYTE): multi-byte values are stored little-endian, low byte first; the
  memory bytes `Pre` and `Post` describe are read in this order.
- EXT-ENABLES-OBJECT (MEM-OBJECT-ORDER-CAUSALITY): enabling respects the order of each CTA barrier;
  not derived from PTX.
- EXT-IEEE754 (THREAD-FLOAT-IEEE): an instruction with a rounding modifier computes the exact
  result of its operands and rounds it as IEEE 754 specifies (rounding directions, infinity and
  NaN arithmetic, the sign of an exact zero, invalid operations and overflow); the manual's own
  overrides (`.ftz`, `.sat`, `.relu`, `.satfinite`, the unspecified NaN) take precedence, and the
  rules come from IEEE 754-2008/2019, not from PTX.
- EXT-FLOAT-BITS (THREAD-BITS): under the ideal-arithmetic assumption a result is a real number
  that may not be representable in its format; where its bits are read, they are that number
  rounded to nearest, ties to even.
- `Assumptions.idealAdd` (ASM-IDEAL, in the statement): the kernel's one floating instruction form,
  `add.f32`, is exact real addition. -/

/-- Total correctness of the decoded PTX over all consistent event executions. Each
CTA writes its exact input sum; barriers and the finite reduction always complete. -/
theorem correct (hpre : Pre L A B x mem0) : Correct kernel [Assumptions.idealAdd] L mem0
    (Post L B x mem0) :=
  Proof.correct hpre

/-- The correctness theorem is non-vacuous: its model admits a completed execution. -/
theorem completed_execution (hpre : Pre L A B x mem0) :
    ∃ X, Consistent L kernel [Assumptions.idealAdd] mem0 X ∧ Complete L X :=
  (correct hpre).complete_exists (Proof.valid hpre) (by
    simp [Assumptions.idealAdd, Assumption.idealReal])

/-- A completed execution and output satisfying this kernel's postcondition exist. -/
theorem realizable_result (hpre : Pre L A B x mem0) :
    ∃ X mf, Consistent L kernel [Assumptions.idealAdd] mem0 X ∧ Complete L X ∧
      IsFinal L mem0 X mf ∧ Post L B x mem0 mf :=
  (correct hpre).output_exists (Proof.valid hpre) (by
    simp [Assumptions.idealAdd, Assumption.idealReal])

end PTX.Kernels.BlockSum
