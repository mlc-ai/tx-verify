-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmaCopy.Proof.Correct
public import Lemmas.Kernel.Existence

@[expose] public section

namespace PTX.Kernels.TmaCopy
open PTX

section
variable {L : Launch} {A B : Nat} {x : Value} {mem0 : Mem0}

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
- EXT-OBJECT-ORDER (MEM-OBJECT-ORDER-CAUSALITY): the operations on the mbarrier are totally ordered
  consistently with causality, not derived from PTX.
- EXT-ASYNC-OBJECT and EXT-ENABLES-OBJECT (MEM-OBJECT-ORDER-CAUSALITY): orders of the mbarrier and
  the bulk copy's completion, not derived from PTX.
- EXT-STAGE-ORDER (MEM-OBJECT-ORDER-CAUSALITY): an operation's issue precedes its completion, not
  derived from PTX.
- EXT-ENDIAN (MEM-BYTE): multi-byte values are stored little-endian, low byte first; the
  memory bytes `Pre` and `Post` describe are read in this order.
-/

/-- **Main theorem.** For every one-CTA launch and launch memory satisfying `Pre`, under no kernel
assumptions: no possible execution has undefined behaviour (in particular, `buf` is read only after
the mbarrier phase that the bulk copy completes), every maximal execution has every thread exited
and all async work drained (pending copies can complete and their waits can then succeed), the
counted events are bounded, and after a complete execution `B` holds the first word of `A`. -/
theorem correct (hpre : Pre L A B x mem0) : Correct kernel [] L mem0 (Post B x mem0) :=
  Proof.correct hpre

/-- The correctness theorem is non-vacuous: its model admits a completed execution. -/
theorem completed_execution (hpre : Pre L A B x mem0) :
    ∃ X, Consistent L kernel [] mem0 X ∧ Complete L X :=
  (correct hpre).complete_exists (Proof.valid hpre) (by simp )

/-- A completed execution and output satisfying this kernel's postcondition exist. -/
theorem realizable_result (hpre : Pre L A B x mem0) :
    ∃ X mf, Consistent L kernel [] mem0 X ∧ Complete L X ∧
      IsFinal L mem0 X mf ∧ Post B x mem0 mf :=
  (correct hpre).output_exists (Proof.valid hpre) (by simp )

end

end PTX.Kernels.TmaCopy
