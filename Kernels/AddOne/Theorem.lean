-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.AddOne.Proof.Correct
public import Lemmas.Kernel.Existence

@[expose] public section

namespace PTX.Kernels.AddOne
open PTX

section
variable {L : Launch} {A : Nat} {x : Nat → BitVec 32} {mem0 : Mem0}

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
- EXT-ENDIAN (MEM-BYTE): multi-byte values are stored little-endian, low byte first; the
  memory bytes `Pre` and `Post` describe are read in this order.
-/

/-- **Main theorem.** For every launch and launch memory satisfying `Pre`, under no kernel
assumptions: no possible execution has undefined behaviour (in particular no data race),
every maximal execution has every thread exited, executions are bounded, and the memory
after a complete execution satisfies `Post`. -/
theorem correct (hpre : Pre L A x mem0) : Correct kernel [] L mem0 (Post L A x mem0) :=
  Proof.correct hpre

/-- The correctness theorem is non-vacuous: its model admits a completed execution. -/
theorem completed_execution (hpre : Pre L A x mem0) :
    ∃ X, Consistent L kernel [] mem0 X ∧ Complete L X :=
  (correct hpre).complete_exists (Proof.valid hpre) (by simp)

/-- A completed execution and output satisfying this kernel's postcondition exist. -/
theorem realizable_result (hpre : Pre L A x mem0) :
    ∃ X mf, Consistent L kernel [] mem0 X ∧ Complete L X ∧
      IsFinal L mem0 X mf ∧ Post L A x mem0 mf :=
  (correct hpre).output_exists (Proof.valid hpre) (by simp)

end

end PTX.Kernels.AddOne
