-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.SegQ
import Kernels.FlashMlaSparseDecodeH64.Flow.Code
import Kernels.FlashMlaSparseDecodeH64.Gen.StepMma

@[expose] public section

/-! # The MMA warp's obligations at the length loads and the trap

The two `.nc` length loads record the word they read (a value that is not one 32-bit word stops
the machine) and continue to the second load, the trap or the first Q load (`land_q0`); the trap
fires undefined behaviour and no continuing event. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The trap fires no continuing event. -/
theorem stepOk_trap (l0 l1 neg cnt pha par : BitVec 64) :
    (code P L g).StepOk ⟨.trap, l0, l1, neg, cnt, pha, par⟩ :=
  ⟨fun _ _ _ hc hf => by
    rw [show (code P L g).pc ⟨.trap, l0, l1, neg, cnt, pha, par⟩ = 1896 from rfl,
      Flow.code_1896] at hc
    cases hc
    exact absurd hf.2 (by simp)⟩

theorem stepAt_trap (d : D) (hs : d.site = .trap) : (code P L g).StepAt d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  simp only at hs
  mma_sites s except [.trap => (stepOk_trap l0 l1 neg cnt pha par)]

theorem stepAt_loadTopk (hp : Pre P L m) (d : D) (hs : d.site = .loadTopk) :
    (code P L g).StepAt d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  simp only at hs
  mma_sites s

theorem stepAt_loadExtra (hp : Pre P L m) (d : D) (hs : d.site = .loadExtra) :
    (code P L g).StepAt d := by
  obtain ⟨s, l0, l1, neg, cnt, pha, par⟩ := d
  simp only at hs
  mma_sites s

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
