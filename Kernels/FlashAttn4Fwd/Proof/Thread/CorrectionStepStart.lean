-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionStepBase

@[expose] public section

/-! # The correction warps' first steps

The register reduction reaches the start barrier with no local instruction between. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- `setmaxnreg.dec 88`, then the start barrier. -/
theorem step_setMaxReg {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {d : D} {t u : TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0)
    (hs : d.site = .setMaxReg) (hi : Inv L g d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_5)
  obtain rfl := fires_next (show AdvancesOp (.setMaxReg _ _) from trivial) hf
  refine step_of_run (d' := ⟨.bar0, i, tt, aw, a, o⟩) (by simp [next])
    (inv_same (d := ⟨.setMaxReg, i, tt, aw, a, o⟩) .bar0 hi rfl
      (.inr (.inr ⟨hi.start (.inl rfl), .inr (.inl rfl)⟩)) (by simp [Site.inTrip])
      (by simp [Site.rescale]) (fun _ => .inl rfl)) rfl ⟨0, ?_⟩
  corr_seg (At.next h) hpre

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
