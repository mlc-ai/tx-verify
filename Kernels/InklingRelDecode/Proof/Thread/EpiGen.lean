-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EpiWait

@[expose] public section

/-! # Generic steps of the epilogue

The step of an event instruction that continues at the next instruction (`step_issue_of`): the
segment from the instruction's successor to the next site is a hypothesis. The step of a
broadcast (`step_shfl_of`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epi
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {d dn : D} {t u : TState} {e : Event} {ins : Instr}

/-- An instruction that continues at the next instruction (`hu`) and every event takes to `dn`:
the segment to `dn`. -/
theorem step_issue_of
    (hu : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u) → u = PTX.next t)
    (hn : ∀ e', next d e' = some (some dn))
    (hseg : SegE L g (d.site.pc + 1) (facts d) dn.site.pc (facts dn))
    (hin : Inv dn) (h : At t d.site.pc (facts d))
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    Cont L g d e u := by
  obtain rfl := hu hf
  right
  obtain ⟨k, hseg⟩ := hseg
  obtain ⟨t', hr', ht'⟩ := hseg _ (At.next h)
  exact ⟨dn, t', hn e, run_rtg hr', ht', hin⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Epi
