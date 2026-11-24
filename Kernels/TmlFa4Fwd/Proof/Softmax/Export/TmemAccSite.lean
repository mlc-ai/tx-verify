-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Shape
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.NoLdSt

@[expose] public section

/-! # The sites of the softmax loads and stores

A softmax store is fired at a P store (`soft_st_site`); a softmax load at a score load or at an
implicit-wait state at sub-step 0 (`soft_ld_site`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

set_option maxHeartbeats 8000000 in
theorem soft_st_site {d : Softmax.D} {pc a : Nat} {vals : List Value} {sh : TcShape}
    (hev : Softmax.Ev p L g d ⟨pc, .tc (.st a vals sh)⟩) : ∃ r q, d.site = .pst r q := by
  obtain ⟨s, v, kk, acc⟩ := d
  cases s
  case pst r q => exact ⟨r, q, rfl⟩
  all_goals exfalso
  all_goals simp only [Softmax.Ev] at hev
  all_goals first | exact (epi_noldst (hev := hev) (by trivial)).elim | skip
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals (try subst_vars)
  all_goals simp_all [Softmax.rdOrUb, Softmax.tcLdOrUb]

set_option maxHeartbeats 8000000 in
theorem soft_ld_site {d : Softmax.D} {pc a : Nat} {vals : List Value} {sh : TcShape}
    (hev : Softmax.Ev p L g d ⟨pc, .tc (.ld a vals sh)⟩) :
    (∃ r c, d.site = .sld r c) ∨ ∃ c, d.site = .sldw c ∧ d.k ≠ 1 := by
  obtain ⟨s, v, kk, acc⟩ := d
  cases s
  case sld r c => exact .inl ⟨r, c, rfl⟩
  case sldw c =>
    refine .inr ⟨c, rfl, fun hk => ?_⟩
    simp only at hk
    subst hk
    simp [Softmax.Ev] at hev
  all_goals exfalso
  all_goals simp only [Softmax.Ev] at hev
  all_goals first | exact (epi_noldst (hev := hev) (by trivial)).elim | skip
  all_goals (try split at hev)
  all_goals shape_destruct hev
  all_goals (try subst_vars)
  all_goals simp_all [Softmax.rdOrUb, Softmax.tcLdOrUb]

end
end PTX.Kernels.TmlFa4Fwd.Proof
