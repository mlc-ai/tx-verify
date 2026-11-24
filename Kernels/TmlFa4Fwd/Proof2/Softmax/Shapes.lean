-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.ShapeCtl
public import Kernels.TmlFa4Fwd.Proof2.Softmax.ShapeScan
public import Kernels.TmlFa4Fwd.Proof2.Softmax.ShapeTc
public import Kernels.TmlFa4Fwd.Proof2.Softmax.ShapeTcWait
public import Kernels.TmlFa4Fwd.Proof2.Softmax.ShapeBld

@[expose] public section

/-! # The softmax warps' shape table at every state

`shape`: every event a state of the softmax machine fires has the state's shape (`Ev`), from the
families of `Shape*.lean` (each by `site_shape`, no override) and the states the invariant
excludes (`shapeAt_junk`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem shapeAt (hp : Pre p L m) (d : D) : (code p L g).ShapeAt (Ev p L g) d := by
  by_cases hb : ∃ b c, d.site = .bld b c
  · exact shapeAt_bld hp d hb
  by_cases hw : (∃ c, d.site = .sldw c) ∨ d.site = .pst .first 0 ∨ d.site = .pst .bias 0
  · by_cases h1 : d.k = 1
    · exact shapeAt_tc1 hp d h1 hw
    by_cases h0 : d.k = 0
    · refine shapeAt_tc0 hp d h0 ?_
      rcases hw with ⟨c, h⟩ | h | h
      · exact .inr (.inl ⟨c, h⟩)
      · exact .inr (.inr ⟨_, _, h⟩)
      · exact .inr (.inr ⟨_, _, h⟩)
    refine shapeAt_junk ?_
    rintro (⟨h, -, -⟩ | h)
    · exact h0 h
    · obtain ⟨s, v, k, acc⟩ := d
      rcases hw with ⟨c, rfl⟩ | rfl | rfl <;> simp_all [Site.midOk]
  by_cases hk : d.k = 0
  swap
  · refine shapeAt_junk ?_
    rintro (⟨h, -, -⟩ | h)
    · exact hk h
    · obtain ⟨s, v, k, acc⟩ := d
      cases s <;> simp_all [Site.midOk]
  obtain ⟨s, v, k, acc⟩ := d
  simp only at hk
  subst hk
  cases s with
  | word k | down k | total k => exact shapeAt_scan hp _ rfl k (by simp)
  | up k j => exact shapeAt_scan hp _ rfl k (by simp)
  | vote l | pre l | tiles l => exact shapeAt_scan hp _ rfl .first (by simp)
  | sld _ _ | pst _ _ => exact shapeAt_tc0 hp _ rfl (by simp)
  | sldw _ => exact absurd (.inl ⟨_, rfl⟩) hw
  | bld _ _ => exact absurd ⟨_, _, rfl⟩ hb
  | _ => exact shapeAt_ctl hp _ rfl (by simp)

/-- **Every event a state of the softmax machine fires has the state's shape.** -/
theorem shape (hp : Pre p L m) : (code p L g).Shape (Ev p L g) :=
  Code.Shape.of_at (shapeAt hp)

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
