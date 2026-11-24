-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Frame
public import Kernels.TmlFa4Fwd.Proof.Startup.Shape
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The startup makes no warp-collective `tcgen05` event -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

/-- A startup event before the role's entry is no warp-collective `tcgen05` event. -/
theorem start_not_tcColl {L : Launch} {g : Nat} {s : Startup.D} {e : Event}
    (hx : exit L g s = none) (hev : Startup.Ev L g s e) : isTcColl e ≠ true := by
  intro hcl
  obtain ⟨site, x1, x2, x3⟩ := s
  obtain ⟨pc, kd⟩ := e
  cases site with
  | sh j =>
    fin_cases j <;> simp only [Startup.Ev] at hev <;> obtain ⟨_, _, hk⟩ := hev <;>
      subst hk <;> cases hcl
  | elect j =>
    simp only [Startup.Ev] at hev
    rcases hev with ⟨_, _, -, hk⟩ | ⟨f, hk⟩ <;> subst hk <;> cases hcl
  | init q =>
    simp only [Startup.Ev] at hev
    rcases hev with ⟨_, _, hk⟩ | ⟨f, hk⟩ <;> subst hk <;> cases hcl
  | fence => simp only [Startup.Ev] at hev; subst hev; cases hcl
  | bar => simp only [Startup.Ev] at hev; subst hev; cases hcl
  | enter r => simp [exit] at hx

end PTX.Kernels.TmlFa4Fwd.Proof
