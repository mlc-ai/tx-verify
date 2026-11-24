-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Kernels.TmlFa4Fwd.Proof.Startup.Shape
public import Lemmas.Kernel.Safety.Classes
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The startup names an mbarrier by an initialization only -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The startup names an mbarrier only by an initialization. -/
theorem start_mbar {s : Startup.D} {e : Event} {l : Loc} (hev : Startup.Ev L g s e)
    (hx : exit L g s = none) (hm : MbarOf e l) : ∃ c, e.kind = .mbInit l c := by
  obtain ⟨site, x1, x2, x3⟩ := s
  obtain ⟨pc, kind⟩ := e
  cases site with
  | sh j =>
    fin_cases j <;> simp only [Startup.Ev] at hev <;> obtain ⟨r, ok, hk⟩ := hev <;>
      (try simp only at hk) <;> subst hk <;> simp [MbarOf] at hm
  | elect j =>
    simp only [Startup.Ev] at hev
    rcases hev with ⟨_, _, _, hk⟩ | ⟨f, hk⟩ <;> (try simp only at hk) <;> subst hk <;>
      simp [MbarOf] at hm
  | init q =>
    simp only [Startup.Ev] at hev
    rcases hev with ⟨l', c, hk⟩ | ⟨f, hk⟩ <;> (try simp only at hk) <;> subst hk
    · simp only [MbarOf] at hm
      exact ⟨c, by rw [hm]⟩
    · simp [MbarOf] at hm
  | fence =>
    simp only [Startup.Ev] at hev
    subst hev
    simp [MbarOf] at hm
  | bar =>
    simp only [Startup.Ev] at hev
    subst hev
    simp [MbarOf] at hm
  | enter r => simp [exit] at hx

end
end PTX.Kernels.TmlFa4Fwd.Proof
