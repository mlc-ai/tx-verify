-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Lemmas.Kernel.Frame
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The step into a role state

`prev_role`: a state one event after a lane's state, if it is a role state that is not the role
fragment's first state, came from a role state. The step is a startup step (`Code.enter`), and the
entered role state is the fragment's first state. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The step into a role state other than its first**: the previous state is a role state. -/
theorem prev_role {h k : Nat} {e : Event} {i : Role} {d : (frag p L h i).D} {n : Cls → Nat}
    (he : (X.tr h)[k]? = some e)
    (hσ : Frame.stateAt (thread p L) X h (k + 1) = some (some (.inr ⟨i, d⟩, n)))
    (hs : d ≠ (frag p L h i).init) :
    ∃ r n0, Frame.stateAt (thread p L) X h k = some (some (.inr r, n0)) := by
  rw [Frame.stateAt_succ he] at hσ
  cases hσ0 : Frame.stateAt (thread p L) X h k with
  | none => rw [hσ0] at hσ; simp at hσ
  | some o =>
    cases o with
    | none => rw [hσ0] at hσ; simp [Code.toMachine] at hσ
    | some σ =>
      rw [hσ0] at hσ
      obtain ⟨σ0, n0⟩ := σ
      rcases σ0 with s0 | r0
      swap
      · exact ⟨r0, n0, rfl⟩
      change (thread p L h).next (.inl s0, n0) e = some (some (.inr ⟨i, d⟩, n)) at hσ
      obtain ⟨h1, -⟩ := Code.counted_next_some (C := glued p L h) hσ
      simp only [glued, Code.glue] at h1
      cases hsu : Startup.succ L h s0 e with
      | none => simp [Startup.code, hsu] at h1
      | some o' =>
        cases o' with
        | none => simp [Startup.code, hsu] at h1
        | some s' =>
          simp only [Startup.code, hsu, Option.map_some, Option.some.injEq] at h1
          unfold Code.enter at h1
          split at h1
          · rename_i r hx
            simp only [Option.some.injEq, Sum.inr.injEq] at h1
            obtain ⟨hr, hd⟩ := Sigma.mk.inj_iff.mp h1
            subst hr
            exact absurd (eq_of_heq hd).symm hs
          · simp at h1

end
end PTX.Kernels.TmlFa4Fwd.Proof
