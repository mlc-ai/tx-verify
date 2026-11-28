-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.Machine

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX

def Site.won : Site → Bool
  | .qk _ | .qkCommit | .pv _ | .pvCommit1 | .pvCommit2 | .finCommit => true
  | _ => false

private theorem iter_not_won (d : D) : (iterNext d).site.won = false := by
  simp only [iterNext]
  split <;> first | rfl | (split <;> rfl)

private theorem after_not_won (d : D) : (afterQk d).site.won = false := by
  unfold afterQk
  split <;> first | exact iter_not_won _ | rfl

/-- Before the first winner-only instruction there is a successful election. Later
instructions of the same QK/PV family retain that witness. -/
theorem predecessor_won {L g d e d'} (hz : next L g d e = some (some d'))
    (hw : d'.site.won = true) :
    d.site.won = true ∨ ∃ mask inst, e.kind = .elect mask inst (laneOf L g) := by
  obtain ⟨s,i,v⟩ := d
  cases s
  all_goals try exact .inl rfl
  all_goals simp only [next] at hz
  all_goals repeat' split at hz
  all_goals try contradiction
  all_goals try (rename_i bs he; cases hv : (rebuild 3 bs).toOption <;>
    simp [hv] at hz; subst d'; cases hw)
  all_goals try (cases hz; done)
  all_goals try (obtain rfl := Option.some.inj (Option.some.inj hz))
  all_goals first
    | exact Or.inr (by rename_i h; rw [h]; exact ⟨_,_,by assumption⟩)
    | contradiction
    | exact (Bool.noConfusion ((iter_not_won _).symm.trans hw))
    | exact (Bool.noConfusion ((after_not_won _).symm.trans hw))
    | (simp only [startSite] at hw; split at hw <;> cases hw)

end PTX.Kernels.InklingRelDecode.Proof.Mma
