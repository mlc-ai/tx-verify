-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.Machine

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX

/-- The site is still on the entry side of the last commit. -/
def Site.beforeFinal : Site → Bool
  | .bar1 | .setMaxRegInc | .dispatch => false
  | _ => true

private theorem iter_before (d : D) : (iterNext d).site.beforeFinal = true := by
  unfold iterNext
  split <;> first | rfl | (split <;> rfl)

private theorem qk_before (d : D) : (afterQk d).site.beforeFinal = true := by
  unfold afterQk
  split <;> first | exact iter_before _ | rfl

theorem stays_before {L g d e d'} (hz : next L g d e = some (some d'))
    (live : d.site.beforeFinal = true) (nf : d.site ≠ .finCommit)
    (elect : ∀ m i ld, e.kind = .elect m i ld → ld = laneOf L g) : d'.site.beforeFinal = true := by
  obtain ⟨s,i,v⟩ := d
  cases s <;> try contradiction
  all_goals simp only [next] at hz
  all_goals repeat' split at hz
  all_goals try contradiction
  all_goals try (rename_i bs he; cases hv : (rebuild 3 bs).toOption <;>
    simp [hv] at hz; subst d'; rfl)
  all_goals try (obtain rfl := Option.some.inj (Option.some.inj hz))
  all_goals first
    | rfl
    | exact iter_before _
    | exact qk_before _
    | (simp only [issueNext]; split <;> rfl)
    | (simp only [startSite]; split <;> rfl)
    | (rename_i hn; exact False.elim (hn ((elect _ _ _ (by assumption)).symm)))

end PTX.Kernels.InklingRelDecode.Proof.Mma
