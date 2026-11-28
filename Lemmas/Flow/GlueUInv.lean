-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.GlueU

@[expose] public section

/-! # The step obligation of a role from that of the glued machine

`glue_stepsU` builds the glued machine's obligations from its fragments'. Conversely, the glued
machine's obligation at a state of a role is the role's: the facts, the invariant and the successor
are the role's (the successor wrapped by the role's index). -/

namespace PTX.Flow.Code
open PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {P : Code K A L g} {ι : Type}
  {R : ι → Code K A L g} {exit : P.D → Option ι}

theorem glue_inr_stepAtU {i : ι} {d : (R i).D} (h : (glue P R exit).StepAtU (.inr ⟨i, d⟩)) :
    (R i).StepAtU d := by
  refine ⟨h.site, ?_⟩
  intro t e u ins hat hinv hc hf
  rcases h.step ins hat hinv hc hf with (hn | ⟨d', t', hn, hl, hg⟩) | ⟨hn, hd⟩
  · left; left
    change ((R i).next d e).map _ = _ at hn
    rcases hr : (R i).next d e with _ | _ | x <;> rw [hr] at hn <;> simp at hn
  · left; right
    change ((R i).next d e).map _ = _ at hn
    rcases hr : (R i).next d e with _ | _ | x <;> rw [hr] at hn <;> simp at hn
    obtain rfl := hn
    exact ⟨x, t', rfl, hl, hg⟩
  · right
    change ((R i).next d e).map _ = _ at hn
    rcases hr : (R i).next d e with _ | _ | x <;> rw [hr] at hn <;> simp at hn
    exact ⟨rfl, hd⟩

end

end PTX.Flow.Code
