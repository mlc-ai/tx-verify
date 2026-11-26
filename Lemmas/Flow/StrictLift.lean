-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.StrictWindow
public import Lemmas.Flow.LoopGlue

@[expose] public section

/-! # The strict step of one state for one event, through the glue

`Code.StepFor` (`Lemmas/Flow/StrictWindow.lean`) of a state of a counted, glued or loop-glued
machine, from the strict step of the state it is built from, for the same event
(`counted_stepFor`, `glue_inl_stepFor`, `glue_inr_stepFor`, `loopGlue_inl_stepFor`,
`loopGlue_inr_stepFor`). The proofs are those of `counted_steps`, `glue_steps` and
`loopGlue_steps`, at one state and one event. -/

namespace PTX.Flow.Code
open PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat}

theorem counted_stepFor {C : Code K A L g} {κ : Type} {cls : κ → Event → Bool} {d : C.D}
    {e : Event} (h : C.StepFor d e) (n : κ → Nat) : (C.counted cls).StepFor (d, n) e := by
  intro t u ins hat hinv hc hf
  rcases h ins hat hinv hc hf with (hn | ⟨d', t', hn, hl, hg⟩) | ⟨hn, hd⟩
  · exact .inl (.inl (by rw [counted_next, hn]; rfl))
  · exact .inl (.inr ⟨(d', bump cls n e), t', by rw [counted_next, hn]; rfl, hl, hg⟩)
  · exact .inr ⟨by rw [counted_next, hn]; rfl, hd⟩

variable {P : Code K A L g} {ι : Type} {R : ι → Code K A L g} {exit : P.D → Option ι}

theorem glue_inl_stepFor {d : P.D} {e : Event} (hP : exit d = none → P.StepFor d e)
    (hglue : Handoff P R exit) : (glue P R exit).StepFor (.inl d) e := by
  intro t u ins hat hinv hc hf
  rcases hP hinv.2 ins hat hinv.1 hc hf with (hn | ⟨d', t', hn, hl, hg⟩) | ⟨hn, hd⟩
  · exact .inl (.inl (by show (P.next d e).map _ = _; rw [hn]; rfl))
  · exact .inl (.inr ⟨enter P R exit d', t', by show (P.next d e).map _ = _; rw [hn]; rfl,
      hl, good_enter hglue hg⟩)
  · exact .inr ⟨by show (P.next d e).map _ = _; rw [hn]; rfl, hd⟩

theorem glue_inr_stepFor {i : ι} {d : (R i).D} {e : Event} (h : (R i).StepFor d e) :
    (glue P R exit).StepFor (.inr ⟨i, d⟩) e := by
  intro t u ins hat hinv hc hf
  rcases h ins hat hinv hc hf with (hn | ⟨d', t', hn, hl, hg⟩) | ⟨hn, hd⟩
  · exact .inl (.inl (by show ((R i).next d e).map _ = _; rw [hn]; rfl))
  · exact .inl (.inr ⟨.inr ⟨i, d'⟩, t', by show ((R i).next d e).map _ = _; rw [hn]; rfl,
      hl, hg⟩)
  · exact .inr ⟨by show ((R i).next d e).map _ = _; rw [hn]; rfl, hd⟩

variable {back : (i : ι) → (R i).D → Option P.D}

theorem loopGlue_inl_stepFor {d : P.D} {e : Event} (hP : exit d = none → P.StepFor d e)
    (hglue : Handoff P R exit) (hinit : ∀ i, back i (R i).init = none) :
    (loopGlue P R exit back).StepFor (.inl d) e := by
  intro t u ins hat hinv hc hf
  rcases hP hinv.2 ins hat hinv.1 hc hf with (hn | ⟨d', t', hn, hl, hg⟩) | ⟨hn, hd⟩
  · exact .inl (.inl (by show (P.next d e).map _ = _; rw [hn]; rfl))
  · exact .inl (.inr ⟨enter P R exit d', t', by show (P.next d e).map _ = _; rw [hn]; rfl,
      hl, good_enter_loop hglue hinit hg⟩)
  · exact .inr ⟨by show (P.next d e).map _ = _; rw [hn]; rfl, hd⟩

theorem loopGlue_inr_stepFor {i : ι} {d : (R i).D} {e : Event}
    (hR : back i d = none → (R i).StepFor d e) (hglue : Handoff P R exit)
    (hback : Back P R back) (hinit : ∀ i, back i (R i).init = none) :
    (loopGlue P R exit back).StepFor (.inr ⟨i, d⟩) e := by
  intro t u ins hat hinv hc hf
  rcases hR hinv.2 ins hat hinv.1 hc hf with (hn | ⟨d', t', hn, hl, hg⟩) | ⟨hn, hd⟩
  · exact .inl (.inl (by show ((R i).next d e).map _ = _; rw [hn]; rfl))
  · exact .inl (.inr ⟨backEnter P R exit back i d', t',
      by show ((R i).next d e).map _ = _; rw [hn]; rfl, hl,
      good_backEnter hglue hback hinit hg⟩)
  · exact .inr ⟨by show ((R i).next d e).map _ = _; rw [hn]; rfl, hd⟩

end
end PTX.Flow.Code
