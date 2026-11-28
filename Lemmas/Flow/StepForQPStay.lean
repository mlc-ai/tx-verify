-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.StepForQPGlue
import Lemmas.Execution.EventFrameSource

@[expose] public section

/-! # The strict step with a fact of the next state, from the first fragment of a glue

`glue_inl_stepForQP` (with the hand-off, as `glue_inl_stepForQ`) and `glue_inl_stepForQP_stay` (a
step that never reaches the exit, as `glue_inl_stepForQ_stay`) for `StepForQP`. -/

namespace PTX.Flow.Code
open PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {P : Code K A L g}
  {ι : Type} {R : ι → Code K A L g} {exit : P.D → Option ι}

theorem glue_inl_stepForQP {Q Pu : TState → Prop} {Wf : Event → Prop} {d : P.D} {e : Event}
    (hP : exit d = none → P.StepForQP Q Pu Wf d e) (hglue : Handoff P R exit) :
    (glue P R exit).StepForQP Q Pu Wf (.inl d) e := by
  intro t u ins hat hinv hc hq hw hf hp
  rcases hP hinv.2 ins hat hinv.1 hc hq hw hf hp with ⟨d', t', hn, hl, hg, hq'⟩ | ⟨hn, hd⟩
  · exact .inl ⟨enter P R exit d', t', by show (P.next d e).map _ = _; rw [hn]; rfl, hl,
      good_enter hglue hg, hq'⟩
  · exact .inr ⟨by show (P.next d e).map _ = _; rw [hn]; rfl, hd⟩

theorem glue_inl_stepForQP_stay {Q Pu : TState → Prop} {Wf : Event → Prop} {d : P.D}
    {e : Event} (hP : exit d = none → P.StepForQP Q Pu Wf d e)
    (hstay : Wf e → e.pc = P.pc d → ∀ d', P.next d e = some (some d') → exit d' = none) :
    (glue P R exit).StepForQP Q Pu Wf (.inl d) e := by
  intro t u ins hat hinv hc hq hw hf hp
  rcases hP hinv.2 ins hat hinv.1 hc hq hw hf hp with ⟨d', t', hn, hl, hg, hq'⟩ | ⟨hn, hd⟩
  · have hx := hstay hw (EventFrame.fires_source_pc hf) d' hn
    refine .inl ⟨enter P R exit d', t', by show (P.next d e).map _ = _; rw [hn]; rfl, hl, ?_, hq'⟩
    rw [enter_none hx]
    exact ⟨hg.1, hg.2, hx⟩
  · exact .inr ⟨by show (P.next d e).map _ = _; rw [hn]; rfl, hd⟩

end

end PTX.Flow.Code
