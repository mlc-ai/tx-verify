-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.StepForQ
import Lemmas.Execution.EventFrameSource

@[expose] public section

/-! # A glued strict step that never reaches the exit

`glue_inl_stepForQ` needs the hand-off of the first fragment to its roles. A step of the first
fragment that stays below the exit needs none: its successor is a state of the first fragment. -/

namespace PTX.Flow.Code
open PTX.Proof

noncomputable section

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {P : Code K A L g}
  {ι : Type} {R : ι → Code K A L g} {exit : P.D → Option ι}

theorem glue_inl_stepForQ_stay {Q : TState → Prop} {Wf : Event → Prop} {d : P.D} {e : Event}
    (hP : exit d = none → P.StepForQ Q Wf d e)
    (hstay : Wf e → e.pc = P.pc d → ∀ d', P.next d e = some (some d') → exit d' = none) :
    (glue P R exit).StepForQ Q Wf (.inl d) e := by
  intro t u ins hat hinv hc hq hw hf
  rcases hP hinv.2 ins hat hinv.1 hc hq hw hf with ⟨d', t', hn, hl, hg, hq'⟩ | ⟨hn, hd⟩
  · have hx := hstay hw (EventFrame.fires_source_pc hf) d' hn
    refine .inl ⟨enter P R exit d', t', by show (P.next d e).map _ = _; rw [hn]; rfl, hl, ?_, hq'⟩
    rw [enter_none hx]
    exact ⟨hg.1, hg.2, hx⟩
  · exact .inr ⟨by show (P.next d e).map _ = _; rw [hn]; rfl, hd⟩

end

end PTX.Flow.Code
