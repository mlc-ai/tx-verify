-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.StepForQ
public import Lemmas.Flow.StepForQPcP

@[expose] public section

/-! # The strict step with a fact of the next state, through the glue and the counters

`Code.counted_stepForQP` and `Code.glue_inr_stepForQP` carry `StepForQP` from a sub-machine to
`Code.counted` and `Code.glue`, as `counted_stepForQ` and `glue_inr_stepForQ` do for `StepForQ`. -/

namespace PTX.Flow.Code
open PTX.Proof

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}
  {P : Code K A L g} {ι : Type} {R : ι → Code K A L g} {exit : P.D → Option ι}

theorem counted_stepForQP {κ : Type} {cls : κ → Event → Bool} {Q Pu : TState → Prop}
    {Wf : Event → Prop} {d : C.D} {e : Event} (h : C.StepForQP Q Pu Wf d e) (n : κ → Nat) :
    (C.counted cls).StepForQP Q Pu Wf (d, n) e := by
  intro t u ins hat hinv hc hq hw hf hp
  rcases h ins hat hinv hc hq hw hf hp with ⟨d', t', hn, hl, hg, hq'⟩ | ⟨hn, hd⟩
  · exact .inl ⟨(d', bump cls n e), t', by rw [counted_next, hn]; rfl, hl, hg, hq'⟩
  · exact .inr ⟨by rw [counted_next, hn]; rfl, hd⟩

theorem glue_inr_stepForQP {Q Pu : TState → Prop} {Wf : Event → Prop} {i : ι} {d : (R i).D}
    {e : Event} (h : (R i).StepForQP Q Pu Wf d e) :
    (glue P R exit).StepForQP Q Pu Wf (.inr ⟨i, d⟩) e := by
  intro t u ins hat hinv hc hq hw hf hp
  rcases h ins hat hinv hc hq hw hf hp with ⟨d', t', hn, hl, hg, hq'⟩ | ⟨hn, hd⟩
  · exact .inl ⟨.inr ⟨i, d'⟩, t', by show ((R i).next d e).map _ = _; rw [hn]; rfl, hl, hg, hq'⟩
  · exact .inr ⟨by show ((R i).next d e).map _ = _; rw [hn]; rfl, hd⟩

end PTX.Flow.Code
