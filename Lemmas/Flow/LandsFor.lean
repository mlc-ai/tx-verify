-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.StrictWindow

@[expose] public section

namespace PTX.Flow.Code
open PTX.Proof

variable {K : Kernel} {A : List Assumption} {L : Launch} {g : Nat} {C : Code K A L g}

/-- A strict segment into a state's facts lands strictly good. -/
theorem landsFor {d : C.D} {u : TState} {a n : Nat} {F : List (Nat × Value)}
    (hu : At u a F) (hl : Seg K A L g n a F (C.pc d) (C.facts d)) (hi : C.inv d)
    (hs : C.sub d = 0) (ha : C.acc d = []) :
    ∃ s, Relation.ReflTransGen (Tau K A L g) u s ∧ C.Good (some d) s := by
  obtain ⟨s, hr, hp, hsub, hacc, hf, hF⟩ := hl u hu
  exact ⟨s, run_rtg hr, ⟨hp, hsub.trans hs.symm, hacc.trans ha.symm, hf, hF⟩, hi⟩

end PTX.Flow.Code
