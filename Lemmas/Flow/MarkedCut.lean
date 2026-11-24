-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.WarpUniform

@[expose] public section

namespace PTX
open PTX.Flow PTX.EventFrame

/-- Cut an actual walk before a witnessed later event. The saved prefix contains exactly the
marked events described by the remaining-count rank, with a property of every event in the cut. -/
theorem Walk.cut_marked_where {K : Kernel} {A : List Assumption} {l : Launch} {g : Nat}
    {s : TState} {events : List Event} {visits : List Visit}
    (hw : Walk K A l g s events visits)
    {P cut : TState → Prop} {good : Event → Prop} (remaining : TState → Nat) (mark : Event → Bool)
    (hZero : ∀ t, P t → cut t → remaining t = 0)
    (hStep : ∀ {t u event}, P t → ¬ cut t → WStep K A l g t event u →
      P u ∧ remaining t = event.toList.countP mark + remaining u)
    (hGood : ∀ {t u e}, P t → ¬ cut t → EStep K A l g t e (some u) → good e)
    (hs : P s) {target : Event} (hFound : target ∈ events)
    (hLater : ∀ t, P t → ¬ cut t → t.pc ≠ target.pc) :
    ∃ u before rest tail, events = before ++ rest ∧ target ∈ rest ∧ P u ∧ cut u ∧
      before.countP mark = remaining s ∧ (∀ e ∈ before, good e) ∧
      Walk K A l g u rest tail := by
  classical
  induction hw with
  | stop => cases hFound
  | @tau t u es vs ht hw ih =>
    by_cases hc : cut t
    · exact ⟨t, [], es, _, rfl, hFound, hs, hc, (hZero t hs hc).symm, by simp, .tau ht hw⟩
    obtain ⟨hu, hEq⟩ := hStep hs hc (.inl ⟨rfl, ht⟩)
    obtain ⟨v, before, rest, tail, hEs, hMem, hv, hcut, hCount, hWords, hWalk⟩ := ih hu hFound
    exact ⟨v, before, rest, tail, hEs, hMem, hv, hcut, hCount.trans (by simpa using hEq.symm),
      hWords,hWalk⟩
  | @ev t u e es vs he hw ih =>
    by_cases hc : cut t
    · exact ⟨t, [], e::es, _, rfl, hFound, hs, hc, (hZero t hs hc).symm, by simp, .ev he hw⟩
    have hNe : target ≠ e := by
      intro h
      exact hLater t hs hc ((estep_source_pc he).symm.trans (congrArg Event.pc h.symm))
    have hTail := (List.mem_cons.mp hFound).resolve_left hNe
    obtain ⟨hu, hEq⟩ := hStep hs hc (.inr ⟨e, rfl, he⟩)
    obtain ⟨v, before, rest, tail, hEs, hMem, hv, hcut, hCount, hWords, hWalk⟩ := ih hu hTail
    refine ⟨v, e::before, rest, tail, by rw [hEs]; rfl, hMem, hv, hcut, ?_, ?_, hWalk⟩
    · simpa [List.countP_cons, hCount, Nat.add_comm] using hEq.symm
    · intro f hf
      rcases List.mem_cons.mp hf with rfl | hIn
      · exact hGood hs hc he
      · exact hWords f hIn
  | @last t e he =>
    by_cases hc : cut t
    · exact ⟨t, [], [e], _, rfl, hFound, hs, hc, (hZero t hs hc).symm, by simp, .last he⟩
    obtain rfl := List.mem_singleton.mp hFound
    exact (hLater t hs hc (estep_source_pc he).symm).elim


/-- Cut an actual walk before a witnessed later event. The saved prefix contains exactly the
marked events described by the remaining-count rank. Local steps contribute no mark. -/
theorem Walk.cut_marked {K : Kernel} {A : List Assumption} {l : Launch} {g : Nat}
    {s : TState} {events : List Event} {visits : List Visit}
    (hw : Walk K A l g s events visits)
    {P cut : TState → Prop} (remaining : TState → Nat) (mark : Event → Bool)
    (hZero : ∀ t, P t → cut t → remaining t = 0)
    (hStep : ∀ {t u event}, P t → ¬ cut t → WStep K A l g t event u →
      P u ∧ remaining t = event.toList.countP mark + remaining u)
    (hs : P s) {target : Event} (hFound : target ∈ events)
    (hLater : ∀ t, P t → ¬ cut t → t.pc ≠ target.pc) :
    ∃ u before rest tail, events = before ++ rest ∧ target ∈ rest ∧ P u ∧ cut u ∧
      before.countP mark = remaining s ∧ Walk K A l g u rest tail := by
  obtain ⟨u, before, rest, tail, hEs, hMem, hu, hcut, hCount, _, hWalk⟩ :=
    hw.cut_marked_where (good := fun _ => True) remaining mark hZero hStep
      (fun _ _ _ => trivial) hs hFound hLater
  exact ⟨u, before, rest, tail, hEs, hMem, hu, hcut, hCount, hWalk⟩

end PTX
