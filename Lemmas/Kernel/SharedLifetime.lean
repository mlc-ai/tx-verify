-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Execution
public import Lemmas.Order.StageCausalityThread
public import Lemmas.Async.AsyncMBarrier

@[expose] public section

/-! Building lifetime evidence (ERR-SHARED-LIFETIME): base causality paths, enabling paths
with one object's order, and the completion of an asynchronous stage observed by a wait. -/

namespace PTX

section
variable {L : Launch} {K : Kernel} {A : List Assumption} {X : Execution}

/-- Enabling together with the order of one object (and the assumed commit order). -/
abbrev EnablesWith (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution)
    (o : OrderObject) : AsyncCopy.Ref × Bool → AsyncCopy.Ref × Bool → Prop :=
  LifetimeStep L K A X o

/-- A dependency path is a lifetime step with any object's order. -/
theorem EnablesWith.of_enables {o : OrderObject} {a c : AsyncCopy.Ref × Bool}
    (h : Relation.TransGen (DepStep L K X) a c) :
    Relation.TransGen (EnablesWith L K A X o) a c :=
  Relation.TransGen.mono (fun _ _ => Or.inl) _ _ h

/-- Base causality orders the return of `i` before the issue of `j`. -/
theorem LifetimeOrder.of_baseCausality {i j : EvId} (h : baseCausality L X i j) :
    LifetimeOrder L K A X (.thread i, true) (.thread j, false) :=
  .inl (.single (stageCausality.of_baseCausality h))

/-- An instruction's completion before a node, by base causality. -/
theorem CompletedBefore.of_baseCausality {i j : EvId} (h : baseCausality L X i j) :
    CompletedBefore L K A X (.thread i) (.thread j, false) :=
  .inl (LifetimeOrder.of_baseCausality h)

/-- A dependency path from the return of a wait whose mbarrier history records `x` before it. -/
theorem CompletedBefore.of_before {m : Loc} {x : AsyncCopy.Ref} {w : EvId}
    {n : AsyncCopy.Ref × Bool} (hb : MBarrier.Before (X.objects m) x (.thread w))
    (h : Relation.TransGen (DepStep L K X) (.thread w, true) n) :
    CompletedBefore L K A X x n :=
  .inl (.inr ⟨.mbar m, trivial, .head (Or.inr (Or.inl ⟨rfl, rfl, hb⟩))
    (EnablesWith.of_enables h)⟩)

/-- A dependency path from the return of a wait that the completion of an asynchronous stage is a
witness of. -/
theorem CompletedBefore.of_observed {i : EvId} {p : AsyncCopy.Part} {w : EvId}
    {n : AsyncCopy.Ref × Bool} (ho : Witness L X (.async i p) w)
    (h : Relation.TransGen (DepStep L K X) (.thread w, true) n) :
    CompletedBefore L K A X (.async i p) n :=
  .inr ⟨i, p, w, .mbar ⟨.shared, 0, 0⟩, rfl, ho, trivial, EnablesWith.of_enables h⟩

/-- The completion of a stage precedes whatever the completion of its next stage precedes. -/
theorem CompletedBefore.of_stage {i j : EvId} {p q : AsyncCopy.Part} {n : AsyncCopy.Ref × Bool}
    (h : CompletedBefore L K A X (.async j q) n) (hq : X.RefPresent (.async j q))
    (hs : StageOrder X (.async i p, true) (.async j q, false)) :
    CompletedBefore L K A X (.async i p) n := by
  have hc1 : stageCausality L X (.async i p, true) (.async j q, false) := .inl hs
  have hc2 : stageCausality L X (.async j q, false) (.async j q, true) :=
    .inl (.inl ⟨rfl, rfl, rfl, hq⟩)
  rcases h with (h | ⟨o, ho, h⟩) | ⟨j', q', w, o, he, hobs, ho, h⟩
  · exact .inl (.inl (.head hc1 (.head hc2 h)))
  · exact .inl (.inr ⟨o, ho,
      .head (Or.inl (DepStep.stage hs)) (.head (Or.inl (DepStep.node (L := L) hq)) h)⟩)
  · exact .inl (.inr ⟨o, ho, .head (Or.inl (DepStep.stage hs))
      (.head (Or.inl (DepStep.of_witness (L := L) hobs)) h)⟩)

/-- An MMA observed through its commit's notification completed before every event the
observing wait enables. -/
theorem CompletedBefore.of_observesMma (hc : AsyncCopy.CommitOk X) {i w : EvId} {acq : Bool}
    {ws : MbarScope} {n : AsyncCopy.Ref × Bool} (h : AsyncCopy.AsyncObserved X i .mmaDone w acq ws)
    (hen : Relation.TransGen (DepStep L K X) (.thread w, true) n) :
    X.async.mmaDone i = true ∧ CompletedBefore L K A X (.async i .mmaDone) n := by
  obtain ⟨c, _, rank, m, htrack, _, _, hn, hwo⟩ := h.mma
  have hd := (hc c rank hn).2 i htrack
  have hnp : X.AsyncPresent c (.tcNotify rank) := hn
  refine ⟨hd, CompletedBefore.of_stage (L := L) (K := K) (A := A)
    (CompletedBefore.of_before hwo.before hen) hnp ?_⟩
  exact .inr ⟨rfl, rfl, htrack, hd, hnp⟩


/-- An instruction other than an exit, of a thread of CTA `c`, completes before that thread's
exit once the CTA has exited. -/
theorem SharedFinished.of_thread (hout : ∀ g, L.threads ≤ g → X.tr g = []) {e : EvId}
    {ev : Event} {c : Nat} (he : X.get e = some ev) (hne : ∀ pc, ev ≠ ⟨pc, .exit⟩)
    (hc : e.1 / L.block = c) (hx : CtaExited L X c) :
    SharedFinished L K A X (.thread e) c := by
  have hg : e.1 < L.threads := by
    by_contra h
    simp [Execution.get, hout e.1 (by omega)] at he
  obtain ⟨pc, hl⟩ := hx e.1 hg hc
  have hlen : e.2 < (X.tr e.1).length := by
    simp only [Execution.get] at he
    exact (List.getElem?_eq_some_iff.mp he).1
  have hlast : (X.tr e.1)[(X.tr e.1).length - 1]? = some ⟨pc, .exit⟩ := by
    rw [List.getLast?_eq_getElem?] at hl; exact hl
  have hlt : e.2 < (X.tr e.1).length - 1 := by
    rcases Nat.lt_or_ge e.2 ((X.tr e.1).length - 1) with h | h
    · exact h
    · have heq : e.2 = (X.tr e.1).length - 1 := by omega
      simp only [Execution.get] at he
      rw [heq, hlast] at he
      cases he
      exact absurd rfl (hne pc)
  refine ⟨⟨ev, he⟩, (e.1, (X.tr e.1).length - 1), pc, hg, hc, hlast, ?_⟩
  refine CompletedBefore.of_baseCausality (.single (Or.inl ⟨rfl, hlt, by simp; omega, ?_⟩))
  rintro ⟨hs, -⟩
  simp [Execution.get, hlast, Event.acc] at hs

/-- A memory access of a thread of CTA `c` completes before that thread's exit once the CTA has
exited. -/
theorem SharedFinished.of_access (hout : ∀ g, L.threads ≤ g → X.tr g = []) {e : EvId} {a : Acc}
    {w : Bool} {c : Nat} (ha : X.Access e a w) (hc : e.1 / L.block = c) (hx : CtaExited L X c) :
    SharedFinished L K A X (.thread e) c := by
  rcases ha with ⟨bs, ⟨pc, he⟩, -⟩ | ⟨bs, ⟨pc, he⟩, -⟩ | ⟨old, new, pc, he⟩
  · exact SharedFinished.of_thread hout he (fun _ h => by cases h) hc hx
  · exact SharedFinished.of_thread hout he (fun _ h => by cases h) hc hx
  · exact SharedFinished.of_thread hout he (fun _ h => by cases h) hc hx

/-- A performed stage completes before whatever the completion of its operation's next stage
precedes. -/
theorem SharedFinished.of_stage {i j : EvId} {p q : AsyncCopy.Part} {c : Nat}
    (hp : X.RefPresent (.async i p)) (hs : StageOrder X (.async i p, true) (.async j q, false))
    (h : SharedFinished L K A X (.async j q) c) : SharedFinished L K A X (.async i p) c := by
  obtain ⟨hq, finish, pc, hf, hc, hget, hb⟩ := h
  exact ⟨hp, finish, pc, hf, hc, hget, CompletedBefore.of_stage (L := L) (K := K) (A := A) hb hq hs⟩


/-- The release complete-tx of a copy observed by an acquire wait completes before the wait's
program-order successor. -/
theorem CompletedBefore.of_copyRelease {i w f : EvId} {p : AsyncCopy.Part} {ws : MbarScope}
    (hp : p = .notify .copy ∨ p = .notify .load) (ho : AsyncCopy.AsyncObserved X i p w true ws)
    (hs : ScopesMeet L .cluster i.1 ws w.1) (hpo : po X w f) :
    CompletedBefore L K A X (.async i p) (.thread f, false) :=
  .inl (.inl (.single (.inr (.inr ⟨rfl, rfl, f, rfl, i, p, w, ws, rfl, hp, ho, hs, hpo⟩))))

/-- A thread instruction acting on an mbarrier object is an instruction other than an exit. -/
theorem objectAction_thread {S : AsyncCopy.Snapshot} {m : Loc} {i : EvId} {act : MBarrier.Action}
    (h : AsyncCopy.objectAction X S m (.thread i) = some act) :
    ∃ ev, X.get i = some ev ∧ ∀ pc, ev ≠ ⟨pc, .exit⟩ := by
  unfold AsyncCopy.objectAction at h
  cases he : X.get i with
  | none => simp [he] at h
  | some ev =>
    refine ⟨ev, rfl, ?_⟩
    rintro pc rfl
    simp [he] at h

end

end PTX
