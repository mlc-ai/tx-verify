-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.SharedLifetime

@[expose] public section

/-! # Exit coverage without an exit cluster barrier

A proof tool for ERR-SHARED-LIFETIME (`SharedLifetimeUnsafe`) in a kernel whose CTAs do not meet
at a cluster barrier before they exit. A use of CTA `c`'s shared memory is finished
(`SharedFinished`) once its completion precedes, in `CompletedBefore`, the issue of an exit of a
thread of `c` (`OwnerExit`). Two kinds of chains give that order, and they are never joined:

* **Causal chains** (`StageCausedBefore`): a base causality path from the completion of the use to
  the issue of a thread instruction: `hb`, the release complete-tx of a copy observed by an acquire
  wait (`StageCausedBefore.of_copyRelease`), and the stages of one asynchronous operation
  (`StageCausedBefore.of_stage`). A causal chain extends by `hb`
  (`StageCausedBefore.tail_baseCausality`), so an `hb` path to an owner exit (`ReachesExit`)
  finishes the use (`SharedFinished.of_caused`, `SharedFinished.of_baseCausality`).
* **Enabling chains** (`EnabledBefore`): the use witnessed by a wait, followed by dependency
  edges with one object's order (`Resumes`, witnesses, stages), or such a path from the use's
  completion. The common case is a wait of an owner thread that witnesses the use and resumes
  that thread's exit (`SharedFinished.of_observer_exit`). An enabling chain extends by dependency
  edges (`EnabledBefore.tail`), and an enabling path from the completion of one use to the issue
  of another prepends to the other's chain (`EnabledBefore.of_edge`).

The last form serves an edge that a kernel assumption adds, such as the order of the arrive-ons of
two consecutive `tcgen05.commit`s of one thread at the same target (FA4's assumption A9, the
`CommitNext` edge of `LifetimeStep`): the arrive-on of the earlier commit, which no thread observes,
is finished when the later one is (`SharedFinished.of_next`). The edge is a premise, so the lemma
does not depend on the form of the Core arm that supplies it. -/

namespace PTX
open AsyncCopy

section
variable {L : Launch} {K : Kernel} {A : List Assumption} {X : Execution}

/-- `finish` is the exit of a thread of CTA `c`. -/
def OwnerExit (L : Launch) (X : Execution) (c : Nat) (finish : EvId) : Prop :=
  finish.1 < L.threads ∧ finish.1 / L.block = c ∧ ∃ pc, X.get finish = some ⟨pc, .exit⟩

/-- **A present use finished before an owner exit is finished.** -/
theorem SharedFinished.of_completedBefore {e : Ref} {c : Nat} {finish : EvId}
    (hp : X.RefPresent e) (hx : OwnerExit L X c finish)
    (h : CompletedBefore L K A X e (.thread finish, false)) : SharedFinished L K A X e c := by
  obtain ⟨hf, hc, pc, hget⟩ := hx
  exact ⟨hp, finish, pc, hf, hc, hget, h⟩

/-! ## Causal chains -/

/-- A base causality path from the completion of `e` to the issue of thread instruction `j`. -/
def StageCausedBefore (L : Launch) (X : Execution) (e : Ref) (j : EvId) : Prop :=
  Relation.TransGen (stageCausality L X) (e, true) (.thread j, false)

/-- An instruction before another in `hb`. -/
theorem StageCausedBefore.of_baseCausality {i j : EvId} (h : baseCausality L X i j) :
    StageCausedBefore L X (.thread i) j :=
  .single (stageCausality.of_baseCausality h)

/-- A causal chain to a present instruction extends by `hb` from that instruction. -/
theorem StageCausedBefore.tail_baseCausality {e : Ref} {j k : EvId} {ev : Event}
    (h : StageCausedBefore L X e j)
    (hj : X.get j = some ev) (hjk : baseCausality L X j k) : StageCausedBefore L X e k :=
  (h.tail (stageCausality.of_present hj)).tail (stageCausality.of_baseCausality hjk)

/-- The release complete-tx of a copy, observed by an acquire wait whose scope meets the issuer,
precedes the wait's program-order successor. -/
theorem StageCausedBefore.of_copyRelease {i w f : EvId} {p : Part} {ws : MbarScope}
    (hp : p = .notify .copy ∨ p = .notify .load) (ho : AsyncObserved X i p w true ws)
    (hs : ScopesMeet L .cluster i.1 ws w.1) (hpo : po X w f) :
    StageCausedBefore L X (.async i p) f :=
  .single (.inr (.inr ⟨rfl, rfl, f, rfl, i, p, w, ws, rfl, hp, ho, hs, hpo⟩))

/-- A stage precedes what the completion of its operation's next, present stage precedes. -/
theorem StageCausedBefore.of_stage {i j k : EvId} {p q : Part} (hq : X.RefPresent (.async j q))
    (hs : StageOrder X (.async i p, true) (.async j q, false))
    (h : StageCausedBefore L X (.async j q) k) :
    StageCausedBefore L X (.async i p) k := by
  have hc1 : stageCausality L X (.async i p, true) (.async j q, false) := .inl hs
  have hc2 : stageCausality L X (.async j q, false) (.async j q, true) :=
    .inl (.inl ⟨rfl, rfl, rfl, hq⟩)
  exact .head hc1 (.head hc2 h)

/-- A causal chain is a lifetime order. -/
theorem StageCausedBefore.completedBefore {e : Ref} {j : EvId} (h : StageCausedBefore L X e j) :
    CompletedBefore L K A X e (.thread j, false) :=
  .inl (.inl h)

/-! ## Exits reached by `hb` -/

/-- Instruction `x` precedes, in `hb`, the exit of a thread of CTA `c`. -/
def ReachesExit (L : Launch) (X : Execution) (c : Nat) (x : EvId) : Prop :=
  ∃ finish, OwnerExit L X c finish ∧ baseCausality L X x finish

/-- An instruction followed in program order by an owner exit reaches it. -/
theorem ReachesExit.of_po {c : Nat} {x finish : EvId} (hx : OwnerExit L X c finish)
    (h : po X x finish) : ReachesExit L X c x :=
  ⟨finish, hx, .single (.inl h)⟩

/-- `hb` predecessors of an instruction that reaches an owner exit reach it. -/
theorem ReachesExit.of_baseCausality {c : Nat} {x y : EvId} (h : ReachesExit L X c x)
    (hyx : baseCausality L X y x) :
    ReachesExit L X c y := by
  obtain ⟨finish, hf, hxf⟩ := h
  exact ⟨finish, hf, hyx.trans hxf⟩

/-- **A use with a causal chain to an instruction that reaches an owner exit is finished.** -/
theorem SharedFinished.of_caused {e : Ref} {c : Nat} {x : EvId} {ev : Event}
    (hp : X.RefPresent e) (h : StageCausedBefore L X e x) (hx : X.get x = some ev)
    (hr : ReachesExit L X c x) : SharedFinished L K A X e c := by
  obtain ⟨finish, hf, hxf⟩ := hr
  exact SharedFinished.of_completedBefore hp hf (h.tail_baseCausality hx hxf).completedBefore

/-- **A thread instruction that precedes an owner exit in `hb` is finished.** -/
theorem SharedFinished.of_baseCausality {e : EvId} {c : Nat} {ev : Event} (he : X.get e = some ev)
    (hr : ReachesExit L X c e) : SharedFinished L K A X (.thread e) c := by
  obtain ⟨finish, hf, hef⟩ := hr
  exact SharedFinished.of_completedBefore ⟨ev, he⟩ hf (CompletedBefore.of_baseCausality hef)

/-! ## Enabling chains -/

/-- The enabling forms of `CompletedBefore`: a dependency path, with the order of one object of
`OrderObject.Enabling`, from the completion of `e`, or from the return of a wait that the
asynchronous stage `e` is a witness of. -/
def EnabledBefore (L : Launch) (K : Kernel) (A : List Assumption) (X : Execution) (e : Ref)
    (n : Ref × Bool) : Prop :=
  (∃ o, o.Enabling ∧ Relation.TransGen (EnablesWith L K A X o) (e, true) n) ∨
  ∃ i p w o, e = .async i p ∧ Witness L X e w ∧ o.Enabling ∧
    Relation.TransGen (EnablesWith L K A X o) (.thread w, true) n

/-- An enabling chain is a lifetime order. -/
theorem EnabledBefore.completedBefore {e : Ref} {n : Ref × Bool}
    (h : EnabledBefore L K A X e n) : CompletedBefore L K A X e n := by
  rcases h with ⟨o, ho, h⟩ | h
  · exact .inl (.inr ⟨o, ho, h⟩)
  · exact .inr h

/-- An asynchronous stage witnessed by a wait, then a dependency path from the wait's return. -/
theorem EnabledBefore.of_observed {i w : EvId} {p : Part} {n : Ref × Bool}
    (ho : Witness L X (.async i p) w)
    (h : Relation.TransGen (DepStep L K X) (.thread w, true) n) :
    EnabledBefore L K A X (.async i p) n :=
  .inr ⟨i, p, w, .mbar ⟨.shared, 0, 0⟩, rfl, ho, trivial, EnablesWith.of_enables h⟩

/-- An enabling chain extends by a dependency edge. -/
theorem EnabledBefore.tail {e : Ref} {n n' : Ref × Bool} (h : EnabledBefore L K A X e n)
    (hn : DepStep L K X n n') : EnabledBefore L K A X e n' := by
  rcases h with ⟨o, ho, h⟩ | ⟨i, p, w, o, he, hobs, ho, h⟩
  · exact .inl ⟨o, ho, h.tail (Or.inl hn)⟩
  · exact .inr ⟨i, p, w, o, he, hobs, ho, h.tail (Or.inl hn)⟩

/-- **A dependency path from the completion of `e` to the issue of the present `f` prepends to
`f`'s enabling chain.** The path may contain the edge a kernel assumption adds (`CommitNext`). -/
theorem EnabledBefore.of_edge {e f : Ref} {n : Ref × Bool}
    (hedge : Relation.TransGen (DepStep L K X) (e, true) (f, false)) (hf : X.RefPresent f)
    (h : EnabledBefore L K A X f n) : EnabledBefore L K A X e n := by
  have hp : ∀ o, Relation.TransGen (EnablesWith L K A X o) (e, true) (f, false) :=
    fun _ => EnablesWith.of_enables hedge
  rcases h with ⟨o, ho, h⟩ | ⟨i, p, w, o, rfl, hobs, ho, h⟩
  · exact .inl ⟨o, ho, (hp o).trans (.head (Or.inl (DepStep.node hf)) h)⟩
  · exact .inl ⟨o, ho, (hp o).trans (.head (Or.inl (DepStep.of_witness L hobs)) h)⟩

/-! ## Exits reached by enabling -/

/-- The later instruction `f` of a thread follows the successful poll `w` of a canonical spin. -/
theorem Resumes.of_spin {w f : EvId} {pc ex : Nat} {m : Loc} {q : Nat} {acq : Bool}
    {sc : MbarScope} (hw : X.get w = some ⟨pc, .wait m q true acq sc⟩)
    (hs : K.CanonicalSpin pc ex) (hthr : w.1 = f.1) (hlt : w.2 < f.2)
    (hlen : f.2 < (X.tr f.1).length) : Resumes K X w f := by
  refine ⟨⟨hthr, hlt, hlen⟩, ?_⟩
  simp only [hw, Option.map_some, Kind.resume]
  exact ⟨pc, ex, m, q, acq, sc, hw, hs, ⟨hthr, hlt, hlen⟩⟩

/-- **A use witnessed by a wait that resumes an owner exit is finished.** The common form: the
waiting thread belongs to the owner CTA, and its exit is reached only through the wait. -/
theorem SharedFinished.of_observer_exit {i w finish : EvId} {p : Part} {c : Nat}
    (hp : X.RefPresent (.async i p)) (ho : Witness L X (.async i p) w)
    (hg : Resumes K X w finish) (hx : OwnerExit L X c finish) :
    SharedFinished L K A X (.async i p) c :=
  SharedFinished.of_completedBefore hp hx
    (EnabledBefore.of_observed ho (.single (DepStep.of_resumes L hg))).completedBefore

/-- **A use witnessed by a wait, followed by a dependency path to an owner exit, is finished.** -/
theorem SharedFinished.of_observed_chain {i w finish : EvId} {p : Part} {c : Nat}
    (hp : X.RefPresent (.async i p)) (ho : Witness L X (.async i p) w)
    (h : Relation.TransGen (DepStep L K X) (.thread w, true) (.thread finish, false))
    (hx : OwnerExit L X c finish) : SharedFinished L K A X (.async i p) c :=
  SharedFinished.of_completedBefore hp hx (EnabledBefore.of_observed ho h).completedBefore

/-- **A use ordered by a dependency path before another use's enabling chain to an owner exit is
finished.** For FA4's assumption A9, `e` and `f` are the arrive-ons at one target rank of two
consecutive commits of one thread and `hedge` is the assumed edge. -/
theorem SharedFinished.of_next {e f : Ref} {c : Nat} {finish : EvId} (he : X.RefPresent e)
    (hedge : Relation.TransGen (DepStep L K X) (e, true) (f, false)) (hf : X.RefPresent f)
    (h : EnabledBefore L K A X f (.thread finish, false)) (hx : OwnerExit L X c finish) :
    SharedFinished L K A X e c :=
  SharedFinished.of_completedBefore he hx (EnabledBefore.of_edge hedge hf h).completedBefore

/-- The arrive-on form of `SharedFinished.of_next`: the arrive-on of commit `i` at rank `r`, which a
kernel assumption orders before the arrive-on at rank `r` of commit `j` (`CommitNext`), and which a
wait witnesses before a dependency path to an owner exit. -/
theorem SharedFinished.of_commit_next {i j w finish : EvId} {r : Fin 16} {c : Nat}
    (hi : X.RefPresent (.async i (.tcNotify r)))
    (hn : CommitNext A X (.async i (.tcNotify r)) (.async j (.tcNotify r)))
    (ho : Witness L X (.async j (.tcNotify r)) w)
    (h : Relation.TransGen (DepStep L K X) (.thread w, true) (.thread finish, false))
    (hx : OwnerExit L X c finish) : SharedFinished L K A X (.async i (.tcNotify r)) c := by
  refine SharedFinished.of_completedBefore hi hx (.inl (.inr ⟨.mbar ⟨.shared, 0, 0⟩, trivial, ?_⟩))
  exact .head (Or.inr (Or.inr ⟨rfl, rfl, .inl hn⟩))
    (.head (Or.inl (DepStep.of_witness L ho)) (EnablesWith.of_enables h))

end

end PTX
