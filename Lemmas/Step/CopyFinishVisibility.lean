-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Async.AsyncChain
public import Lemmas.Step.CopyFinishObject

@[expose] public section

/-! Appending a completion cannot retroactively change an earlier wait's observation.
In particular it cannot publish the new copy's bytes to a consumer already in the trace. -/
namespace PTX
open AsyncCopy MBarrier
noncomputable section
variable {L : Launch} {X : Execution} {i : EvId} {bs : List Byte} {src : Nat → Option Ref}
  {mb : Loc} {rec : Record Ref}

theorem finishCopyRecord_baseCausality_iff (hid : rec.id = .async i (.notify .copy)) {e f : EvId} :
    baseCausality L (X.finishCopyRecord i bs src mb rec) e f ↔ baseCausality L X e f := by
  change baseCausality L ((X.finishCopy i bs src).appendObject mb rec) e f ↔ _
  rw [appendObject_baseCausality_iff (fun w _ _ => by rw [hid]; simp)]
  rfl

theorem finishCopyRecord_waitObserves_iff (hid : rec.id = .async i (.notify .copy)) {x : Ref}
    {w : EvId} {m : Loc} {acq : Bool} {ws : MbarScope} :
    WaitObserves (X.finishCopyRecord i bs src mb rec) x w m acq ws ↔
      WaitObserves X x w m acq ws := by
  change WaitObserves ((X.finishCopy i bs src).appendObject mb rec) x w m acq ws ↔ _
  rw [appendObject_waitObserves_iff (by rw [hid]; simp)]
  rfl

theorem finishCopyRecord_asyncObserved_iff (ho : ObjectsOk X)
    (hn : (X.async.copies i).notified = false) (hid : rec.id = .async i (.notify .copy))
    {j w : EvId} {p : Part} {acq : Bool} {ws : MbarScope} :
    AsyncObserved (X.finishCopyRecord i bs src mb rec) j p w acq ws ↔
      AsyncObserved X j p w acq ws := by
  have hnone : ∀ m, ¬ WaitObserves X (.async i (.notify .copy)) w m acq ws := by
    rintro m ⟨-, k, l, r, waiter, phase, hk, hrid, -⟩
    exact no_copy_notification_record ho hn (List.mem_of_getElem? hk) hrid
  unfold AsyncObserved
  simp only [finishCopyRecord_waitObserves_iff hid]
  by_cases hj : j = i
  · subst j
    cases p <;> try rfl
    all_goals
      simp only [Notifies, Part.target]
      constructor
    all_goals
      first
        | rintro ⟨n, m, (⟨rfl, -⟩ | h), hw⟩
          · exact (hnone m hw).elim
          · exact ⟨n, m, .inr h, hw⟩
        | rintro ⟨n, m, ⟨rfl, -⟩, hw⟩
          exact (hnone m hw).elim
  · cases p <;> try rfl
    all_goals
      simp only [Notifies, AsyncCopy.Part.target, AsyncCopy.NotifyOn, Notification,
        Execution.finishCopyRecord, Execution.appendObject,
        Execution.finishCopy, ite_eq_right hj]
      rfl

/-- Completing copy `i` changes the presence of no stage of another operation. -/
theorem finishCopyRecord_asyncPresent_of_ne {j : EvId} (hj : j ≠ i) {p : Part} :
    (X.finishCopyRecord i bs src mb rec).AsyncPresent j p ↔ X.AsyncPresent j p := by
  cases p <;> simp only [Execution.AsyncPresent, Execution.MmaRead, Execution.finishCopyRecord,
    Execution.appendObject, Execution.finishCopy, ite_eq_right hj]
  all_goals rfl

/-- No group wait covers a copy completed through an mbarrier. -/
theorem not_groupWaitsFor_of_mbarrier {s : Spec} {m : Loc} (hc : X.Copy i s)
    (hm : s.completion = .mbarrier m) (k : GroupWait) (w : EvId) : ¬ GroupWaitsFor X k i w := by
  cases k with
  | bulk mode => exact not_bulkWaitsFor_of_copy hc (by simp [hm])
  | cpAsync => exact not_asyncGroupWaitsFor_of_copy hc (by simp [hm])

/-- The stages that a group wait covering `j` waits for are present after the completion of copy
`i` exactly when they were present before, when `i` is completed through an mbarrier. -/
theorem finishCopyRecord_groupWaitPresent_iff {s : Spec} {m : Loc} (hc : X.Copy i s)
    (hm : s.completion = .mbarrier m) {k : GroupWait} {j w : EvId} :
    (GroupWaitsFor X k j w ∧ ∀ q ∈ GroupWaitStages X j k,
      (X.finishCopyRecord i bs src mb rec).AsyncPresent j q) ↔
    (GroupWaitsFor X k j w ∧ ∀ q ∈ GroupWaitStages X j k, X.AsyncPresent j q) := by
  apply and_congr_right
  intro hw
  by_cases hj : j = i
  · subst j
    exact (not_groupWaitsFor_of_mbarrier hc hm k w hw).elim
  · simp only [finishCopyRecord_asyncPresent_of_ne hj]

theorem finishCopyRecord_asyncFinished_iff (ho : ObjectsOk X)
    (hn : (X.async.copies i).notified = false) (hid : rec.id = .async i (.notify .copy))
    {s : Spec} {m : Loc} (hc : X.Copy i s) (hm : s.completion = .mbarrier m)
    {j w : EvId} {p : Part} :
    AsyncFinished L (X.finishCopyRecord i bs src mb rec) j p w ↔ AsyncFinished L X j p w := by
  unfold AsyncFinished
  simp only [finishCopyRecord_asyncObserved_iff ho hn hid]
  exact or_congr_left (exists_congr fun _ => and_congr_right fun _ =>
    finishCopyRecord_groupWaitPresent_iff hc hm)

theorem finishCopyRecord_asyncOnlyFinished_iff {s : Spec} {m : Loc} (hc : X.Copy i s)
    (hm : s.completion = .mbarrier m) {j w : EvId} {p : Part} :
    AsyncOnlyFinished (X.finishCopyRecord i bs src mb rec) j p w ↔ AsyncOnlyFinished X j p w := by
  unfold AsyncOnlyFinished
  exact and_congr_right fun _ => finishCopyRecord_groupWaitPresent_iff (k := .bulk .asyncProxy)
    hc hm

theorem finishCopyRecord_asyncBefore_iff (ho : ObjectsOk X)
    (hn : (X.async.copies i).notified = false) (hid : rec.id = .async i (.notify .copy))
    {s : Spec} {m : Loc} (hc : X.Copy i s) (hm : s.completion = .mbarrier m)
    {l : Loc} {a b : EvId × Part} :
    AsyncBefore L (X.finishCopyRecord i bs src mb rec) l a b ↔ AsyncBefore L X l a b := by
  exact AsyncBefore.congr (L:=L) (X:=X.finishCopyRecord i bs src mb rec) (Y:=X)
    (fun _ _ => Iff.rfl)
    (fun _ _ _ => finishCopyRecord_asyncFinished_iff ho hn hid hc hm)
    (fun _ _ _ => finishCopyRecord_asyncOnlyFinished_iff hc hm)
    (fun _ _ _ _ => finishCopyRecord_baseCausality_iff hid)
    (fun _ _ _ _ => Iff.rfl)

/-- Before its notification, the read, the write and the notification of a copy completed through
an mbarrier are observed by no wait. -/
theorem unnotified_copy_not_finished {s : Spec} {m : Loc} (hc : X.Copy i s)
    (hm : s.completion = .mbarrier m) (hn : (X.async.copies i).notified = false) {p : Part}
    (hp : p = .read .copy ∨ p = .write .copy ∨ p = .notify .copy) (w : EvId) :
    ¬ AsyncFinished L X i p w := by
  intro hf
  obtain ⟨ws, ⟨n, m', hN, -⟩, -⟩ := (asyncFinished_copy_of_mbarrier (L := L) hc hm).mp hf
  have hon : NotifyOn X i .copy m' := by
    rcases hp with rfl | rfl | rfl
    · exact ((notifies_copy_of_mbarrier hc hm (.inl rfl)).mp hN).2
    · exact ((notifies_copy_of_mbarrier hc hm (.inr rfl)).mp hN).2
    · exact hN.2
  obtain ⟨-, -, -, hnot, -⟩ := hon
  rw [hn] at hnot
  cases hnot

theorem finishCopyRecord_asyncPresent_on_edge (ho : ObjectsOk X)
    (hn : (X.async.copies i).notified = false) (hid : rec.id = .async i (.notify .copy))
    {s : Spec} {m : Loc} (hc : X.Copy i s) (hm : s.completion = .mbarrier m)
    {l : Loc} {a b : EvId × Part}
    (hedge : AsyncBefore L (X.finishCopyRecord i bs src mb rec) l a b) :
    (X.finishCopyRecord i bs src mb rec).AsyncPresent a.1 a.2 ↔ X.AsyncPresent a.1 a.2 := by
  rcases a with ⟨j, p⟩
  by_cases hj : j = i
  · subst j
    have h := (finishCopyRecord_asyncBefore_iff ho hn hid hc hm).mp hedge
    have hnf : ∀ w, (p = .read .copy ∨ p = .write .copy ∨ p = .notify .copy) →
        ¬ AsyncFinished L X i p w := fun w hp => unnotified_copy_not_finished hc hm hn hp w
    have hno : ∀ w, ¬ AsyncOnlyFinished X i p w := fun w ho' =>
      not_groupWaitsFor_of_mbarrier hc hm _ w ho'.2.1
    rcases h.2.2 with ⟨w, hf, -⟩ | ⟨w, ho', -⟩
    · cases p <;> first
        | rfl
        | (simp [Execution.AsyncPresent, Execution.finishCopyRecord, Execution.appendObject,
            Execution.finishCopy]; done)
        | exact (hnf w (by simp) hf).elim
    · exact (hno w ho').elim
  · exact finishCopyRecord_asyncPresent_of_ne hj

/-- Visibility between existing instruction instances is unchanged until a new wait
actually observes the appended notification. -/
theorem finishCopyRecord_modelCausality_iff (ho : ObjectsOk X)
    (hn : (X.async.copies i).notified = false) (hid : rec.id = .async i (.notify .copy))
    {s : Spec} {m : Loc} (hc : X.Copy i s) (hm : s.completion = .mbarrier m)
    {l : Loc} {e f : Ref} :
    modelCausality L (X.finishCopyRecord i bs src mb rec) l e f ↔ modelCausality L X l e f := by
  have hp : ∀ e j, ProxyBefore L (X.finishCopyRecord i bs src mb rec) e j l ↔
      ProxyBefore L X e j l := by
    intro e j
    unfold ProxyBefore
    simp only [finishCopyRecord_baseCausality_iff hid]
    rfl
  cases e with
  | thread e =>
    cases f with
    | thread f => exact or_congr (finishCopyRecord_baseCausality_iff hid) Iff.rfl
    | async j p =>
      simp only [modelCausality, hp, finishCopyRecord_baseCausality_iff hid]
      rfl
  | async j p =>
    cases f with
    | thread f =>
      have hcb (w : EvId) :
          ObservedCompletionBefore L (X.finishCopyRecord i bs src mb rec) l j p w f ↔
            ObservedCompletionBefore L X l j p w f :=
        observedCompletionBefore_congr rfl rfl (finishCopyRecord_baseCausality_iff hid) (hp w f)
      simp only [modelCausality, finishCopyRecord_asyncFinished_iff ho hn hid hc hm, hcb]
      rfl
    | async k q =>
      exact and_congr_right fun _ =>
        AsyncChain.congr_on_edges (fun _ _ => finishCopyRecord_asyncBefore_iff ho hn hid hc hm)
          (fun _ _ => finishCopyRecord_asyncPresent_on_edge ho hn hid hc hm)

/-- An unnotified copy completed through an mbarrier cannot yet publish its destination bytes
through a successful completion observation. This does not prevent its write effect from
existing. -/
theorem unnotified_copy_write_not_vis {s : Spec} {m : Loc} (hc : X.Copy i s)
    (hm : s.completion = .mbarrier m) (hn : (X.async.copies i).notified = false)
    {l : Loc} {e : Ref} : ¬ modelCausality L X l (.async i (.write .copy)) e := by
  have hfin := unnotified_copy_not_finished (L := L) hc hm hn (p := .write .copy) (by simp)
  cases e with
  | thread e => rintro ⟨_, w, hf, _⟩; exact hfin w hf
  | async j p =>
    intro h
    obtain ⟨_, edge⟩ := AsyncChain.first h.2
    rcases edge.2.2 with ⟨w, hf, _⟩ | ⟨w, ho, _⟩
    · exact hfin w hf
    · exact not_groupWaitsFor_of_mbarrier hc hm _ w ho.2.1

end
end PTX
