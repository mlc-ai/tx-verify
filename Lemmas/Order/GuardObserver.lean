-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.GuardOrder
public import Lemmas.Order.WaitOrderWaits
import Lemmas.Order.Order
import Lemmas.Order.OrderWaits
import Lemmas.Tmem.AllocResultDependency

@[expose] public section

/-! # Observers of a guarded synchronization

The guarded `baseCausality` lemmas are in `Lemmas.Order.GuardOrder`; the observations that name a
group wait live in `Lemmas.Order.WaitOrderWaits`, so the two halves meet here. The observer of an
asynchronous completion has two halves, kept apart: what the waiting event is
(`observer_guard_source`, proved from `SyncGuarded`) and how the completion is reached by
dependency (`observer_path`, proved from the stage order and the effect validity). The guarded
model causality is asymmetric. -/

namespace PTX
noncomputable section
variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- The event of a group wait and its kind: a blocking return that is not an arrival. -/
private theorem groupWaitEvent {X : Execution} {i w : EvId} {k : GroupWait}
    (h : GroupWaitsFor X k i w) :
    ∃ pc kd, X.get w = some ⟨pc, kd⟩ ∧ kd.resume = .blocking false ∧
      (∀ m tx count sc, kd ≠ .arrive m tx count true sc) := by
  cases k with
  | bulk mode =>
    obtain ⟨pc, rem, hget, -⟩ := h
    exact ⟨pc, .bulkWait mode rem, hget, by simp [Kind.resume],
      by rintro m tx count sc h'; cases h'⟩
  | cpAsync =>
    obtain ⟨pc, rem, hget, -⟩ := h
    exact ⟨pc, .asyncWait rem, hget, by simp [Kind.resume],
      by rintro m tx count sc h'; cases h'⟩

/-- An observing wait of an asynchronous completion is a guard that is not a release arrival: a
group wait returns after its blocking wait, and an acquire wait is the successful poll of a
canonical spin (`SyncGuarded.wait`). This is the half of `observer_enables` that
`chain_observers` consumes directly; the dependency path to the wait is `observer_path`. -/
theorem observer_guard_source (hg : SyncGuarded L K X) {i w : EvId} {p : AsyncCopy.Part}
    (h : AsyncFinished L X i p w ∨ AsyncOnlyFinished X i p w) :
    GuardSource K X w ∧ ∀ m tx count sc, ¬ X.Arrive w m tx count true sc := by
  have notArrive : ∀ {pc : Nat} {kd : Kind}, X.get w = some ⟨pc, kd⟩ →
      (∀ m tx count sc, kd ≠ .arrive m tx count true sc) →
      ∀ m tx count sc, ¬ X.Arrive w m tx count true sc := by
    rintro pc kd hw hk m tx count sc ⟨pc', h'⟩
    rw [hw] at h'
    cases h'
    exact hk m tx count sc rfl
  have groupWait : ∀ {k : GroupWait}, GroupWaitsFor X k i w →
      GuardSource K X w ∧ ∀ m tx count sc, ¬ X.Arrive w m tx count true sc := by
    intro k hwk
    obtain ⟨pc, kd, hget, hres, hkd⟩ := groupWaitEvent hwk
    exact ⟨.inr ⟨_, false, hget, hres⟩, notArrive hget hkd⟩
  rcases h with (⟨k, -, hwk, -⟩ | ⟨ws, hobs, -⟩) | ⟨-, hwk, -⟩
  · exact groupWait hwk
  · rcases hobs with ⟨hn, hm, hnot, hwo⟩
    obtain ⟨pc, par, hgetw⟩ := hwo.1
    exact ⟨hg.wait hgetw, notArrive hgetw (by intros; simp)⟩
  · exact groupWait hwk

/-- The issue of a recorded linear copy is a present instruction. -/
private theorem copy_issue_present (hv : EffectValidity L X) {i : EvId} {q : AsyncCopy.Part}
    (hq : AsyncCopy.present (X.async.copies i) q) : X.RefPresent (.thread i) := by
  obtain ⟨s, hs, -⟩ := hv.tma.1 i ⟨q, hq⟩
  unfold AsyncCopy.issuedBy at hs
  split at hs
  · exact ⟨_, by assumption⟩
  · cases hs

/-- The issue of an operation reaches, through one of its present writes, every stage that the
write precedes (`IssueStage`, then `StageEdge`). -/
private theorem issue_write_path {i : EvId} {s : AsyncCopy.Slot} {n : AsyncCopy.Ref}
    (hi : X.RefPresent (.thread i)) (hw : X.AsyncPresent i (.write s))
    (he : StageEdge X (.async i (.write s)) n) :
    Relation.TransGen (DepStep L K X) (.thread i, false) (n, false) :=
  ((Relation.TransGen.single (DepStep.issue hi hw (fun _ h => by cases h) (fun h => by cases h)
    (fun h => by cases h) (fun h => by cases h))).tail (DepStep.node hw)).tail
    (DepStep.stage (.inr ⟨rfl, rfl, he⟩))

/-- The notification `t` of the operation issued by `i` is present and reached from the issue
through the write it signals: a notified copy has written (`CopyOk`), a notified tensor load has
written a tile byte (`tensor_write_present`), and a notified CLC response has been written
(`Clc.EffectsOk.notified`). -/
private theorem notifyOn_path (hv : EffectValidity L X) {i : EvId} {t : AsyncCopy.Target}
    {m : Loc} (h : AsyncCopy.NotifyOn X i t m) :
    X.AsyncPresent i (.notify t) ∧
      Relation.TransGen (DepStep L K X) (.thread i, false) (.async i (.notify t), false) := by
  cases t with
  | copy =>
    obtain ⟨bytes, s, hs, hn, -, -⟩ := h
    obtain ⟨s', hs', hcopy⟩ := hv.tma.1 i ⟨.notify .copy, hn⟩
    obtain ⟨-, bs, hwb⟩ := hcopy.2.2.2.1 hn
    have hw : X.AsyncPresent i (.write .copy) := by simp [Execution.AsyncPresent, hwb]
    exact ⟨hn, issue_write_path (copy_issue_present hv (q := .notify .copy) hn) hw
      ⟨rfl, rfl, hw, hn⟩⟩
  | load =>
    obtain ⟨o, a, ho, ⟨pc, hiss⟩, -, hnot⟩ := h
    obtain ⟨x, y, k, hw⟩ := tensor_write_present hv ho hnot
    have hn : X.AsyncPresent i (.notify .load) := ⟨o, ho, hnot⟩
    exact ⟨hn, issue_write_path ⟨_, hiss⟩ hw ⟨rfl, rfl, hw, hn⟩⟩
  | cta c =>
    obtain ⟨s, targets, ⟨pc, hiss⟩, -, hnot, -⟩ := h
    have hw : X.AsyncPresent i (.write (.cta c)) :=
      (hv.clc.2.2.2.1 i s targets ⟨pc, hiss⟩).1.notified c hnot
    exact ⟨hnot, issue_write_path ⟨_, hiss⟩ hw ⟨rfl, rfl, hw, hnot⟩⟩

/-- The notification that signals the completion of part `p` of the operation issued by `i` is
present and reached by dependency from the issue of the operation or of a later instruction of its
thread: an MMA's commit arrive-on follows the issue of the commit (`IssueStage`), the arrive-on of a
`cp.async.mbarrier.arrive` follows the tracked copy's write (`ArriveOk`, `StageEdge`), and every
other notification follows the write it signals (`notifyOn_path`). -/
private theorem notifies_path (hv : EffectValidity L X) {i : EvId} {p : AsyncCopy.Part}
    {x : AsyncCopy.Ref} {m : Loc} (h : AsyncCopy.Notifies X i p x m) :
    ∃ j q, x = .async j q ∧ X.AsyncPresent j q ∧ ∃ n, (n = i ∨ po X i n) ∧
      Relation.TransGen (DepStep L K X) (.thread n, false) (x, false) := by
  have mma : ∀ {commit s rank}, x = .async commit (.tcNotify rank) →
      AsyncCopy.TracksMma X i commit → X.Commit commit s → rank ∈ X.tcNotified commit →
      ∃ j q, x = .async j q ∧ X.AsyncPresent j q ∧ ∃ n, (n = i ∨ po X i n) ∧
        Relation.TransGen (DepStep L K X) (.thread n, false) (x, false) := by
    rintro commit s rank rfl ⟨h1, h2, -, -⟩ ⟨pc, hc⟩ hrank
    exact ⟨_, _, rfl, hrank, commit,
      .inr (po_of_not_access h1 h2 (len_of_get hc) (by simp [hc, Event.acc])),
      .single (DepStep.issue ⟨_, hc⟩ hrank (fun _ h => by cases h) (fun h => by cases h)
        (fun h => by cases h) (fun h => by cases h))⟩
  have copy : (x = .async i (.notify .copy) ∧ AsyncCopy.NotifyOn X i .copy m) ∨
      (∃ j noinc, x = .async j .arriveOn ∧ AsyncCopy.TracksCpAsync X i j ∧
        X.AsyncArrive j m noinc ∧ X.async.arrived j = true) →
      ∃ j q, x = .async j q ∧ X.AsyncPresent j q ∧ ∃ n, (n = i ∨ po X i n) ∧
        Relation.TransGen (DepStep L K X) (.thread n, false) (x, false) := by
    rintro (⟨rfl, hn⟩ | ⟨j, noinc, rfl, ht, -, harr⟩)
    · exact ⟨_, _, rfl, (notifyOn_path (K := K) hv hn).1, i, .inl rfl, (notifyOn_path hv hn).2⟩
    · have hwb := (hv.tma.2.2.2 j harr).2 i ht
      have hw : X.AsyncPresent i (.write .copy) := hwb
      exact ⟨_, _, rfl, harr, i, .inl rfl, issue_write_path
        (copy_issue_present hv (q := .write .copy) hwb) hw ⟨ht, hw, harr⟩⟩
  have target : ∀ {t}, x = .async i (.notify t) → AsyncCopy.NotifyOn X i t m →
      ∃ j q, x = .async j q ∧ X.AsyncPresent j q ∧ ∃ n, (n = i ∨ po X i n) ∧
        Relation.TransGen (DepStep L K X) (.thread n, false) (x, false) := by
    rintro t rfl hn
    exact ⟨_, _, rfl, (notifyOn_path (K := K) hv hn).1, i, .inl rfl, (notifyOn_path hv hn).2⟩
  cases p with
  | mmaRead b k =>
    obtain ⟨commit, s, rank, hx, ht, hc, -, hr⟩ := h
    exact mma hx ht hc hr
  | mmaDone =>
    obtain ⟨commit, s, rank, hx, ht, hc, -, hr⟩ := h
    exact mma hx ht hc hr
  | readCopy | writeCopy => exact copy h
  | readLoad _ _ _ | writeLoad _ _ _ | writeCta _ | writeElem _ | oldElem _ | notifyCopy
  | notifyLoad | notifyCta _ => exact target h.1 h.2
  | _ => exact h.elim

/-- A stage that a group wait waits for and that the issue of the operation precedes
(`IssueStage`): the read completion of a tensor store or the read of a linear copy. -/
private theorem groupWait_issueStage (hv : EffectValidity L X) {i : EvId} {k : GroupWait}
    (hst : ∀ q ∈ GroupWaitStages X i k, X.AsyncPresent i q) :
    ∃ q, q ∈ GroupWaitStages X i k ∧ X.AsyncPresent i q ∧
      Relation.TransGen (DepStep L K X) (.thread i, false) (.async i q, false) := by
  have hq : ∃ q, q ∈ GroupWaitStages X i k ∧ (q = .readsDone ∨ q = .read .copy) := by
    unfold GroupWaitStages
    split <;> simp
  obtain ⟨q, hmem, hq⟩ := hq
  have hp := hst q hmem
  have hi : X.RefPresent (.thread i) := by
    rcases hq with rfl | rfl
    · obtain ⟨o, ho, -⟩ := hp
      obtain ⟨⟨a, pc, hiss⟩, -⟩ := hv.store i o ho
      exact ⟨_, hiss⟩
    · exact copy_issue_present hv (q := .read .copy) hp
  refine ⟨q, hmem, hp, .single (DepStep.issue hi hp ?_ ?_ ?_ ?_)⟩ <;>
    rcases hq with rfl | rfl <;> first | (intro _ h; cases h) | (intro h; cases h)

/-- The dependency half of `observer_enables`: an observed completion of an asynchronous operation
is reached by a `DepStep` path from the issue of the operation or from a later instruction of its
thread. A group wait returns after the stages it waits for (`GroupWaitsFor.witness`), and an
acquire wait after the notification it observed (`Witness.of_mbarObserved`); that notification is
reached through the stage order (`notifies_path`). -/
theorem observer_path (hv : EffectValidity L X) {i w : EvId} {p : AsyncCopy.Part}
    (h : AsyncFinished L X i p w ∨ AsyncOnlyFinished X i p w) :
    ∃ n, (n = i ∨ po X i n) ∧
      Relation.TransGen (DepStep L K X) (.thread n, false) (.thread w, true) := by
  have group : ∀ {k}, GroupWaitsFor X k i w →
      (∀ q ∈ GroupWaitStages X i k, X.AsyncPresent i q) → ∃ n, (n = i ∨ po X i n) ∧
        Relation.TransGen (DepStep L K X) (.thread n, false) (.thread w, true) := by
    intro k hk hst
    obtain ⟨q, hmem, hp, hpath⟩ := groupWait_issueStage (K := K) hv hst
    exact ⟨i, .inl rfl, hpath.tail (DepStep.of_witness L (hk.witness hmem hp))⟩
  rcases h with (⟨k, -, hk, hst⟩ | ⟨ws, ⟨x, m, hn, hwo⟩, -⟩) | ⟨-, hk, hst⟩
  · exact group hk hst
  · obtain ⟨j, q, rfl, hx, n, hin, hpath⟩ := notifies_path (K := K) hv hn
    exact ⟨n, hin, hpath.tail (DepStep.of_witness L (Witness.of_mbarObserved
      (mbarObserved_of_waitObserves hv.tma.2.2.1 hx hwo)))⟩
  · exact group hk hst

/-- A successful mbarrier observation, including a relaxed one, follows its notification in
the dependency order. The wait is a guard for the subsequent events of its thread. -/
theorem asyncObserved_enables (hv : EffectValidity L X) (hg : SyncGuarded L K X)
    {i w : EvId} {p : AsyncCopy.Part} {acq : Bool} {sc : MbarScope}
    (h : AsyncCopy.AsyncObserved X i p w acq sc) :
    ∃ n, (n = i ∨ po X i n) ∧
      Relation.TransGen (DepStep L K X) (.thread n, false) (.thread w, true) ∧
      GuardSource K X w ∧ ∀ m tx count scope, ¬ X.Arrive w m tx count true scope := by
  obtain ⟨x, m, hn, hwo⟩ := h
  obtain ⟨j, q, rfl, hx, n, hin, hpath⟩ := notifies_path (K := K) hv hn
  obtain ⟨pc, par, hget⟩ := hwo.1
  refine ⟨n, hin, hpath.tail (DepStep.of_witness L (Witness.of_mbarObserved
    (mbarObserved_of_waitObserves hv.tma.2.2.1 hx hwo))), hg.wait hget, ?_⟩
  rintro addr tx count scope ⟨pc', h⟩
  rw [hget] at h
  cases h

/-- An observer of an asynchronous operation's completion is a guard reached by dependency from
the issue of the operation or of a later instruction of its thread: `observer_path` supplies the
path, `observer_guard_source` identifies the wait. -/
theorem observer_enables (hv : EffectValidity L X) (hg : SyncGuarded L K X) {i w : EvId}
    {p : AsyncCopy.Part} (h : AsyncFinished L X i p w ∨ AsyncOnlyFinished X i p w) :
    ∃ n, (n = i ∨ po X i n) ∧
      Relation.TransGen (DepStep L K X) (.thread n, false) (.thread w, true) ∧
      GuardSource K X w ∧ ∀ m tx count sc, ¬ X.Arrive w m tx count true sc := by
  obtain ⟨n, hn, hp⟩ := observer_path (K := K) hv h
  exact ⟨n, hn, hp, observer_guard_source hg h⟩

/-- The guard behind an `hb` path reaches the notifying instruction of a later operation. -/
theorem reach_notifier (hg : SyncGuarded L K X) (ho : AsyncCopy.ObjectsOk X)
    (hok : GuardOk L X) {w x n : EvId} (hw : GuardSource K X w)
    (hna : ∀ m tx count sc, ¬ X.Arrive w m tx count true sc) (h : baseCausality L X w x)
    (hn : n = x ∨ po X x n) :
    Relation.TransGen (DepStep L K X) (.thread w, true) (.thread n, false) := by
  rcases hn with rfl | hn
  · exact baseCausality_enables hg ho hok hw hna h
  · exact baseCausality_enables hg ho hok hw hna (h.tail (.inl hn))

/-- A direct asynchronous order step: its source is observed, and the observer precedes the
target's issue. -/
private theorem before_observed {l : Loc} {a b : EvId × AsyncCopy.Part}
    (h : AsyncBefore L X l a b) : ∃ w, (AsyncFinished L X a.1 a.2 w ∨
      AsyncOnlyFinished X a.1 a.2 w) ∧ baseCausality L X w b.1 := by
  obtain ⟨-, -, ⟨w, hf, hb⟩ | ⟨w, hf, hp⟩⟩ := h
  · exact ⟨w, .inl hf, hb⟩
  · exact ⟨w, .inr hf, .single (.inl hp)⟩

/-- Along an asynchronous chain the observers are connected by enabling. -/
private theorem chain_observers (hv : EffectValidity L X)
    (hg : SyncGuarded L K X) (hok : GuardOk L X)
    {l : Loc} {a c : EvId × AsyncCopy.Part} (h : AsyncChain L X l a c) :
    ∃ w0 wl, (AsyncFinished L X a.1 a.2 w0 ∨ AsyncOnlyFinished X a.1 a.2 w0) ∧
      Relation.ReflTransGen (DepStep L K X) (.thread w0, true) (.thread wl, true) ∧
      GuardSource K X wl ∧ (∀ m tx count sc, ¬ X.Arrive wl m tx count true sc) ∧
      baseCausality L X wl c.1 := by
  induction h with
  | direct h =>
    obtain ⟨w, hf, hb⟩ := before_observed h
    obtain ⟨hw, hna⟩ := observer_guard_source hg hf
    exact ⟨w, w, hf, .refl, hw, hna, hb⟩
  | tail _ _ h ih =>
    obtain ⟨w0, wl, hf0, hwlk, hwl, hnal, hbl⟩ := ih
    obtain ⟨w, hf, hb⟩ := before_observed h
    obtain ⟨n, hn, hnw, hw, hna⟩ := observer_enables hv hg hf
    exact ⟨w0, w, hf0, hwlk.trans ((reach_notifier hg hv.tma.2.2.1 hok hwl hnal hbl hn).trans
      hnw).to_reflTransGen, hw, hna, hb⟩

/-- An observer of an operation's completion does not precede, in `hb`, the issue of the
operation (or of its notifying instruction). -/
private theorem observer_not_before (hv : EffectValidity L X)
    (hg : SyncGuarded L K X) (hok : GuardOk L X)
    (he : DepStepAcyclic L K X) {i w v : EvId} {p : AsyncCopy.Part}
    (hf : AsyncFinished L X i p w ∨ AsyncOnlyFinished X i p w)
    (hwv : Relation.ReflTransGen (DepStep L K X) (.thread w, true) (.thread v, true))
    (hv' : GuardSource K X v) (hna : ∀ m tx count sc, ¬ X.Arrive v m tx count true sc)
    (hb : baseCausality L X v i) : False := by
  obtain ⟨n, hn, hnw, -, -⟩ := observer_enables hv hg hf
  exact he _ (((reach_notifier hg hv.tma.2.2.1 hok hv' hna hb hn).trans hnw).trans_right hwv)

/-- Byte visibility with the endpoint condition of asynchronous-to-asynchronous edges dropped
(the composition through a thread instruction, and the chains of `AsyncChain`, need not
relate two operations of one CTA), and with causality in place of the proxy fence after an
MMA read's observed completion (`CompletionBefore.baseCausality`). Acyclicity is proved for this
  wider relation on the ordinary causality branches. Allocation-result edges end at reads and
  do not occur in the writer-to-writer relation used to choose read sources. -/
def ModelCausalityChain (L : Launch) (X : Execution)
    (l : Loc) : AsyncCopy.Ref → AsyncCopy.Ref → Prop
  | .async i p, .async j q => AsyncChain L X l (i, p) (j, q)
  | .async i p, .thread f => AsyncCovers X i p l ∧ ∃ w, AsyncFinished L X i p w ∧ baseCausality L X
      w f
  | .thread e, .thread f => baseCausality L X e f
  | e, f => modelCausality L X l e f

/-- An observed completion of an MMA read is base causality through its proxy fence; every other
part's observed completion already is base causality (`CompletionBefore`). -/
theorem completionBefore_baseCausality {l : Loc} {p : AsyncCopy.Part} {w f : EvId}
    (h : CompletionBefore L X l p w f) : baseCausality L X w f := by
  cases p with
  | mmaRead isB byte =>
    obtain ⟨fence, sp, -, -, -, -, -, h1, h2⟩ := h
    exact h1.trans h2
  | readCopy | readLoad _ _ _ | readStore _ _ _ | readCta _ | readElem _ | writeCopy
  | writeLoad _ _ _ | writeStore _ _ _ | writeCta _ | writeElem _ | oldCopy | oldLoad _ _ _
  | oldStore _ _ _ | oldCta _ | oldElem _ | notifyCopy | notifyLoad | notifyCta _
  | readPrefetch _ _ _ | writePrefetch _ _ _ | oldPrefetch _ _ _ | readsDone | fullDone | resolve
  | tcNotify _ | mmaDone | arriveOn => exact h

theorem observedCompletionBefore_baseCausality {l : Loc} {i w f : EvId}
    {p : AsyncCopy.Part} (h : ObservedCompletionBefore L X l i p w f) :
    baseCausality L X w f :=
  h.elim completionBefore_baseCausality (TcReadReuseBefore.base L)

private theorem allocResult_not_write {l : Loc} {e f : EvId} {a : Acc} {bs : List Byte}
    (h : Tmem.Pair.AllocResultBefore L X l e f) (hw : X.MemWrites (.thread f) a bs) :
    False := by
  obtain ⟨_, _, _, _, _, _, _, ⟨_, hload⟩, _⟩ := h
  rcases hw with ⟨_, hget⟩ | ⟨_, _, hget⟩ <;> rw [hload] at hget <;> cases hget

private theorem chain_or_allocResult {l : Loc} {e f : AsyncCopy.Ref}
    (h : modelCausality L X l e f) : ModelCausalityChain L X l e f ∨
      ∃ i j, e = .thread i ∧ f = .thread j ∧ Tmem.Pair.AllocResultBefore L X l i j := by
  cases e with
  | thread e =>
    cases f with
    | thread f =>
      exact h.elim Or.inl (fun hb => .inr ⟨e, f, rfl, rfl, hb⟩)
    | async i p => exact .inl h
  | async i p =>
    cases f with
    | thread f =>
      obtain ⟨hc, w, hfin, hcb⟩ := h
      exact .inl ⟨hc, w, hfin, observedCompletionBefore_baseCausality hcb⟩
    | async j q => exact .inl h.2

/-- Every visibility edge targeting a write belongs to the wider writer-order relation. -/
theorem modelCausality.chain_of_write {l : Loc} {e f : AsyncCopy.Ref} {a : Acc}
    {bs : List Byte} (h : modelCausality L X l e f) (hw : X.MemWrites f a bs) :
    ModelCausalityChain L X l e f := by
  rcases chain_or_allocResult h with hc | ⟨_, _, rfl, rfl, ha⟩
  · exact hc
  · exact (allocResult_not_write ha hw).elim

private theorem allocResult_not_reverse (hv : EffectValidity L X) (hc : ObjectCoherent L X)
    (he : DepStepAcyclic L K X) (hg : SyncGuarded L K X) (hok : GuardOk L X)
    {l : Loc} {store load : EvId} (ha : Tmem.Pair.AllocResultBefore L X l store load)
    (hb : modelCausality L X l (.thread load) (.thread store)) : False := by
  obtain ⟨j, dst, a, bytes, hlink, hj, hbyte, hrd, hrdByte⟩ := ha
  obtain ⟨out, hw⟩ := hlink.writes
  rcases hb with hbase | hr
  · have hfill : Tmem.Pair.AllocResultFill L X (load.1, j) (.thread store) := ⟨dst, hlink⟩
    obtain ⟨hwarp, hleader, _, _, k, site, group, count, _, _, hk, _, hpart, hkl, hkj, _⟩ :=
      hlink
    obtain ⟨tag, hget⟩ := hrd
    by_cases hlane : laneOf L load.1 = 0
    · have ht : store.1 = load.1 := Tmem.Pair.sameWarp_leader_eq hwarp hleader hlane
      rw [ht] at hkl
      have hind := hkl.unique hkj
      have hne : store ≠ load := by
        rintro rfl
        obtain ⟨_, hwrite⟩ := hw
        rw [hget] at hwrite
        cases hwrite
      have hlt : store.2 < load.2 := by
        have hidx : store.2 ≠ load.2 := fun h => hne (Prod.ext ht h)
        omega
      have hpo := po_of_overlap (X := X) (a := { loc := dst, size := 4 }) (b := a)
        (we := true) (wf := false) (.inr (.inl ⟨out, hw, rfl⟩))
        (.inl ⟨bytes, ⟨tag, hget⟩, rfl⟩) ht hlt ⟨l, hbyte, hrdByte⟩
      exact baseCausality_irrefl hc.cause (hbase.tail (.inl hpo))
    · have hnode := allocResult_witnessed L X (load.1, j) hpart hlane
      have hp := po_of_source_not_access (X := X) (e := (load.1, j)) (f := load)
        rfl hj (len_of_get hget)
        (show (X.get (load.1, j)).bind Event.acc = none by rw [hpart]; rfl)
      have hguard : GuardSource K X (load.1, j) := .inr ⟨_, false, hpart, rfl⟩
      have hn : ∀ m tx count sc, ¬ X.Arrive (load.1, j) m tx count true sc := by
        rintro m tx count sc ⟨_, h⟩
        rw [hpart] at h
        cases h
      have hr := baseCausality_enables hg hv.tma.2.2.1 hok hguard hn
        ((Relation.TransGen.single (.inl hp)).trans hbase)
      exact he _ (hr.tail (DepStep.of_witness L (Witness.of_need L hnode hfill.present hfill)))
  · exact allocResult_not_write hr (.inl hw)

/-- No cycle of length two in `ModelCausalityChain`, given guarded synchronization. Between thread
instructions it is causality; through an asynchronous operation it would make an observer
of the operation's completion enable the operation's own issue. -/
theorem modelCausalityChain_asymm_guarded (hv : EffectValidity L X) (hc : ObjectCoherent L X)
    (he : DepStepAcyclic L K X) (hg : SyncGuarded L K X)
    (hok : GuardOk L X) {e f : AsyncCopy.Ref} {l : Loc}
    (hf : X.RefPresent f) (h : ModelCausalityChain L X l e f)
        (h' : ModelCausalityChain L X l f e) : False := by
  cases e with
  | thread e =>
    cases f with
    | thread f => exact baseCausality_irrefl hc.cause (Relation.TransGen.trans h h')
    | async i p =>
      obtain ⟨-, hbefore⟩ := h
      obtain ⟨-, w, hfin, hwe⟩ := h'
      obtain ⟨hw, hna⟩ := observer_guard_source hg (.inl hfin)
      obtain ⟨fence, -, -, -, -, -, -, h1, h2⟩ | ⟨-, h2⟩ := hbefore
      · exact observer_not_before hv hg hok he (.inl hfin) .refl hw hna
          ((hwe.trans h1).trans h2)
      · exact observer_not_before hv hg hok he (.inl hfin) .refl hw hna (hwe.trans h2)
  | async i p =>
    cases f with
    | thread f =>
      obtain ⟨-, w, hfin, hwf⟩ := h
      obtain ⟨-, hbefore⟩ := h'
      obtain ⟨hw, hna⟩ := observer_guard_source hg (.inl hfin)
      obtain ⟨fence, -, -, -, -, -, -, h1, h2⟩ | ⟨-, h2⟩ := hbefore
      · exact observer_not_before hv hg hok he (.inl hfin) .refl hw hna
          ((hwf.trans h1).trans h2)
      · exact observer_not_before hv hg hok he (.inl hfin) .refl hw hna (hwf.trans h2)
    | async j q =>
      obtain ⟨w0, wl, hf0, hp, hwl, hnal, hbl⟩ :=
        chain_observers hv hg hok (AsyncChain.trans h hf h')
      exact observer_not_before hv hg hok he hf0 hp hwl hnal hbl

theorem modelCausality_asymm_guarded (hv : EffectValidity L X) (hc : ObjectCoherent L X)
    (he : DepStepAcyclic L K X) (hg : SyncGuarded L K X)
    (hok : GuardOk L X) {e f : AsyncCopy.Ref} {l : Loc}
    (hf : X.RefPresent f) (h : modelCausality L X l e f)
    (h' : modelCausality L X l f e) : False := by
  rcases chain_or_allocResult h with h | ⟨_, _, rfl, rfl, ha⟩
  · rcases chain_or_allocResult h' with h' | ⟨_, _, rfl, rfl, ha⟩
    · exact modelCausalityChain_asymm_guarded hv hc he hg hok hf h h'
    · exact allocResult_not_reverse hv hc he hg hok ha (.inl h)
  · exact allocResult_not_reverse hv hc he hg hok ha h'

theorem modelCausality_asymm {K : Kernel}
    (ht : EffectValidity L X) (hc : ObjectCoherent L X) (hen : DepStepAcyclic L K X)
    (hg : SyncGuarded L K X) (hok : GuardOk L X)
    {e f : AsyncCopy.Ref} {l : Loc}
    (hf : X.RefPresent f) (h : modelCausality L X l e f) : ¬ modelCausality L X l f e :=
  fun h' => modelCausality_asymm_guarded ht hc hen hg hok hf h h'

/-- A memory write is present: its thread instruction exists, or its asynchronous write stage is
recorded. -/
private theorem memWrites_present {X : Execution} {f : AsyncCopy.Ref} {b : Acc}
    {cs : List Byte} (h : X.MemWrites f b cs) : X.RefPresent f := by
  cases f with
  | thread e =>
    rcases h with ⟨pc, hget⟩ | ⟨old, pc, hget⟩
    · exact ⟨_, hget⟩
    · exact ⟨_, hget⟩
  | async i p =>
    cases p with
    | writeCopy =>
      obtain ⟨s, -, -, -, hb⟩ := h
      exact show (X.async.copies i).writeBytes.isSome from by rw [hb]; rfl
    | writeElem j =>
      obtain ⟨s, -, -, hb⟩ := h
      exact show ((X.async.copies i).elemWrites j).isSome from by rw [hb]; rfl
    | writeCta c =>
      obtain ⟨s, targets, -, -, hres⟩ := h
      exact hres.1
    | writeStore x y k =>
      obtain ⟨o, _, _, ho, _, _, hwb, _, _, _, _, _, _⟩ := h
      exact ⟨o, ho, by rw [hwb]; rfl⟩
    | writeLoad x y k =>
      obtain ⟨o, _, _, ho, _, _, hwb, _, _, _, _, _, _⟩ := h
      have hslot : ∃ slot value, TensorTransfer.slotAt o.spec.descriptor x y k = some slot ∧
          o.effects.write slot = some value := by
        unfold TensorCopy.writeByte at hwb
        cases hw : TensorTransfer.slotAt o.spec.descriptor x y k with
        | none => simp [hw] at hwb
        | some slot =>
          cases hwr : o.effects.write slot with
          | none => simp [hw, hwr] at hwb
          | some value => exact ⟨slot, value, rfl, hwr⟩
      obtain ⟨slot, value, hw, hwr⟩ := hslot
      exact ⟨o, slot, value, ho, hw, hwr⟩
    | _ => simp [Execution.MemWrites] at h

/-- Two actual writes cannot each be after the other at the same byte. -/
theorem writes_vis_asymm {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (hg : SyncGuarded L K X)
    {e f : AsyncCopy.Ref} {a b : Acc}
    {bs cs : List Byte} {l : Loc} (_he : X.MemWrites e a bs) (hf : X.MemWrites f b cs)
    (hef : modelCausality L X l e f) : ¬ modelCausality L X l f e :=
  modelCausality_asymm hX.effectValidity hX.object (DepStepAcyclic.of_dependency hX.dependency)
    hg hX.guardOk (memWrites_present hf) hef
end
end PTX
