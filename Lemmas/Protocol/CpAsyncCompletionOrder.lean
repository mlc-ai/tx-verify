-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Order.CommitOperandFrame
public import Lemmas.Tmem.AllocResult

public import Lemmas.Protocol.CpAsyncCompletion
public import Lemmas.Step.CopyFinishWaiting
public import Lemmas.Async.AsyncChain
public import Lemmas.Step.Drain
public import Lemmas.Step.WfInOrder
public import Lemmas.Tcgen05.MmaCompletionGrowth
public import Lemmas.Tcgen05.TcMmaReadMono

@[expose] public section

namespace PTX

open AsyncCopy MBarrier

noncomputable section

variable {L : Launch} {X : Execution} {i : EvId} {rs bs : List Byte}

local notation "copyDone" => X.finishCpAsync i rs bs

/-- Completing the ordinary copy preserves the sources of all thread instructions. -/
theorem finishCpAsync_baseCausality_iff {e f : EvId} :
    baseCausality L copyDone e f ↔ baseCausality L X e f := by
  have hbase : ∀ a b,
      (po copyDone a b ∨ CtaBarSync L copyDone a b ∨ MSync L copyDone a b ∨
        ClusterSync L copyDone a b ∨
        WarpBarSync L copyDone a b ∨ synchronizesWith L copyDone a b ∨ FenceSync L copyDone a b) ↔
      (po X a b ∨ CtaBarSync L X a b ∨ MSync L X a b ∨ ClusterSync L X a b ∨
        WarpBarSync L X a b ∨ synchronizesWith L X a b ∨ FenceSync L X a b) := by
    intro a b
    have hs : synchronizesWith L copyDone a b ↔ synchronizesWith L X a b := by
      simp [synchronizesWith, Execution.MemWrites, Execution.MemReads, Execution.Rmw,
        Execution.Writes, Execution.Reads, Execution.get, Execution.finishCpAsync]
    have hf : FenceSync L copyDone a b ↔ FenceSync L X a b := by
      simp [FenceSync, FenceScSync, StrongRead, ScStrong, ReleaseHead, AcquireTail,
        Execution.MemWrites, Execution.Rmw, Execution.Writes, Execution.Reads,
        Execution.ThreadFence, Execution.get, Execution.finishCpAsync]
    rw [hs, hf]
    rfl
  constructor <;> intro h
  · induction h with
    | single h => exact .single ((hbase _ _).mp h)
    | tail _ h ih => exact ih.tail ((hbase _ _).mp h)
  · induction h with
    | single h => exact .single ((hbase _ _).mpr h)
    | tail _ h ih => exact ih.tail ((hbase _ _).mpr h)

theorem finishCpAsync_asyncPresent_of_ne {j : EvId} (hj : j ≠ i) {p : Part} :
    (copyDone).AsyncPresent j p ↔ X.AsyncPresent j p := by
  cases p <;> simp only [Execution.AsyncPresent, Execution.MmaRead, Execution.finishCpAsync,
    ite_eq_right hj]
  all_goals rfl

theorem finishCpAsync_asyncObserved_iff {j w : EvId} {p : Part} {acq : Bool} {ws : MbarScope} :
    AsyncObserved copyDone j p w acq ws ↔ AsyncObserved X j p w acq ws := by
  suffices ∀ n loc, Notifies copyDone j p n loc ↔ Notifies X j p n loc by
    simp only [AsyncObserved, this]
    rfl
  intro n loc
  suffices ∀ j, ((copyDone).async.copies j).notified = (X.async.copies j).notified by
    cases p <;> try rfl
    all_goals (simp only [Notifies, NotifyOn, Notification, this]; rfl)
  intro k
  by_cases hk : k = i <;> simp [Execution.finishCpAsync, hk]

theorem finishCpAsync_groupWaitPresent_iff (hno : ∀ k w, ¬ GroupWaitsFor X k i w)
    {k : GroupWait} {j w : EvId} :
    (GroupWaitsFor X k j w ∧ ∀ q ∈ GroupWaitStages X j k, (copyDone).AsyncPresent j q) ↔
      (GroupWaitsFor X k j w ∧ ∀ q ∈ GroupWaitStages X j k, X.AsyncPresent j q) := by
  apply and_congr_right
  intro hw
  by_cases hj : j = i
  · subst j
    exact (hno k w hw).elim
  · simp only [finishCpAsync_asyncPresent_of_ne hj]

theorem finishCpAsync_asyncFinished_iff (hno : ∀ k w, ¬ GroupWaitsFor X k i w)
    {j w : EvId} {p : Part} :
    AsyncFinished L copyDone j p w ↔ AsyncFinished L X j p w := by
  unfold AsyncFinished
  simp only [finishCpAsync_asyncObserved_iff]
  exact or_congr_left (exists_congr fun _ => and_congr_right fun _ =>
    finishCpAsync_groupWaitPresent_iff hno)

theorem finishCpAsync_asyncOnlyFinished_iff (hno : ∀ k w, ¬ GroupWaitsFor X k i w)
    {j w : EvId} {p : Part} :
    AsyncOnlyFinished copyDone j p w ↔ AsyncOnlyFinished X j p w := by
  unfold AsyncOnlyFinished
  exact and_congr_right fun _ => finishCpAsync_groupWaitPresent_iff
    (k := .bulk .asyncProxy) (j := j) (w := w) hno

theorem pendingCpAsync_not_notified {s : Spec} (hi : X.Copy i s)
    (hc : s.completion = .asyncGroup) (h : WellFormed (issuedBy X) X.async) :
    (X.async.copies i).notified = false := by
  cases hn : (X.async.copies i).notified
  · rfl
  · obtain ⟨s', hi', hok⟩ := h i ⟨.notify .copy, by simp [present, hn]⟩
    have hspec := (issuedBy_some.mp hi').unique hi
    subst s'
    obtain ⟨_, hcomp⟩ := (hok.2.2.2.1 hn).1
    rw [hc] at hcomp
    cases hcomp

/-- A pending write has no observing wait before the group wait or tracking arrive-on. -/
theorem pendingCpAsync_not_finished {s : Spec} (hi : X.Copy i s) (hc : s.completion = .asyncGroup)
    (ht : TmaOk X) (hn : (X.async.copies i).writeBytes = none)
    (hno : ∀ k w, ¬ GroupWaitsFor X k i w) {p : Part}
    (hp : p = .read .copy ∨ p = .write .copy) (w : EvId) :
    ¬ AsyncFinished L X i p w := by
  rintro (⟨k, _, hw, _⟩ | ⟨ws, ⟨n, m, hnot, _⟩, _⟩)
  · exact hno k w hw
  · have hnot' : (n = .async i (.notify .copy) ∧ NotifyOn X i .copy m) ∨
        ∃ j noinc, n = .async j .arriveOn ∧ TracksCpAsync X i j ∧ X.AsyncArrive j m noinc ∧
          X.async.arrived j = true := by
      rcases hp with rfl | rfl <;> exact hnot
    rcases hnot' with ⟨_, _, _, _, hdone, _⟩ | ⟨j, _, _, ht', _, hdone⟩
    · rw [pendingCpAsync_not_notified hi hc ht.1] at hdone
      cases hdone
    · rw [no_arriveOn_tracks_pending_copy ht.2.2.2 hn ht'] at hdone
      cases hdone

theorem finishCpAsync_asyncBefore_iff (hno : ∀ k w, ¬ GroupWaitsFor X k i w)
    {l : Loc} {a b : EvId × Part} :
    AsyncBefore L copyDone l a b ↔ AsyncBefore L X l a b := by
  exact AsyncBefore.congr (L := L) (X := copyDone) (Y := X)
    (fun _ _ => Iff.rfl)
    (fun _ _ _ => finishCpAsync_asyncFinished_iff hno)
    (fun _ _ _ => finishCpAsync_asyncOnlyFinished_iff hno)
    (fun _ _ _ _ => finishCpAsync_baseCausality_iff) (fun _ _ _ _ => Iff.rfl)

theorem finishCpAsync_asyncPresent_on_edge {s : Spec} (hi : X.Copy i s)
    (hc : s.completion = .asyncGroup) (ht : TmaOk X) (hn : (X.async.copies i).writeBytes = none)
    (hno : ∀ k w, ¬ GroupWaitsFor X k i w) {l : Loc} {a b : EvId × Part}
    (hedge : AsyncBefore L copyDone l a b) :
    (copyDone).AsyncPresent a.1 a.2 ↔ X.AsyncPresent a.1 a.2 := by
  rcases a with ⟨j, p⟩
  by_cases hj : j = i
  · subst j
    have h := (finishCpAsync_asyncBefore_iff hno).mp hedge
    have hnf : ∀ w, (p = .read .copy ∨ p = .write .copy) →
        ¬ AsyncFinished L X i p w := fun w hp => pendingCpAsync_not_finished hi hc ht hn hno hp w
    rcases h.2.2 with ⟨w, hf, -⟩ | ⟨w, ho, -⟩
    · cases p <;> first
      | rfl
      | (simp [Execution.AsyncPresent, Execution.finishCpAsync]; done)
      | exact (hnf w (by simp) hf).elim
    · exact (hno _ w ho.2.1).elim
  · exact finishCpAsync_asyncPresent_of_ne hj

theorem finishCpAsync_modelCausality_iff {s : Spec} (hi : X.Copy i s)
    (hc : s.completion = .asyncGroup) (ht : TmaOk X) (hn : (X.async.copies i).writeBytes = none)
    (hno : ∀ k w, ¬ GroupWaitsFor X k i w) {l : Loc} {e f : Ref} :
    modelCausality L copyDone l e f ↔ modelCausality L X l e f := by
  have hp : ∀ e j, ProxyBefore L copyDone e j l ↔ ProxyBefore L X e j l := by
    intro e j
    simp only [ProxyBefore, finishCpAsync_baseCausality_iff]
    rfl
  cases e with
  | thread e =>
    cases f with
    | thread f =>
      exact or_congr finishCpAsync_baseCausality_iff (Tmem.Pair.AllocResultBefore.iff_of_tr rfl)
    | async j p => simp only [modelCausality, hp, finishCpAsync_baseCausality_iff]; rfl
  | async j p =>
    cases f with
    | thread f =>
      have hCompletion (w : EvId) :
          ObservedCompletionBefore L copyDone l j p w f ↔
            ObservedCompletionBefore L X l j p w f :=
        observedCompletionBefore_congr (X := X) (Y := copyDone)
          rfl rfl (finishCpAsync_baseCausality_iff) (hp w f)
      simp only [modelCausality, finishCpAsync_asyncFinished_iff hno, hCompletion]
      rfl
    | async k q =>
      exact and_congr_right fun _ =>
        AsyncChain.congr_on_edges (fun _ _ => finishCpAsync_asyncBefore_iff hno)
          (fun _ _ => finishCpAsync_asyncPresent_on_edge hi hc ht hn hno)

theorem pendingCpAsync_write_not_visible {s : Spec} (hi : X.Copy i s)
    (hc : s.completion = .asyncGroup) (ht : TmaOk X) (hn : (X.async.copies i).writeBytes = none)
    (hno : ∀ k w, ¬ GroupWaitsFor X k i w) {l : Loc} {e : Ref} :
    ¬ modelCausality L X l (.async i (.write .copy)) e := by
  have hfin := pendingCpAsync_not_finished (L := L) hi hc ht hn hno (Or.inr rfl)
  cases e with
  | thread e => rintro ⟨_, w, hf, _⟩; exact hfin w hf
  | async j p =>
    intro h
    obtain ⟨_, edge⟩ := AsyncChain.first h.2
    rcases edge.2.2 with ⟨w, hf, _⟩ | ⟨w, ho, _⟩
    · exact hfin w hf
    · exact hno _ w ho.2.1


theorem finishCpAsync_present_old {e : Ref} (he : ¬ CopyRef i e) :
    (copyDone).RefPresent e ↔ X.RefPresent e := by
  cases e with
  | thread j => rfl
  | async j p =>
    by_cases hj : j = i
    · subst j
      cases p <;> try rfl
      all_goals
        first
        | (simp [Execution.RefPresent, Execution.AsyncPresent, Execution.finishCpAsync]; done)
        | exact (he ⟨_, rfl, by simp [CopyPart]⟩).elim
    · exact finishCpAsync_asyncPresent_of_ne hj

theorem finishCpAsync_needs (ho : ObjectsOk X) (hn : (X.async.copies i).notified = false)
    (e : EvId) : Needs L copyDone e = Needs L X e := by
  refine needs_congr (X := X) (Y := copyDone) (fun _ => rfl)
    (fun k _ hk => by
      cases k <;> first | rfl | exact (hk _ _ _ _ _ rfl).elim | (rename_i t; cases t <;> rfl))
    (fun e m => pollNeeds_congr (X := X) (Y := copyDone) (fun _ => rfl) (fun m r hr w => ?_) e m) e
  apply and_congr _ Iff.rfl
  apply finishCpAsync_present_old
  rintro ⟨p, hp, hcp⟩
  exact unnotified_no_copy_record ho hn hcp hr hp

theorem finishCpAsync_no_witness (ho : ObjectsOk X) (hn : (X.async.copies i).notified = false)
    (hno : ∀ k w, ¬ GroupWaitsFor X k i w) {p : Part} (hp : CopyPart p) {w : EvId} :
    ¬ Witness L copyDone (.async i p) w := by
  rintro ⟨fills, hneed, -, hf⟩
  rw [finishCpAsync_needs ho hn] at hneed
  rcases needs_node_fills hneed hf with ⟨t, ht⟩ | ⟨m, r, hr, hrid⟩ | ⟨k, j, q, hw, hjq⟩
  · cases ht
  · exact unnotified_no_copy_record ho hn hp hr hrid.symm
  · cases hjq
    exact hno k w hw

theorem finishCpAsync_copy_no_before (ho : ObjectsOk X)
    (hn : (X.async.copies i).notified = false) {p : Part} (hp : CopyPart p)
    {m : Loc} {f : Ref} : ¬ Before ((copyDone).objects m) (.async i p) f := by
  rintro ⟨a, b, ra, rb, ha, hid, hb, _, hab⟩
  have ha' : (X.objects m)[a]? = some ra := ha
  exact unnotified_no_copy_record ho hn hp (List.mem_of_getElem? ha') hid

private theorem finishCpAsync_copy_stageEdge {s : Spec} (hi : X.Copy i s)
    (hw : s.writes = .whole) (_hc : s.completion = .asyncGroup)
    (ht : TmaOk X) (hn : (X.async.copies i).writeBytes = none)
    {p : Part} (hp : CopyPart p) {f : Ref} (h : StageEdge copyDone (.async i p) f) :
    ∃ q, f = .async i q ∧ CopyPart q ∧ copyStageRank p < copyStageRank q := by
  have he : ∀ k, ¬ (copyDone).AsyncPresent i (.write (.elem k)) := by
    intro k
    have hnone := (elems_none_of_whole ht.1 (issuedBy_some.mpr hi) hw k).1
    simp [Execution.AsyncPresent, Execution.finishCpAsync, hnone]
  rcases hp with rfl | rfl | rfl
  all_goals unfold StageEdge at h
  all_goals split at h
  all_goals try (rename_i heq; cases heq)
  all_goals first
    | exact h.elim
    | (obtain ⟨rfl, hk⟩ := h; exact (he _ hk.2).elim)
    | (obtain ⟨rfl, rfl, -⟩ := h
       exact ⟨_, rfl, by simp [CopyPart], by simp [copyStageRank]⟩)
    | (obtain ⟨rfl, ht, -⟩ := h
       obtain rfl : _ = Target.copy := by simpa [AsyncCopy.Part.target] using ht.symm
       exact ⟨_, rfl, by simp [CopyPart], by simp [copyStageRank]⟩)
    | (obtain ⟨htracks, -, hdone⟩ := h
       have htracks' : TracksCpAsync X i _ := htracks
       have hdone' : X.async.arrived _ = true := hdone
       rw [no_arriveOn_tracks_pending_copy ht.2.2.2 hn htracks'] at hdone'
       cases hdone')

private theorem finishCpAsync_waits_from_copy {s : Spec} (hi : X.Copy i s)
    (hw : s.writes = .whole) (hc : s.completion = .asyncGroup) (ht : TmaOk X)
    (hn : (X.async.copies i).writeBytes = none) (hno : ∀ k w, ¬ GroupWaitsFor X k i w)
    {p : Part} (hp : CopyPart p) {b : Bool} {v : Ref × Bool}
    (h : Waits L copyDone (.async i p, b) v) :
    ∃ q c, v = (.async i q, c) ∧ CopyPart q ∧ copyNodeRank p b < copyNodeRank q c := by
  have hnot := pendingCpAsync_not_notified hi hc ht.1
  rcases h with ⟨he, hb, hb', _⟩ | ⟨_, _, j, k, he, _⟩ |
    ⟨j, k, he, _⟩ | ⟨_, _, j, k, he, _⟩ | ⟨_, _, j, k, he, _⟩ |
    ⟨hb, hb', hs⟩ | ⟨_, _, loc, ho'⟩ | ⟨j, k, he, _⟩ |
    ⟨_, _, j, hf, hwit⟩ | ⟨_, _, j, k, he, _⟩ |
    ⟨_, _, j, k, he, _⟩ | ⟨j, k, he, _⟩ | ⟨_, _, j, k, he, _⟩ | ⟨_, _, j, k, he, _⟩ |
    ⟨_, _, hi'⟩
  · exact ⟨p, true, Prod.ext he.symm hb', hp, by simp [copyNodeRank, hb]⟩
  all_goals try cases he
  · rcases hs with ⟨-, hb2, -⟩ | ⟨-, -, hs⟩
    · rw [hb] at hb2; cases hb2
    · obtain ⟨q, hq, hcq, hlt⟩ := finishCpAsync_copy_stageEdge hi hw hc ht hn hp hs
      refine ⟨q, false, Prod.ext hq hb', hcq, ?_⟩
      simp only [copyNodeRank, hb, ↓reduceIte, Bool.false_eq_true]
      omega
  · exact (finishCpAsync_copy_no_before ht.2.2.1 hnot hp ho').elim
  · exact (finishCpAsync_no_witness ht.2.2.1 hnot hno hp hwit).elim
  · obtain ⟨-, -, j, q, he, -⟩ := hi'
    cases he

theorem finishCpAsync_sinkFrame {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) {s : Spec} (hi : X.Copy i s)
    (hw : s.writes = .whole) (hc : s.completion = .asyncGroup)
    (hn : (X.async.copies i).writeBytes = none) (hno : ∀ k w, ¬ GroupWaitsFor X k i w) :
    SinkFrame L K A X copyDone (fun n => CopyRef i n.1) := by
  have hnot := pendingCpAsync_not_notified hi hc hX.tma.1
  have hclosed : ∀ u v, Waits L copyDone u v → CopyRef i u.1 →
      CopyRef i v.1 ∧ copyRank u < copyRank v := by
    rintro ⟨e, b⟩ v h ⟨p, rfl, hp⟩
    obtain ⟨q, c, rfl, hq, hlt⟩ := finishCpAsync_waits_from_copy hi hw hc hX.tma hn hno hp h
    exact ⟨⟨q, rfl, hq⟩, hlt⟩
  have hpres : ∀ {e : Ref}, ¬ CopyRef i e → (copyDone).RefPresent e → X.RefPresent e :=
    fun he h => (finishCpAsync_present_old he).mp h
  have hstage : ∀ u v, ¬ CopyRef i u.1 → ¬ CopyRef i v.1 → StageOrder copyDone u v →
      StageOrder X u v := fun u v hu hv h =>
    StageOrder.transfer (X := X) (Y := copyDone)
      (fun _ _ h => h) (fun _ _ h => h) (hpres hu) (hpres hv) h
  have hcaus : ∀ u v, ¬ CopyRef i u.1 → ¬ CopyRef i v.1 →
      stageCausality L copyDone u v → Relation.TransGen (stageCausality L X) u v := by
    rintro ⟨e, b⟩ ⟨f, b'⟩ hu hv (h | ⟨h1, h2, j, k, h3, h4, h⟩ |
      ⟨h1, h2, k, h3, c, p, w, ws, h5, h6, h7, h8⟩)
    · exact .single (Or.inl (hstage _ _ hu hv h))
    · exact .single (Or.inr (Or.inl ⟨h1, h2, j, k, h3, h4, finishCpAsync_baseCausality_iff.mp h⟩))
    · exact .single (Or.inr (Or.inr
        ⟨h1, h2, k, h3, c, p, w, ws, h5, h6, finishCpAsync_asyncObserved_iff.mp h7, h8⟩))
  refine ⟨⟨copyRank, hclosed⟩, hcaus, ?_, fun _ _ _ _ _ h => h, fun _ _ _ _ _ h => h,
    ?_, ?_, fun m j p y h => (hX.asyncObject m j p y h).1, fun _ _ _ _ _ _ h => h,
    ?_, fun _ _ => rfl⟩
  · intro x w hx _ h
    rcases h with ⟨hm, rest⟩ | ⟨j, p, k, q, rfl, h2, h3, h4, h5⟩
    · exact .inl ⟨⟨hpres hx hm.1, hm.2⟩, rest⟩
    · exact .inr ⟨j, p, k, q, rfl, h2, hpres hx h3, h4, h5⟩
  · rintro ⟨e, b⟩ ⟨f, b'⟩ hu hv (h | h | ⟨h1, h2, j, hj, fills, hf, hpres', hfill⟩ | h)
    · exact .single (Or.inl (hstage _ _ hu hv h))
    · exact .single (Or.inr (Or.inl
        (IssueStage.transfer (X := X) (Y := copyDone) (fun _ => rfl) (hpres hv) h)))
    · rw [finishCpAsync_needs hX.tma.2.2.1 hnot] at hf
      exact .single (Or.inr (Or.inr (Or.inl ⟨h1, h2, j, hj, fills, hf, hpres hu hpres', hfill⟩)))
    · exact .single (Or.inr (Or.inr (Or.inr h)))
  · rintro m j p y _ ⟨q, h, _⟩
    cases h
  · intro m init w y hs ht
    have hnoThread (j : EvId) (b : Bool) : ¬ CopyRef i ((.thread j, b) : Ref × Bool).1 := by
      rintro ⟨p, h, _⟩
      cases h
    exact hX.initFence m init w y hs
      (SinkFrame.old_path hclosed (fun _ _ h => stageCausality.waits h) hcaus ht
        (hnoThread _ _)).2


theorem finishCpAsync_reads {spec : Spec} (hi : issuedBy X i = some spec)
    {e : Ref} {a : Acc} {bytes : List (Option Byte)}
    (hr : (copyDone).MemReads e a bytes) :
    (e = .async i (.read .copy) ∧ a = spec.src ∧ bytes = rs.map some) ∨ X.MemReads e a bytes := by
  cases e with
  | thread j => exact .inr hr
  | async j p =>
    cases p <;> simp only [Execution.MemReads] at hr ⊢
    all_goals try exact Or.inr hr
    · obtain ⟨s, raw, hb, hsa, hraw, rfl⟩ := hr
      by_cases hj : j = i
      · subst j
        have hspec : s = spec := Execution.Copy.unique (X := X) hb (issuedBy_some.mp hi)
        subst s
        have he : raw = rs := by
          simpa [Execution.finishCpAsync] using hraw.symm
        exact .inl ⟨rfl, hsa.symm, by rw [he]⟩
      · refine .inr ⟨s, raw, hb, hsa, ?_, rfl⟩
        simpa [Execution.finishCpAsync,
          hj] using hraw
    · obtain ⟨s, r, raw, hb, hw, he, ho, rfl⟩ := hr
      refine .inr ⟨s, r, raw, hb, hw, he, ?_, rfl⟩
      by_cases hj : j = i
      · subst j
        simpa [Execution.finishCpAsync] using ho
      · simpa [Execution.finishCpAsync,
          hj] using ho

theorem finishCpAsync_writes {spec : Spec} (hi : issuedBy X i = some spec)
    {e : Ref} {a : Acc} {bytes : List Byte}
    (hw : (copyDone).MemWrites e a bytes) :
    (e = .async i (.write .copy) ∧ a = spec.dst ∧ bytes = bs) ∨ X.MemWrites e a bytes := by
  cases e with
  | thread j => exact .inr hw
  | async j p =>
    cases p <;> simp only [Execution.MemWrites] at hw ⊢
    all_goals try exact Or.inr hw
    · obtain ⟨s, hb, hwh, hd, hraw⟩ := hw
      by_cases hj : j = i
      · subst j
        have hspec : s = spec := Execution.Copy.unique (X := X) hb (issuedBy_some.mp hi)
        subst s
        exact .inl ⟨rfl, hd.symm, by
          simpa [Execution.finishCpAsync] using hraw.symm⟩
      · refine .inr ⟨s, hb, hwh, hd, ?_⟩
        simpa [Execution.finishCpAsync,
          hj] using hraw
    · obtain ⟨s, hb, he, hraw⟩ := hw
      refine .inr ⟨s, hb, he, ?_⟩
      by_cases hj : j = i
      · subst j
        simpa [Execution.finishCpAsync] using hraw
      · simpa [Execution.finishCpAsync,
          hj] using hraw


/-- The completion uses the source bytes of launch memory and preserves old read sources. -/
theorem finishCpAsync_initial_rf {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {spec : Spec} (hX : Consistent L K A mem0 X) (hi : issuedBy X i = some spec)
    (hle : X.le (X.finishCpAsync i (initialBytes mem0 X spec.src) bs)) :
    RfWf mem0 (X.finishCpAsync i (initialBytes mem0 X spec.src) bs) := by
  intro e a bs hr
  rcases finishCpAsync_reads hi hr with ⟨rfl, rfl, rfl⟩ | hold
  · refine ⟨by simp [initialBytes], ?_⟩
    intro k hk
    simp only [Execution.finishCpAsync]
    rw [ite_eq_left ⟨True.intro, by simpa [initialBytes] using hk⟩]
    intro c hinit
    simp [initialBytes, List.getElem?_range hk, hinit, Execution.initialByte]
  · obtain ⟨hn, hs⟩ := hX.rf e a bs hold
    refine ⟨hn, ?_⟩
    intro k hk
    rw [hle.2.1 e k ⟨a, bs, hold⟩]
    cases hf : X.rf e k with
    | none =>
      have hh := hs k hk
      simp only [hf] at hh ⊢
      exact hh
    | some w =>
      have hh := hs k hk
      rw [hf] at hh
      obtain ⟨dst, raw, hw, hc, hv⟩ := hh
      exact ⟨dst, raw, Execution.le_memWrites hle hw, hc, hv⟩

theorem finishCpAsync_initial_noFuture {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {spec : Spec} (hX : Consistent L K A mem0 X) (hi : issuedBy X i = some spec)
    (hc : spec.completion = .asyncGroup) (hn : (X.async.copies i).writeBytes = none)
    (hno : ∀ k w, ¬ GroupWaitsFor X k i w)
    (hle : X.le (X.finishCpAsync i (initialBytes mem0 X spec.src) bs)) :
    NoFuture L (X.finishCpAsync i (initialBytes mem0 X spec.src) bs) := by
  have hcopy := issuedBy_some.mp hi
  intro e a readBytes k w hr hk hf hv
  rcases finishCpAsync_reads hi hr with ⟨rfl, rfl, rfl⟩ | hold
  · simp [Execution.finishCpAsync, initialBytes, hk] at hf
  · rw [hle.2.1 e k ⟨a, readBytes, hold⟩] at hf
    exact hX.noFuture e a readBytes k w hold hk hf
      (ByteCausality.of_same_context (X := X)
        (Y := X.finishCpAsync i (initialBytes mem0 X spec.src) bs) rfl rfl
        (fun h => (finishCpAsync_modelCausality_iff hcopy hc hX.tma hn hno).mp h) (fun h => h) hv)

theorem finishCpAsync_initial_hidden {L : Launch} {K : Kernel} {A : List Assumption}
    {mem0 : Mem0} {spec : Spec} (hX : Consistent L K A mem0 X) (hi : issuedBy X i = some spec)
    (hc : spec.completion = .asyncGroup) (hn : (X.async.copies i).writeBytes = none)
    (hno : ∀ k w, ¬ GroupWaitsFor X k i w)
    (hsource : ∀ k < spec.src.size, ∀ w target bytes, X.MemWrites w target bytes →
      ¬ target.Covers (spec.src.loc.at k))
    (hle : X.le (X.finishCpAsync i (initialBytes mem0 X spec.src) bs)) :
    Hidden L (X.finishCpAsync i (initialBytes mem0 X spec.src) bs) := by
  have hcopy := issuedBy_some.mp hi
  intro e a bytes k w target raw hr hk hw hcover hv
  have reflect {l e f} :
      ByteCausality L (X.finishCpAsync i (initialBytes mem0 X spec.src) bs) l e f →
      ByteCausality L X l e f :=
    ByteCausality.of_same_context (X := X)
      (Y := X.finishCpAsync i (initialBytes mem0 X spec.src) bs) rfl rfl
      (fun h => (finishCpAsync_modelCausality_iff hcopy hc hX.tma hn hno).mp h) (fun h => h)
  have hv' := reflect hv
  rcases finishCpAsync_writes hi hw with ⟨rfl, _, _⟩ | hwrite
  · obtain ⟨_, edge⟩ := hv'.starts
    exact (pendingCpAsync_write_not_visible hcopy hc hX.tma hn hno edge).elim
  rcases finishCpAsync_reads hi hr with ⟨rfl, rfl, rfl⟩ | hread
  · exact (hsource k hk w target raw hwrite hcover).elim
  · rw [hle.2.1 e k ⟨a, bytes, hread⟩]
    have hh := hX.hidden e a bytes k w target raw hread hk hwrite hcover hv'
    cases hf : X.rf e k with
    | none => simp only [hf] at hh
    | some w' =>
      rw [hf] at hh
      intro hvis
      exact hh (reflect hvis)


theorem finishCpAsync_atomicOk (h : AtomicOk L X) : AtomicOk L copyDone := by
  have hcp : ∀ j k, ((copyDone).async.copies j).elemWrites k = (X.async.copies j).elemWrites k := by
    intro j k
    by_cases hj : j = i <;> simp [Execution.finishCpAsync, hj]
  refine atomicOk_congr (X := X) (Y := copyDone) (fun p l n => ?_)
    (fun _ _ => rmwStrong_congr rfl rfl) (fun p k => ?_) h
  · cases p
    · rfl
    · rfl
    · simp only [Execution.RmwAt, hcp]
      rfl
  · cases p <;> simp [Execution.oldRf, Execution.finishCpAsync]

private theorem finishCpAsync_tcRead {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (hle : X.le copyDone) : TcMma.ReadOk L A copyDone := by
  refine (TcMma.ReadPreserved.readOk ⟨hle,
    fun _ => finishCpAsync_baseCausality_iff, fun _ => finishCpAsync_asyncObserved_iff,
    fun _ _ h => h, fun _ _ h => .inl h, fun _ => Iff.rfl, fun _ h => .inl h⟩
    hX.tcRead hX.tma.2.1) ?_
  intro load address vals sh j source cell value ⟨pc, hl⟩ _ hnew _
  have := len_of_get (X := X) hl
  omega

/-- Complete an ordinary whole copy from its launch source. The program's group-wait discipline
ensures that the new stages cannot change the result of an earlier observation. -/
theorem consistent_finishCpAsync_initial {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) {spec : Spec} (hi : issuedBy X i = some spec)
    (hc : spec.completion = .asyncGroup) (hw : spec.writes = .whole) (hd : spec.data = none)
    (hn : (X.async.copies i).writeBytes = none) (hno : ∀ k w, ¬ GroupWaitsFor X k i w)
    (hsize : spec.src.size ≤ spec.dst.size)
    (hsource : ∀ k < spec.src.size, ∀ w target bytes, X.MemWrites w target bytes →
      ¬ target.Covers (spec.src.loc.at k))
    (hbs : bs = initialBytes mem0 X spec.src ++ List.replicate
      (spec.dst.size - spec.src.size) zeroByte)
    (hle : X.le (X.finishCpAsync i (initialBytes mem0 X spec.src) bs))
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.finishCpAsync i (initialBytes mem0 X spec.src) bs)) :
    Consistent L K A mem0 (X.finishCpAsync i (initialBytes mem0 X spec.src) bs) := by
  let read := initialBytes mem0 X spec.src
  have hcopy := issuedBy_some.mp hi
  have horder := (finishCpAsync_sinkFrame (rs := read) (bs := bs) hX hcopy hw hc hn hno).orderOk
    hX.orderOk
  exact {
    thr := hX.thr, outside := hX.outside, ctaBar := hX.ctaBar, cluster := hX.cluster
    shfl := hX.shfl, vote := hX.vote, warpValue := hX.warpValue, matrix := hX.matrix
    elect := hX.elect, warpBar := hX.warpBar
    rf := finishCpAsync_initial_rf hX hi hle
    dependency := {
      ready := fun e hr n hneed => by
        rw [finishCpAsync_needs hX.tma.2.2.1 (pendingCpAsync_not_notified hcopy hc hX.tma.1)]
          at hneed
        have h := hX.dependency.ready e hr n hneed
        cases n with
        | cond holds => exact h
        | node fills =>
          obtain ⟨ref, hpres, hf⟩ := h
          have hnew : (X.finishCpAsync i read bs).RefPresent ref := by
            by_cases href : CopyRef i ref
            · obtain ⟨p, rfl, rfl | rfl | rfl⟩ := href
              · simp [Execution.RefPresent, Execution.AsyncPresent, Execution.finishCpAsync]
              · simp [Execution.RefPresent, Execution.AsyncPresent, Execution.finishCpAsync]
              · simpa [Execution.RefPresent, Execution.AsyncPresent, Execution.finishCpAsync]
                  using hpres
            · exact (finishCpAsync_present_old href).mpr hpres
          exact ⟨ref, hnew, hf⟩
      acyclic := horder.depAcyclic }
    observation := horder.observation, object := horder.object
    asyncObject := horder.asyncObject, initFence := horder.initFence
    noFuture := finishCpAsync_initial_noFuture hX hi hc hn hno hle
    hidden := finishCpAsync_initial_hidden hX hi hc hn hno hsource hle
    tma := finishCpAsync_tmaOk hX.tma hle hi hw hd hc hsize (by simp [initialBytes]) hbs
    clc := hX.clc, tensor := hX.tensor, store := hX.store
    reduce := ⟨hX.reduce.values, fun j s r k v hcopy' hr hs hv => by
      by_cases hj : j = i
      · subst j
        rw [Execution.Copy.unique (X := X) hcopy' hcopy, hw] at hr
        cases hr
      · have he : ((X.finishCpAsync i read bs).async.copies j) = X.async.copies j := by
          simp [Execution.finishCpAsync, hj]
        rw [he] at hs hv ⊢
        exact hX.reduce.copies j s r k v hcopy' hr hs hv⟩
    atomic := finishCpAsync_atomicOk hX.atomic
    fenceSc := ⟨hX.fenceSc.total, hX.fenceSc.acyclic, fun e f hs hb =>
      hX.fenceSc.causal e f hs (finishCpAsync_baseCausality_iff.mp hb)⟩
    tmemPair := hX.tmemPair, tmemPairResult := hX.tmemPairResult
    tmemPairCompletion := Tmem.Pair.completionClosed_of_trace rfl rfl rfl hX.tmemPairCompletion
    tcCommit := hX.tcCommit
    mmaCompletion := TcMma.completionClosed_of_trace hX.mmaCompletion rfl rfl
    tcRead := finishCpAsync_tcRead hX hle
    asm := hasm }

/-- Any pending ordinary copy with an immutable source extends the execution by a counted
read/write completion. This includes a zero-length source, which needs no allocated source byte. -/
theorem pending_cpAsync_extendsInOrder {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    {sel : Nat → Bool} (hA : Assumption.WfStep sel L K mem0 A) (hX : Consistent L K A mem0 X)
    {spec : Spec} (hi : X.Copy i spec) (hc : spec.completion = .asyncGroup)
    (hw : spec.writes = .whole) (hd : spec.data = none)
    (hn : (X.async.copies i).writeBytes = none) (hno : ∀ k w, ¬ GroupWaitsFor X k i w)
    (hsize : spec.src.size ≤ spec.dst.size)
    (ha : ∀ k < spec.src.size, mem0 (spec.src.loc.at k) ≠ none)
    (hsource : ∀ k < spec.src.size, ∀ w target bytes, X.MemWrites w target bytes →
      ¬ target.Covers (spec.src.loc.at k)) :
    ∃ Z, Consistent L K A mem0 Z ∧ X.le Z ∧ X.size L < Z.size L := by
  have hle := finishCpAsync_initial_extends hX hi hw hd ha hsource
  obtain ⟨pc, he⟩ := hi
  obtain ⟨hg, hidx⟩ := issuer_thread hX he
  exact ⟨_, consistent_finishCpAsync_initial hX (issuedBy_some.mpr ⟨pc, he⟩) hc
    hw hd hn hno hsize hsource rfl hle
      (hA _ _ hX hle (Execution.notifiedInOrder_of_eq rfl) (Execution.noNewRead_of_tr rfl)), hle,
    finishCpAsync_size hle hg hidx hn⟩


/-- Complete an ordinary copy when the assumptions impose no execution constraints. -/
theorem pending_cpAsync_extends {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hA : Assumption.WfFree L mem0 A) (hX : Consistent L K A mem0 X)
    {spec : Spec} (hi : X.Copy i spec) (hc : spec.completion = .asyncGroup)
    (hw : spec.writes = .whole) (hd : spec.data = none)
    (hn : (X.async.copies i).writeBytes = none) (hno : ∀ k w, ¬ GroupWaitsFor X k i w)
    (hsize : spec.src.size ≤ spec.dst.size)
    (ha : ∀ k < spec.src.size, mem0 (spec.src.loc.at k) ≠ none)
    (hsource : ∀ k < spec.src.size, ∀ w target bytes, X.MemWrites w target bytes →
      ¬ target.Covers (spec.src.loc.at k)) :
    ∃ Z, Consistent L K A mem0 Z ∧ X.le Z ∧ X.size L < Z.size L :=
  pending_cpAsync_extendsInOrder (sel := fun _ => false) (fun _ Y _ _ _ _ a h => hA a h Y)
    hX hi hc hw hd hn hno hsize ha hsource

/-- A maximal execution cannot leave an ordinary whole copy with an available source pending. -/
theorem Maximal.cpAsync_written {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hA : Assumption.WfFree L mem0 A) (hX : Maximal L K A mem0 X)
    {spec : Spec} (hi : X.Copy i spec) (hc : spec.completion = .asyncGroup)
    (hw : spec.writes = .whole) (hd : spec.data = none)
    (hno : ∀ k w, ¬ GroupWaitsFor X k i w) (hsize : spec.src.size ≤ spec.dst.size)
    (ha : ∀ k < spec.src.size, mem0 (spec.src.loc.at k) ≠ none)
    (hsource : ∀ k < spec.src.size, ∀ w target bytes, X.MemWrites w target bytes →
      ¬ target.Covers (spec.src.loc.at k)) :
    ∃ bytes, (X.async.copies i).writeBytes = some bytes := by
  cases hn : (X.async.copies i).writeBytes with
  | none =>
    exact (hX.not_grows (pending_cpAsync_extends hA hX.1 hi hc hw hd hn hno hsize ha hsource)).elim
  | some bytes => exact ⟨bytes, rfl⟩

end

end PTX
