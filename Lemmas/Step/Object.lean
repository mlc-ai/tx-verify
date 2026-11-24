-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.Issue
public import Lemmas.Snoc.SnocObjectPreserve
public import Lemmas.Snoc.SnocObjectHistory
public import Lemmas.Snoc.SnocObjectWaiting
public import Lemmas.Snoc.SnocWaitFrame
public import Lemmas.Snoc.ObjectAppend
public import Lemmas.Async.AsyncChain
public import Lemmas.Snoc.PlainExtend
public import Lemmas.Snoc.SnocAsync
public import Lemmas.Snoc.SnocAsyncSilent

@[expose] public section

/-! # Appending an mbarrier initialization or arrival

A proof tool. A thread whose last event is released can initialize or arrive on an mbarrier
object: the event is appended together with the object's checked record of it, the reply the
object's transition gives or its fault (`checkedRecord`), so no readiness premise is needed and
undefined behaviour of the object stays an execution for safety to reject. The record has a
fresh identity, so no old acquiring poll observes it, and a release arrival adds no
happens-before edge into an old event (`object_baseCausality_old`). An asynchronous-silent
object event also preserves old byte visibility (`object_counted_extension_silent`). The
safe-prefix form covers any object event in this class of checked appends
(`object_counted_extension`). -/

namespace PTX.Step
open PTX AsyncCopy MBarrier
noncomputable section

/-- The record of an action on an object: the transition's reply, or its fault. -/
def checkedRecord (id : Ref) (action : Action) (before : Option State) : Record Ref :=
  match perform before action with
  | .ok reply => ⟨id, action, reply, none⟩
  | .error fault => ⟨id, action, ⟨before, none, none⟩, some fault⟩

/-- A record of an action other than a poll replies no wait outcome. -/
theorem checkedRecord_waited {action : Action} (hnp : ∀ p ok, action ≠ .pollParity p ok)
    (id : Ref) (before : Option State) : (checkedRecord id action before).reply.waited = none := by
  unfold checkedRecord
  split
  · rename_i reply h
    revert h
    cases action with
    | pollParity p ok => exact absurd rfl (hnp p ok)
    | _ =>
      cases before <;> simp only [perform] <;> intro h <;> (try split_ifs at h) <;>
        simp_all [bind, Except.bind, pure, Except.pure, throw]
      all_goals rw [← h]
  · rfl

theorem checkedRecord_id (id : Ref) (action : Action) (before : Option State) :
    (checkedRecord id action before).id = id := by
  unfold checkedRecord
  split <;> rfl

theorem checkedRecord_action (id : Ref) (action : Action) (before : Option State) :
    (checkedRecord id action before).action = action := by
  unfold checkedRecord
  split <;> rfl

theorem checkedRecord_ok (id : Ref) (action : Action) (before : Option State) :
    RecordOk before (checkedRecord id action before) := by
  cases hp : perform before action <;> simp [RecordOk, checkedRecord, hp]

variable {L : Launch} {X : Execution} {g : Nat} {e : Event} {r : Nat → Option Ref}

/-- A new event's fresh identity has no record in an old history: a release it makes publishes
into no old wait. -/
theorem snoc_msync_old (hv : EffectValidity L X) {a b : EvId} (hbo : b.2 < (X.tr b.1).length)
    (h : MSync L (X.snoc g e r) a b) : MSync L X a b := by
  obtain ⟨x, w, m, rs, ws, ⟨tx, count, pc, hp⟩, ⟨⟨pcw, parity, hw⟩, hphase⟩, hsc, hwf, hwlt, _,
    hxe, hle⟩ := h
  have hxo : x.2 < (X.tr x.1).length := by
    rw [snoc_get] at hp
    split_ifs at hp with hx
    · obtain ⟨i, j, q, z, phase, hq, hid, _⟩ := hphase
      exact (snoc_fresh_object_id hv.tma (List.mem_of_getElem? hq)
        (hid.trans (congrArg Ref.thread hx))).elim
    · exact len_of_get hp
  have hwo : w.2 < (X.tr w.1).length := by rw [hwf]; omega
  exact ⟨x, w, m, rs, ws, ⟨tx, count, pc, by rwa [snoc_get_old hxo] at hp⟩,
    ⟨⟨pcw, parity, by rwa [snoc_get_old hwo] at hw⟩, hphase⟩, hsc, hwf, hwlt, hbo, hxe, hle⟩

/-- **An appended event that is no barrier, warp barrier or `fence.sc`, and that no old read reads
from, adds no causality into old events**, even a release arrival. -/
theorem snoc_baseCausality_old (hv : EffectValidity L X) (hcl : ClusterHistoryOk L X)
    (hnb : ∀ id count mode, e.kind ≠ .bar id count mode) (hwb : ∀ mask inst,
        e.kind ≠ .warpBar mask inst)
    (hold : SnocReadsOld X g e r) (hsc : ∀ s, e.kind ≠ .fence .sc s)
    {a b : EvId} (hbo : b.2 < (X.tr b.1).length) :
    baseCausality L (X.snoc g e r) a b ↔ baseCausality L X a b :=
  ⟨fun h => baseCausality_old_of_step (fun hb => snoc_step_old_of hcl hold
    (fun _ _ => snoc_ctaBarK hnb) (fun _ _ => snoc_ctaBarArrivalK hnb) hb
    (snoc_msync_old hv hb) (fun m i he => (hwb m i he).elim) hsc) h hbo, baseCausality_snoc⟩

/-- **An appended event that writes no memory and is no `fence.sc` starts no causality in the
plain append**, even a release arrival: its identity has no record in an old history, so no wait
observes it. -/
theorem snoc_no_baseCausality_from_new_object (ht : TmaOk X)
    (hwr : ∀ a bs, e.kind ≠ .wr a bs) (hrmw : ∀ a old new, e.kind ≠ .rmw a old new)
    (hsc : ∀ s, e.kind ≠ .fence .sc s) {f : EvId} :
    ¬ baseCausality L (X.snoc g e r) (g, (X.tr g).length) f := by
  have hnw : ∀ a bs, ¬ (X.snoc g e r).MemWrites (.thread (g, (X.tr g).length)) a bs := by
    intro a bs hw
    rcases hw with ⟨pc, hp⟩ | ⟨old, pc, hp⟩ <;> rw [snoc_get_new] at hp
    · exact hwr a bs (congrArg Event.kind (Option.some.inj hp))
    · exact hrmw a old _ (congrArg Event.kind (Option.some.inj hp))
  intro h
  obtain ⟨c, h1, _⟩ := Relation.TransGen.head'_iff.mp h
  rcases h1 with ⟨h1, h2, h3⟩ | ⟨_, k, i, j, hi, _, h4, _⟩ | hs | hc | hw | ha | hfs
  · simp only at h1 h2; rw [← h1, snoc_len, ite_eq_left rfl] at h3; omega
  · have hi' := hi.lt
    simp only [snoc_len, ↓reduceIte] at hi'; omega
  · obtain ⟨x, w, m, rs, ws, hr, ⟨-, hphase⟩, _, _, _, _, hx, hle⟩ := hs
    have hxl := hr.lt
    rw [snoc_len, ite_eq_left hx] at hxl
    have hxe : x = (g, (X.tr g).length) := Prod.ext hx (by simp only at hle; omega)
    obtain ⟨i, j, q, z, phase, hq, hid, _⟩ := hphase
    exact snoc_fresh_object_id ht (List.mem_of_getElem? hq) (hid.trans (congrArg Ref.thread hxe))
  · obtain ⟨_, i, j, _, hi, hlt, _⟩ := hc
    simp only [snoc_len, ↓reduceIte] at hi
    omega
  · obtain ⟨i, j, ⟨_, mask, inst, ⟨pc, hp⟩, _⟩, hi, _⟩ := hw
    have hh := len_of_get hp
    simp only [snoc_len, ↓reduceIte] at hh
    omega
  · obtain ⟨a, b, bs, cs, hw, -⟩ := ha
    exact hnw a bs hw
  · rcases hfs with
      ⟨w, rd, a, b, bs, cs, se, sf, hw, -, hsr, hrel, -⟩ | ⟨⟨s, -, ⟨pc, hp⟩, -, -⟩, -⟩
    · rcases hrel with ⟨rfl, -, -⟩ | ⟨sem, -, -, h1, h2⟩
      · exact hnw a bs hw
      · have hwl := memWrites_thread_lt hw
        simp only at h1 h2
        rw [snoc_len, ← h1, ite_eq_left rfl] at hwl
        omega
    · rw [snoc_get_new] at hp
      exact hsc s (congrArg Event.kind (Option.some.inj hp))

/-- The kinds that make an object action and are no poll: an initialization, an arrival, an
invalidation, a `cp.async.mbarrier.arrive` without `.noinc`. -/
def ObjectKind (k : Kind) : Prop :=
  (∃ m c, k = .mbInit m c) ∨ (∃ m tx c rel s, k = .arrive m tx c rel s) ∨
    (∃ m, k = .mbInval m) ∨ ∃ m, k = .asyncArrive m false

/-- An appended event that acts on an object and is no poll is of an object kind. -/
theorem objectKind_of_action {act : Action} {l : Loc}
    (hnw : ∀ m p ok ac scope, e.kind ≠ .wait m p ok ac scope)
    (h : objectAction (X.snoc g e r) X.async l (.thread (g, (X.tr g).length)) = some act) :
    ObjectKind e.kind := by
  simp only [objectAction, snoc_get_new] at h
  obtain ⟨pc, k⟩ := e
  cases k
  case mbInit m c => exact .inl ⟨m, c, rfl⟩
  case arrive m tx c rel s => exact .inr (.inl ⟨m, tx, c, rel, s, rfl⟩)
  case wait m p ok ac s => exact (hnw m p ok ac s rfl).elim
  case mbInval m => exact .inr (.inr (.inl ⟨m, rfl⟩))
  case asyncArrive m noinc =>
    cases noinc
    · exact .inr (.inr (.inr ⟨m, rfl⟩))
    · simp at h
  all_goals simp at h

/-- The kind facts of an object kind. -/
theorem ObjectKind.facts (h : ObjectKind e.kind) :
    e.kind ≠ .exit ∧ e.kind.laneValue = false ∧ isMatrix e = false ∧
      (∀ a old new, e.kind ≠ .rmw a old new) ∧ (∀ s, e.kind ≠ .fence .sc s) ∧
      (∀ s, e.kind ≠ .copy s) ∧ e.kind.resume = .free := by
  obtain ⟨pc, k⟩ := e
  rcases h with ⟨_, _, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ <;> simp only at h <;> subst h <;>
    exact ⟨fun h => Kind.noConfusion h, rfl, rfl, fun _ _ _ h => Kind.noConfusion h,
      fun _ h => Kind.noConfusion h, fun _ h => Kind.noConfusion h, rfl⟩

/-- An event that resumes freely has not returned. -/
theorem not_returned_of_free {Y : Execution} {i : EvId} (hres : e.kind.resume = .free)
    (hget : Y.get i = some e) : ¬ Returned Y i := by
  intro h
  unfold Returned at h
  rw [hget] at h
  obtain ⟨pc, k⟩ := e
  cases k
  case wait => simp [Kind.resume] at hres
  all_goals simp only [hres] at h

variable {mb : Loc} {record : Record Ref}

/-- A record of a new event other than a poll is observed by no acquiring poll. -/
theorem record_not_acquire (hnw : ∀ m p ok ac scope, e.kind ≠ .wait m p ok ac scope)
    (hid : record.id = .thread (g, (X.tr g).length)) {w : EvId} {m : Loc}
    (hw : (X.snoc g e r).AcquireWait w m) : record.id ≠ .thread w := by
  intro heq
  have heqw := Ref.thread.inj (hid.symm.trans heq)
  obtain ⟨pc, p, scope, hw⟩ := hw
  rw [← heqw, snoc_get_new] at hw
  exact hnw _ _ _ _ _ (congrArg Event.kind (Option.some.inj hw))

theorem object_baseCausality_old (hv : EffectValidity L X) (hcl : ClusterHistoryOk L X)
    (hid : record.id = .thread (g, (X.tr g).length))
    (hnb : ∀ id count mode, e.kind ≠ .bar id count mode) (hwb : ∀ mask inst,
        e.kind ≠ .warpBar mask inst)
    (hold : SnocReadsOld X g e r) (hsc : ∀ s, e.kind ≠ .fence .sc s)
    (hnw : ∀ m p ok ac scope, e.kind ≠ .wait m p ok ac scope)
    {a b : EvId} (hbo : b.2 < (X.tr b.1).length) :
    baseCausality L (X.snocObject g e r mb record) a b ↔ baseCausality L X a b := by
  change baseCausality L ((X.snoc g e r).appendObject mb record) a b ↔ _
  rw [appendObject_baseCausality_iff (fun _ _ hw => record_not_acquire hnw hid hw)]
  exact snoc_baseCausality_old hv hcl hnb hwb hold hsc hbo

theorem object_readOk {A : List Assumption} (hv : EffectValidity L X)
    (hr : TcMma.ReadOk L A X) (hcl : ClusterHistoryOk L X)
    (hid : record.id = .thread (g, (X.tr g).length)) (hk : ∀ k, e.kind ≠ .tc k)
    (hnb : ∀ id count mode, e.kind ≠ .bar id count mode) (hwb : ∀ mask inst,
        e.kind ≠ .warpBar mask inst)
    (hold : SnocReadsOld X g e r) (hsc : ∀ s, e.kind ≠ .fence .sc s)
    (hnw : ∀ m p ok ac scope, e.kind ≠ .wait m p ok ac scope) :
    TcMma.ReadOk L A (X.snocObject g e r mb record) := by
  have hlog : ∀ l, List.IsPrefix (X.objects l)
      ((fun l => if l = mb then X.objects mb ++ [record] else X.objects l) l) := by
    intro l
    by_cases hl : l = mb
    · subst l; exact ⟨[record], by simp⟩
    · simp [hl]
  refine (TcMma.ReadPreserved.readOk ⟨Execution.le_trans (le_snoc (X := X) (g := g) (e := e)
      (r := r)) (Execution.le_appendObject _ _ _),
      fun hf => ⟨(object_baseCausality_old hv hcl hid hnb hwb hold hsc hnw hf).mp,
      fun h => baseCausality_snoc_history
          (records := fun l => if l = mb then X.objects mb ++ [record]
        else X.objects l) hlog h⟩, fun hw => snocObject_observedMma_iff hv.tcCommit hid hw,
      fun _ _ h => h, fun _ _ hr => .inl hr, fun hw => snocObject_mbarExec_old hv.tma.2.2.1 hid hw,
      fun _ hq => .inl hq⟩
      hr hv.tma.2.1) ?_
  intro load address vals sh j source cell value ⟨pc, hl⟩ _ hnew _ _
  change (X.snoc g e r).get load = _ at hl
  rcases snoc_get_cases hl with ⟨rfl, he⟩ | ⟨hold, _⟩
  · exact (hk _ (by rw [← he])).elim
  · omega

/-- Appending a record no acquiring poll observes leaves every completion observation. -/
theorem object_finished_iff (hnw : ∀ w m, X.AcquireWait w m → record.id ≠ .thread w)
    {i w : EvId} {p : Part} :
    AsyncFinished L (X.appendObject mb record) i p w ↔ AsyncFinished L X i p w := by
  unfold AsyncFinished
  refine or_congr Iff.rfl (exists_congr fun _ => and_congr_left' ?_)
  by_cases hn : record.id ≠ .thread w
  · exact appendObject_asyncObserved_iff hn
  · exact ⟨fun ⟨_, _, _, hwo⟩ => (hn (hnw w _ hwo.acquireWait)).elim,
      fun ⟨_, _, _, hwo⟩ => (hn (hnw w _ hwo.acquireWait)).elim⟩

/-- Appending a record no acquiring poll observes leaves all byte visibility. -/
theorem object_modelCausality_iff (hnw : ∀ w m, X.AcquireWait w m → record.id ≠ .thread w)
    {l : Loc} {v w : Ref} :
    modelCausality L (X.appendObject mb record) l v w ↔ modelCausality L X l v w := by
  have hbiff : ∀ a b, baseCausality L (X.appendObject mb record) a b ↔ baseCausality L X a b :=
    fun _ _ => appendObject_baseCausality_iff hnw
  have hp : ∀ a b, ProxyBefore L (X.appendObject mb record) a b l ↔ ProxyBefore L X a b l := by
    intros
    unfold ProxyBefore
    simp only [hbiff]
    rfl
  have hd : ∀ a b, AsyncBefore L (X.appendObject mb record) l a b ↔ AsyncBefore L X l a b := by
    intros
    exact AsyncBefore.congr (L := L) (X := X.appendObject mb record) (Y := X) (l := l)
      (fun _ _ => Iff.rfl) (fun _ _ _ => object_finished_iff hnw)
      (fun _ _ _ => Iff.rfl) (fun _ _ _ _ => hbiff _ _) (fun _ _ _ _ => Iff.rfl)
  have hcb (i waiter f : EvId) (p : Part) :
      ObservedCompletionBefore L (X.appendObject mb record) l i p waiter f ↔
        ObservedCompletionBefore L X l i p waiter f :=
    observedCompletionBefore_congr rfl rfl (hbiff _ _) (hp _ _)
  cases v <;> cases w <;> simp only [modelCausality, hbiff, hp, object_finished_iff hnw, hcb]
  all_goals first | rfl | exact and_congr_right fun _ => AsyncChain.congr hd (fun _ _ => Iff.rfl)

private theorem object_counted_extension_core {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (hg : g < L.threads)
    (hne : X.tr g ≠ [] ∨ Step.Launched L X g) (hrel : Released L X g) {t t1 : TState}
    {o : Option TState}
    (hrun : Run K A L g {} (X.tr g) (some t)) (hl : Relation.ReflTransGen (Tau K A L g) t t1)
    (he : EStep K A L g t1 e o) (hw : e.kind.WaitFree) (hq : e.kind.Quiet)
    (hnb : ∀ id count mode, e.kind ≠ .bar id count mode)
    (hns : ∀ md a b c recv ok, e.kind ≠ .shfl md a b c recv ok)
    (hrd : ∀ a bs, e.kind ≠ .rd a bs) (hwr : ∀ a bs, e.kind ≠ .wr a bs)
    (hnw : ∀ m p ok ac scope, e.kind ≠ .wait m p ok ac scope) (hcnt : e.counts = true)
    {act : Action} (hnp : ∀ p ok, act ≠ .pollParity p ok)
    (hact : ∀ l, objectAction (X.snoc g e (fun _ => none)) X.async l
      (.thread (g, (X.tr g).length)) = if l = mb then some act else none)
    (hasm : ∀ rec : Record Ref, ∀ a ∈ A, a.wf L mem0 (X.snocObject g e (fun _ => none) mb rec))
    (hOld : e.kind.AsyncSilent ∨ ReadsOrdered L X ∧
      ∀ rec : Record Ref, rec.reply.waited = none →
        SyncGuarded L K (X.snocObject g e (fun _ => none) mb rec)) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hk := hw.notTc
  have hok : ObjectKind e.kind :=
    objectKind_of_action hnw (l := mb) (by rw [hact mb, ite_eq_left rfl])
  obtain ⟨hx, hlv, hmat, hrmw, hsc, hcp, hfree⟩ := hok.facts
  have hwb : ∀ mask inst, e.kind ≠ .warpBar mask inst := by
    intro mask inst h
    have := hw.ordinary
    rw [h] at this
    exact this
  have hbo : ∀ {x f : EvId}, f.2 < (X.tr f.1).length →
      (baseCausality L (X.snoc g e (fun _ => none)) x f ↔ baseCausality L X x f) := fun hf =>
    snoc_baseCausality_old hX.effectValidity hX.cluster hnb hwb (.of_rfWf hX.rf) hsc hf
  obtain ⟨last, hh⟩ := (hX.tma.2.2.1 mb).1.2
  let record := checkedRecord (.thread (g, (X.tr g).length)) act last
  have hid : record.id = .thread (g, (X.tr g).length) := checkedRecord_id ..
  have ha : record.action = act := checkedRecord_action ..
  have ho : ObjectsOk (X.snocObject g e (fun _ => none) mb record) := by
    apply snoc_objects_checked hX.effectValidity hk mb record hid
    · rw [ha]; exact hact
    · apply CheckedLog.snoc hh (hX.tma.2.2.1 mb).1.1
      · intro hmem
        obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hmem
        exact snoc_fresh_object_id hX.tma hq (hqe.trans hid)
      · exact checkedRecord_ok ..
    · intro p ok hp
      exact absurd (ha.symm.trans hp) (hnp p ok)
  let Y := X.snocObject g e (fun _ => none) mb record
  have hle : X.le Y := Execution.le_trans le_snoc (Execution.le_appendObject _ _ _)
  have htma : TmaOk Y := snocObject_tma hX.effectValidity hk ho
  have hextra : ExtensionObligations L A Y :=
    ExtensionObligations.snocObject_quiet hX hq hne hx
      (hX.tmemPairResult.snoc_not_wr fun _ _ _ h => hwr _ _ (congrArg Event.kind h))
      (readOk_snoc hX.tcRead hX.tcCommit hX.tma.2.2.1 hX.tma.2.1 hbo
        (by intro pc ta vals sh h; exact (hk _ (congrArg Event.kind h)).elim))
      (hX.atomic.snoc hX.store hX.tma.1 hrmw)
      (hX.fenceSc.snoc hsc fun _ _ hb h => (hbo hb).mp h)
      (hX.matrix.snoc hmat) (hX.reduce.snoc hcp)
      (object_readOk hX.effectValidity hX.tcRead hX.cluster hid hk hnb hwb (.of_rfWf hX.rf) hsc
        hnw)
      (snocObject_fenceScOk hX.fenceSc hsc fun _ _ hb h =>
        (object_baseCausality_old hX.effectValidity hX.cluster hid hnb hwb (.of_rfWf hX.rf) hsc
          hnw hb).mp h)
  have hframe : SnocWaitFrame L X g e (fun _ => none) :=
    ⟨hw, hns, fun j => snoc_new_not_witness hX hw hns (fun h => absurd h hx) hlv hmat
      (snoc_not_allocResult_of_not_wr hwr j),
      fun _ => snoc_no_baseCausality_from_new_object hX.tma hwr hrmw hsc⟩
  have hready : ∀ j, Returned Y j → Ready L Y j :=
    ready_snocHistory hX (SnocRecords.append hid) (fun h => by rw [hmat] at h; cases h)
      hrel.ready fun h => (not_returned_of_free hfree (by
        change (X.snoc g e (fun _ => none)).get (X.newId g) = _
        exact snoc_get_new) h).elim
  have hY : Consistent L K A mem0 Y := by
    have assemble
        (thr : ∀ j < L.threads, Produces K A L j (Y.tr j))
        (outside : ∀ j, L.threads ≤ j → Y.tr j = [])
        (read : ∀ v a bs, Y.MemReads v a bs → X.MemReads v a bs)
        (write : ∀ v a bs, Y.MemWrites v a bs → X.MemWrites v a bs)
        (liftWrite : ∀ v a bs, X.MemWrites v a bs → Y.MemWrites v a bs)
        (rf : ∀ v a bs, Y.MemReads v a bs → ∀ k, Y.rf v k = X.rf v k) :
        Consistent L K A mem0 Y := by
      have order := hframe.objectOrderOk hX mb record hid
      have shfl := snoc_shflOk (g := g) (r := fun _ => none) hX.shfl hns
      have asm := hasm record
      have happens {l v w} : modelCausality L Y l v w ↔
          modelCausality L (X.snoc g e (fun _ => none)) l v w :=
        object_modelCausality_iff (fun _ _ wait => record_not_acquire hnw hid wait)
      rcases hOld with silent | ⟨ordered, guarded⟩
      · apply consistent_preserving_extension hX hle thr outside read write liftWrite rf
          ?_ hready shfl order asm htma rfl hextra
        intro l v w hw
        exact (happens (l := l) (v := v) (w := w)).trans
          (silent.modelCausality_snoc_old hbo (snoc_allocResultBefore_old hX.dependency.ready)
            (refPresent_issuer_lt hX.effectValidity hw))
      · exact consistent_collective_extension_reads hX hle ordered thr outside read write
          liftWrite rf (fun _ _ _ h => happens.mpr (modelCausality_snoc_mono hX.tma.2.1 h))
          (fun _ _ _ _ _ _ hx hf h => ByteCausality.le_reflect hle hX.tma.2.1 hX.tcCommit
            (fun hf' h' => modelCausality_snoc_old_of hbo hX.effectValidity
              (refPresent_issuer_lt hX.effectValidity hx) hf' (happens.mp h'))
            (fun hw' h' => (snocObject_observedMma_iff hX.tcCommit hid hw').mp h')
            (refPresent_issuer_lt hX.effectValidity hf) h)
          hready shfl order (guarded record (checkedRecord_waited hnp ..)) asm htma rfl hextra
    apply assemble
    · intro h hh
      by_cases hhg : h = g
      · subst hhg
        refine ⟨o, ?_⟩
        change Run K A L h {} ((X.snoc h e (fun _ => none)).tr h) o
        rw [snoc_tr, ite_eq_left rfl]; exact hrun.snoc hl he
      · change Produces K A L h ((X.snoc g e (fun _ => none)).tr h)
        rw [snoc_tr, ite_eq_right hhg]; exact hX.thr h hh
    · intro h hh
      change (X.snoc g e (fun _ => none)).tr h = []
      rw [snoc_tr, ite_eq_right (by omega)]; exact hX.outside h hh
    · intro v a bs hv
      exact (snoc_memReads_control (g := g) (e := e) (r := fun _ => none) hX.effectValidity hk
        hrd hrmw).mp hv
    · intro v a bs hv
      exact (snoc_memWrites_control (g := g) (e := e) (r := fun _ => none) hX.effectValidity
        hwr hrmw).mp hv
    · intro v a bs hv
      exact (snoc_memWrites_control (g := g) (e := e) (r := fun _ => none) hX.effectValidity
        hwr hrmw).mpr hv
    · intro v a bs hv k
      have hold := (snoc_memReads_control (g := g) (e := e) (r := fun _ => none)
        hX.effectValidity hk hrd hrmw).mp hv
      exact (le_snoc (X := X) (g := g) (e := e) (r := fun _ => none)).2.1 v k ⟨a, bs, hold⟩
  refine ⟨Y, hY, hle, ?_⟩
  change X.size L < (X.snoc g e (fun _ => none)).size L
  rw [size_snoc hX hg hcnt]
  omega

/-- **A released thread performs an mbarrier event that is no poll**, with the object's checked
record of it: a counted extension of a prefix whose conflicts at read bytes are ordered. -/
theorem object_counted_extension_reads {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (hord : ReadsOrdered L X) (hg : g < L.threads)
    (hne : X.tr g ≠ [] ∨ Step.Launched L X g) (hrel : Released L X g) {t t1 : TState}
    {o : Option TState}
    (hrun : Run K A L g {} (X.tr g) (some t)) (hl : Relation.ReflTransGen (Tau K A L g) t t1)
    (he : EStep K A L g t1 e o) (hw : e.kind.WaitFree) (hq : e.kind.Quiet)
    (hnb : ∀ id count mode, e.kind ≠ .bar id count mode)
    (hns : ∀ md a b c recv ok, e.kind ≠ .shfl md a b c recv ok)
    (hrd : ∀ a bs, e.kind ≠ .rd a bs) (hwr : ∀ a bs, e.kind ≠ .wr a bs)
    (hnw : ∀ m p ok ac scope, e.kind ≠ .wait m p ok ac scope) (hcnt : e.counts = true)
    {act : Action} (hnp : ∀ p ok, act ≠ .pollParity p ok)
    (hact : ∀ l, objectAction (X.snoc g e (fun _ => none)) X.async l
      (.thread (g, (X.tr g).length)) = if l = mb then some act else none)
    (hasm : ∀ rec : Record Ref, ∀ a ∈ A, a.wf L mem0 (X.snocObject g e (fun _ => none) mb rec))
    (hsg : ∀ rec : Record Ref, rec.reply.waited = none →
      SyncGuarded L K (X.snocObject g e (fun _ => none) mb rec)) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L :=
  object_counted_extension_core hX hg hne hrel hrun hl he hw hq hnb hns
    hrd hwr hnw hcnt hnp hact hasm (.inr ⟨hord, hsg⟩)

/-- An object event that issues and awaits no asynchronous operation preserves the constraints
on all previously recorded reads. Its checked record gives a counted extension. -/
theorem object_counted_extension_silent {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (hsilent : e.kind.AsyncSilent)
    (hg : g < L.threads)
    (hne : X.tr g ≠ [] ∨ Step.Launched L X g) (hrel : Released L X g) {t t1 : TState}
    {o : Option TState}
    (hrun : Run K A L g {} (X.tr g) (some t)) (hl : Relation.ReflTransGen (Tau K A L g) t t1)
    (he : EStep K A L g t1 e o) (hw : e.kind.WaitFree) (hq : e.kind.Quiet)
    (hnb : ∀ id count mode, e.kind ≠ .bar id count mode)
    (hns : ∀ md a b c recv ok, e.kind ≠ .shfl md a b c recv ok)
    (hrd : ∀ a bs, e.kind ≠ .rd a bs) (hwr : ∀ a bs, e.kind ≠ .wr a bs)
    (hnw : ∀ m p ok ac scope, e.kind ≠ .wait m p ok ac scope) (hcnt : e.counts = true)
    {act : Action} (hnp : ∀ p ok, act ≠ .pollParity p ok)
    (hact : ∀ l, objectAction (X.snoc g e (fun _ => none)) X.async l
      (.thread (g, (X.tr g).length)) = if l = mb then some act else none)
    (hasm : ∀ rec : Record Ref, ∀ a ∈ A, a.wf L mem0 (X.snocObject g e (fun _ => none) mb rec))
    : ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L :=
  object_counted_extension_core hX hg hne hrel hrun hl he hw hq hnb hns
    hrd hwr hnw hcnt hnp hact hasm (.inl hsilent)

/-- `object_counted_extension_reads` for a safe prefix. -/
theorem object_counted_extension {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    (hX : Consistent L K A mem0 X) (hm : ¬ Mixed L X) (hr : ¬ Race L X) (hst : StrongOrdered L X)
      (hg : g < L.threads)
    (hne : X.tr g ≠ [] ∨ Step.Launched L X g) (hrel : Released L X g) {t t1 : TState}
    {o : Option TState}
    (hrun : Run K A L g {} (X.tr g) (some t)) (hl : Relation.ReflTransGen (Tau K A L g) t t1)
    (he : EStep K A L g t1 e o) (hw : e.kind.WaitFree) (hq : e.kind.Quiet)
    (hnb : ∀ id count mode, e.kind ≠ .bar id count mode)
    (hns : ∀ md a b c recv ok, e.kind ≠ .shfl md a b c recv ok)
    (hrd : ∀ a bs, e.kind ≠ .rd a bs) (hwr : ∀ a bs, e.kind ≠ .wr a bs)
    (hnw : ∀ m p ok ac scope, e.kind ≠ .wait m p ok ac scope) (hcnt : e.counts = true)
    {act : Action} (hnp : ∀ p ok, act ≠ .pollParity p ok)
    (hact : ∀ l, objectAction (X.snoc g e (fun _ => none)) X.async l
      (.thread (g, (X.tr g).length)) = if l = mb then some act else none)
    (hasm : ∀ rec : Record Ref, ∀ a ∈ A, a.wf L mem0 (X.snocObject g e (fun _ => none) mb rec))
    (hsg : ∀ rec : Record Ref, rec.reply.waited = none →
      SyncGuarded L K (X.snocObject g e (fun _ => none) mb rec)) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L :=
  object_counted_extension_reads hX (.of_safe hm hr hst) hg hne hrel hrun hl he hw
    hq hnb hns hrd hwr hnw hcnt hnp hact hasm hsg

end
end PTX.Step
