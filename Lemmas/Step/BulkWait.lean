-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.Released
public import Lemmas.Snoc.ExtensionSnoc
public import Lemmas.Snoc.ExtensionSnocFrame
public import Lemmas.Snoc.SnocConsistent
public import Lemmas.Snoc.SnocAsyncSilent
public import Lemmas.Snoc.SnocPlainWaiting
public import Lemmas.Snoc.SnocVisibility
public import Lemmas.Tcgen05.TcExtend
public import Lemmas.Async.BulkExecution

@[expose] public section

/-! # Appending a bulk-group wait

A proof tool. A thread whose last event is released can append a bulk-group wait: the execution
with the wait appended is consistent and strictly larger (`bulk_wait_counted_extension`). The wait
adds no memory access and no visibility into an old event. It blocks until the stages of the
operations it covers are present (`groupNeeds`, DEP-ORDER), but while it is the last event of its
thread it has not returned, so this obligation is the readiness of the thread's last event when
the thread's next event is appended (`Released`). -/

namespace PTX.Step.BulkWait
open PTX AsyncCopy MBarrier
noncomputable section

def BulkShape : Kind → Prop
  | .bulkCommit | .bulkWait .. => True
  | _ => False

theorem BulkShape.ordinary {k : Kind} (h : BulkShape k) : k.Ordinary := by
  cases k <;> simp_all [BulkShape, Kind.Ordinary]

section
variable {L : Launch} {X : Execution} {g : Nat} {e : Event}
  {r : Nat → Option Ref} {l : Loc} {K : Kernel} {A : List Assumption} {mem0 : Mem0}

theorem ne_kind {k : Kind} (hc : BulkShape e.kind) (hn : ¬BulkShape k) : e.kind ≠ k := by
  intro he
  apply hn
  simpa only [← he] using hc

theorem snoc_copy (hc : BulkShape e.kind) {i : EvId} {s : Spec} :
    (X.snoc g e r).Copy i s ↔ X.Copy i s :=
  snoc_kind_iff (ne_kind hc (by simp [BulkShape]))

theorem snoc_asyncArrive (hc : BulkShape e.kind) {i : EvId} {m : Loc} {noinc : Bool} :
    (X.snoc g e r).AsyncArrive i m noinc ↔ X.AsyncArrive i m noinc :=
  snoc_kind_iff (ne_kind hc (by simp [BulkShape]))

theorem snoc_bulkPrefetch (hc : BulkShape e.kind) {i : EvId} {a : Acc} :
    (X.snoc g e r).BulkPrefetch i a ↔ X.BulkPrefetch i a :=
  snoc_kind_iff (ne_kind hc (by simp [BulkShape]))

theorem snoc_tracksCpAsync (hc : BulkShape e.kind) {i j : EvId} :
    TracksCpAsync (X.snoc g e r) i j ↔ TracksCpAsync X i j := by
  simp only [TracksCpAsync, snoc_copy hc, snoc_asyncArrive hc]

theorem snoc_genericCopy (hc : BulkShape e.kind) {i : EvId} :
    GenericCopy (X.snoc g e r) i ↔ GenericCopy X i := by
  simp only [GenericCopy, snoc_copy hc]

theorem snoc_commit (hc : BulkShape e.kind) {i : EvId} {s : TcCommit.Spec} :
    (X.snoc g e r).Commit i s ↔ X.Commit i s := snoc_kind_iff (ne_kind hc (by simp [BulkShape]))

theorem snoc_issuedBy (hc : BulkShape e.kind) :
    issuedBy (X.snoc g e r) = issuedBy X := by
  funext i
  unfold issuedBy
  rw [snoc_get]
  split_ifs with hi
  · subst i
    obtain ⟨pc, kind⟩ := e
    cases kind <;> simp_all [BulkShape, Execution.get]
  · rfl

theorem snoc_mmaIssue (hc : BulkShape e.kind) {i : EvId} {d : Nat}
    {spec : TcMma.OperandSpec} {accum : Bool} {mask : List Nat} :
    (X.snoc g e r).MmaIssue i d spec accum mask ↔ X.MmaIssue i d spec accum mask :=
  snoc_kind_iff (ne_kind hc (by simp [BulkShape]))

theorem snoc_cpIssue (hc : BulkShape e.kind) {i : EvId} {c : TcCopy.Spec} :
    (X.snoc g e r).CpIssue i c ↔ X.CpIssue i c :=
  snoc_kind_iff (ne_kind hc (by simp [BulkShape]))

theorem snoc_shiftIssue (hc : BulkShape e.kind) {i : EvId} {c : TcShift.Spec} :
    (X.snoc g e r).ShiftIssue i c ↔ X.ShiftIssue i c :=
  snoc_kind_iff (ne_kind hc (by simp [BulkShape]))

theorem snoc_mmaRead (hc : BulkShape e.kind) {i : EvId} {isB : Bool}
    {k : Nat} {l : Loc} {b : Option Byte} :
    (X.snoc g e r).MmaRead i isB k l b ↔ X.MmaRead i isB k l b := by
  simp only [Execution.MmaRead, Execution.MmaFootprint, snoc_mmaIssue hc, snoc_cpIssue hc,
    snoc_async]

theorem snoc_tensorIssue (hc : BulkShape e.kind) {i : EvId} {addr : Nat}
    {spec : TensorCopy.Spec} :
    (X.snoc g e r).TensorIssue i addr spec ↔ X.TensorIssue i addr spec :=
  snoc_kind_iff (ne_kind hc (by simp [BulkShape]))

theorem snoc_storeIssue (hc : BulkShape e.kind) {i : EvId} {addr : Nat}
    {spec : TensorStore.Spec} :
    (X.snoc g e r).TensorStoreIssue i addr spec ↔ X.TensorStoreIssue i addr spec :=
  snoc_kind_iff (ne_kind hc (by simp [BulkShape]))

theorem snoc_prefetchIssue (hc : BulkShape e.kind) {i : EvId} {addr : Nat}
    {spec : TensorPrefetch.Spec} :
    (X.snoc g e r).TensorPrefetchIssue i addr spec ↔ X.TensorPrefetchIssue i addr spec :=
  snoc_kind_iff (ne_kind hc (by simp [BulkShape]))

theorem snoc_clcIssue (hc : BulkShape e.kind) {i : EvId} {spec : Clc.Spec}
    {targets : List Nat} :
    (X.snoc g e r).ClcIssue i spec targets ↔ X.ClcIssue i spec targets :=
  snoc_kind_iff (ne_kind hc (by simp [BulkShape]))

theorem snoc_asyncPresent (hc : BulkShape e.kind) {i : EvId} {p : Part} :
    (X.snoc g e r).AsyncPresent i p ↔ X.AsyncPresent i p := by
  cases p <;> simp only [Execution.AsyncPresent, snoc_mmaRead hc, snoc_async]
  all_goals rfl

theorem snoc_tracksMma (hc : BulkShape e.kind) {i j : EvId} :
    TracksMma (X.snoc g e r) i j ↔ TracksMma X i j := by
  simp only [TracksMma, Execution.TcAsync, snoc_mmaIssue hc, snoc_cpIssue hc,
    snoc_shiftIssue hc, snoc_commit hc]

theorem snoc_waitObserves (hc : BulkShape e.kind) {x : Ref} {w : EvId} {m : Loc}
    {ws : MbarScope} :
    WaitObserves (X.snoc g e r) x w m true ws ↔ WaitObserves X x w m true ws := by
  have hw (parity : Nat) :
      (∃ pc, (X.snoc g e r).get w = some ⟨pc, .wait m parity true true ws⟩) ↔
      ∃ pc, X.get w = some ⟨pc, .wait m parity true true ws⟩ :=
        snoc_kind_iff (ne_kind hc (by simp [BulkShape]))
  unfold WaitObserves
  rw [exists_comm, exists_comm (p := fun pc parity => X.get w =
    some ⟨pc, .wait m parity true true ws⟩)]
  simp only [hw]
  rfl

theorem snoc_intent_async (hc : BulkShape e.kind) {i : EvId} {p : AsyncCopy.Part}
    {a : Acc} {w : Bool} :
    (X.snoc g e r).Intent (.async i p) a w ↔ X.Intent (.async i p) a w := by
  cases p <;> simp only [Execution.Intent, AsyncCopy.Part.writes, Execution.AsyncFootprint,
    and_false, snoc_copy hc, snoc_bulkPrefetch hc, Execution.MmaFootprint, snoc_mmaIssue hc,
    snoc_cpIssue hc, snoc_tensorIssue hc, snoc_storeIssue hc, snoc_prefetchIssue hc,
    snoc_clcIssue hc]

theorem snoc_asyncCovers (hc : BulkShape e.kind) {i : EvId} {p : AsyncCopy.Part} {l : Loc} :
    AsyncCovers (X.snoc g e r) i p l ↔ AsyncCovers X i p l := by
  simp only [AsyncCovers, snoc_intent_async hc]

theorem snoc_memReads (hc : BulkShape e.kind) {i : AsyncCopy.Ref} {a : Acc}
    {bs : List (Option Byte)} :
    (X.snoc g e r).MemReads i a bs ↔ X.MemReads i a bs := by
  cases i with
  | thread i =>
    exact or_congr (snoc_kind_iff (ne_kind hc (by simp [BulkShape])))
      (exists_congr fun n => snoc_kind_iff (ne_kind hc (by simp [BulkShape])))
  | async i p =>
    cases p <;> simp only [Execution.MemReads, snoc_copy hc, snoc_mmaRead hc,
      snoc_tensorIssue hc, snoc_storeIssue hc, snoc_async]
    all_goals rfl

theorem snoc_memWrites (hc : BulkShape e.kind) {i : AsyncCopy.Ref} {a : Acc}
    {bs : List Byte} :
    (X.snoc g e r).MemWrites i a bs ↔ X.MemWrites i a bs := by
  cases i with
  | thread i =>
    exact or_congr (snoc_kind_iff (ne_kind hc (by simp [BulkShape])))
      (exists_congr fun o => snoc_kind_iff (ne_kind hc (by simp [BulkShape])))
  | async i p =>
    cases p <;> simp only [Execution.MemWrites, snoc_copy hc, snoc_tensorIssue hc,
      snoc_storeIssue hc, snoc_clcIssue hc, snoc_async]
    all_goals rfl

theorem snoc_asyncObserved (hc : BulkShape e.kind) {i w : EvId} {p : AsyncCopy.Part}
    {ws : MbarScope} :
    AsyncObserved (X.snoc g e r) i p w true ws ↔ AsyncObserved X i p w true ws := by
  cases p <;> simp only [AsyncObserved, Notifies, AsyncCopy.Part.target, AsyncCopy.NotifyOn,
    Notification, snoc_waitObserves hc, snoc_issuedBy hc, snoc_tensorIssue hc, snoc_clcIssue hc,
    snoc_tracksMma hc, snoc_commit hc, snoc_tracksCpAsync hc, snoc_asyncArrive hc, snoc_async]
  all_goals rfl

/-- A group wait other than the appended event covers the operations it covers in `X`. -/
theorem groupWaits_except_new (hc : BulkShape e.kind) {k : GroupWait} {i w : EvId}
    (hn : w ≠ (g, (X.tr g).length)) :
    GroupWaitsFor (X.snoc g e r) k i w ↔ GroupWaitsFor X k i w := by
  cases k with
  | bulk mode =>
    constructor
    · rintro ⟨pc, n, hget, hobs⟩
      have hx : X.get w = some ⟨pc, .bulkWait mode n⟩ := by
        rwa [snoc_get, ite_eq_right hn] at hget
      exact ⟨pc, n, hx, by simpa only [bulkStateBefore, snoc_take (len_of_get hx).le] using hobs⟩
    · rintro ⟨pc, n, hget, hobs⟩
      exact ⟨pc, n, Execution.le_get le_snoc hget,
        by simpa only [bulkStateBefore, snoc_take (len_of_get hget).le] using hobs⟩
  | cpAsync =>
    constructor
    · rintro ⟨pc, n, hp, hst⟩
      obtain ⟨pc, hp'⟩ := (snoc_kind_iff (X := X) (g := g) (r := r) (v := w)
        (ne_kind (k := .asyncWait n) hc (by simp [BulkShape]))).mp ⟨pc, hp⟩
      refine ⟨pc, n, hp', ?_⟩
      simpa only [asyncStateBefore, snoc_take (len_of_get hp').le] using hst
    · rintro ⟨pc, n, hp, hst⟩
      refine ⟨pc, n, Execution.le_get le_snoc hp, ?_⟩
      simpa only [asyncStateBefore, snoc_take (len_of_get hp).le] using hst

theorem finished_at_old (hc : BulkShape e.kind) {i w : EvId} {p : Part}
    (hw : w.2 < (X.tr w.1).length) :
    AsyncFinished L (X.snoc g e r) i p w → AsyncFinished L X i p w := by
  have hn : w ≠ (g, (X.tr g).length) := by rintro rfl; simp at hw
  rintro (⟨k, hv, hgw, hs⟩ | ⟨ws, ho, hsc⟩)
  · have hgw' := (groupWaits_except_new hc hn).mp hgw
    rw [snoc_groupWaitStages_old (groupWaitsFor_issuer hgw')] at hs
    exact .inl ⟨k, hv, hgw', fun q hq => (snoc_asyncPresent hc).mp (hs q hq)⟩
  · exact .inr ⟨ws, (snoc_asyncObserved hc).mp ho, hsc⟩

theorem onlyFinished_at_old (hc : BulkShape e.kind) {i w : EvId} {p : Part}
    (hw : w.2 < (X.tr w.1).length) :
    AsyncOnlyFinished (X.snoc g e r) i p w → AsyncOnlyFinished X i p w := by
  have hn : w ≠ (g, (X.tr g).length) := by rintro rfl; simp at hw
  rintro ⟨hv, hgw, hs⟩
  have hgw' := (groupWaits_except_new hc hn).mp hgw
  rw [snoc_groupWaitStages_old (groupWaitsFor_issuer hgw')] at hs
  exact ⟨hv, hgw', fun q hq => (snoc_asyncPresent hc).mp (hs q hq)⟩

theorem before_at_old (hc : BulkShape e.kind)
    (hbo : ∀ {x f : EvId}, f.2 < (X.tr f.1).length →
        (baseCausality L (X.snoc g e r) x f ↔ baseCausality L X x f))
    {a b : EvId × Part} (hb : b.1.2 < (X.tr b.1.1).length)
    (h : AsyncBefore L (X.snoc g e r) l a b) : AsyncBefore L X l a b := by
  obtain ⟨ha, hb', hrest⟩ := h
  refine ⟨(snoc_asyncCovers hc).mp ha, (snoc_asyncCovers hc).mp hb', ?_⟩
  rcases hrest with ⟨w, hf, ho⟩ | ⟨w, hf, hp⟩
  · have ho' := (hbo hb).mp ho
    exact .inl ⟨w, finished_at_old hc (baseCausality_events ho').1 hf, ho'⟩
  · have hp' : po X w b.1 := (po_snoc_old (g := g) (e := e) (r := r) hb).mp hp
    have hw : w.2 < (X.tr w.1).length := by rw [hp'.1]; have := hp'.2.1; omega
    exact .inr ⟨w, onlyFinished_at_old hc hw hf, hp'⟩

theorem chain_at_old (hX : Consistent L K A mem0 X) (hc : BulkShape e.kind)
    (hbo : ∀ {x f : EvId}, f.2 < (X.tr f.1).length →
        (baseCausality L (X.snoc g e r) x f ↔ baseCausality L X x f))
    {a b : EvId × Part} (hch : AsyncChain L (X.snoc g e r) l a b)
    (hb : b.1.2 < (X.tr b.1.1).length) : AsyncChain L X l a b := by
  revert hb
  induction hch with
  | direct h => intro hb; exact .direct (before_at_old hc hbo hb h)
  | @tail b c _ hp hedge ih =>
    intro hcl
    have hp' : X.AsyncPresent b.1 b.2 := (snoc_asyncPresent hc).mp hp
    have hb : b.1.2 < (X.tr b.1.1).length :=
      refPresent_issuer_lt hX.effectValidity (show X.RefPresent (.async b.1 b.2) from hp')
    exact .tail (ih hb) hp' (before_at_old hc hbo hcl hedge)

/-- The observation of a completion that precedes an access is an event of `X` when the
access is. -/
theorem completionBefore_src {p : Part} {w f : EvId} (h : CompletionBefore L X l p w f) :
    w.2 < (X.tr w.1).length := by
  cases p
  case mmaRead =>
    obtain ⟨_, _, _, _, _, _, _, h1, _⟩ := (h : ProxyBefore L X w f l)
    exact (baseCausality_events h1).1
  all_goals exact (baseCausality_events h).1

theorem visibility_at_old (hX : Consistent L K A mem0 X) (hc : BulkShape e.kind)
    (hbo : ∀ {x f : EvId}, f.2 < (X.tr f.1).length →
        (baseCausality L (X.snoc g e r) x f ↔ baseCausality L X x f))
    {x f : Ref} {l : Loc} (hf : f.issuer.2 < (X.tr f.issuer.1).length) :
    modelCausality L (X.snoc g e r) l x f ↔ modelCausality L X l x f := by
  constructor
  · intro hv
    cases x with
    | thread x =>
      cases f with
      | thread f =>
        exact hv.elim (fun h => .inl ((hbo hf).mp h))
          (fun h => .inr ((snoc_allocResultBefore_old hX.dependency.ready hf).mp h))
      | async i p =>
        refine ⟨(snoc_asyncCovers hc).mp hv.1, ?_⟩
        rcases hv.2 with hp | ⟨hg, hb⟩
        · exact .inl ((Kind.AsyncSilent.proxyBefore_snoc_old hbo hf).mp hp)
        · exact .inr ⟨(snoc_genericCopy hc).mp hg, (hbo hf).mp hb⟩
    | async i p =>
      cases f with
      | thread f =>
        obtain ⟨hcv, w, hfin, ho⟩ := hv
        have ho' := (observedCompletionBefore_snoc_old (fun _ => snoc_cpIssue hc)
          (fun _ _ _ _ => snoc_mmaIssue hc) hf
          (hbo hf) (Kind.AsyncSilent.proxyBefore_snoc_old hbo hf)).mp ho
        have hw := ho'.elim completionBefore_src
          (fun h => (baseCausality_events (TcReadReuseBefore.base L h)).1)
        exact ⟨(snoc_asyncCovers hc).mp hcv, w, finished_at_old hc hw hfin, ho'⟩
      | async j q =>
        have hpt : ∀ k, PairTc (X.snoc g e r) k ↔ PairTc X k := fun _ => by
          simp only [PairTc, snoc_mmaIssue hc, snoc_cpIssue hc]
        simp only [modelCausality, hpt] at hv ⊢
        exact ⟨hv.1, chain_at_old hX hc hbo hv.2 hf⟩
  · exact modelCausality_snoc_mono hX.tma.2.1

/-- The asynchronous effects stay valid when a bulk wait is appended. -/
theorem wait_tma (hX : Consistent L K A mem0 X) {pc : Nat} {mode : BulkGroup.WaitMode}
    {remaining : Nat} :
    TmaOk (X.snoc g ⟨pc, .bulkWait mode remaining⟩ (fun _ => none)) :=
  hX.tmaOk_snoc_unobserved (fun _ h => by cases h)
    (fun _ => by simp only [objectAction, snoc_get_new])

/-- The appended wait is the last event of its thread, so it has not returned. -/
theorem not_returned_new {pc : Nat} {mode : BulkGroup.WaitMode} {remaining : Nat} :
    ¬ Returned (X.snoc g ⟨pc, .bulkWait mode remaining⟩ r) (X.newId g) := by
  unfold Returned
  change ¬ (match (X.snoc g ⟨pc, .bulkWait mode remaining⟩ r).get (g, (X.tr g).length) with
    | some ⟨_, .wait _ _ ok _ _⟩ => ok = true
    | some ev => match ev.kind.resume with
      | .blocking true => True
      | .blocking false => (g, (X.tr g).length).2 + 1 <
          ((X.snoc g ⟨pc, .bulkWait mode remaining⟩ r).tr (g, (X.tr g).length).1).length
      | _ => False
    | none => False)
  simp [snoc_get_new, Kind.resume, snoc_len]

theorem wait_baseCausality (hX : Consistent L K A mem0 X) {pc : Nat}
    {mode : BulkGroup.WaitMode} {remaining : Nat} {x f : EvId} (hf : f.2 < (X.tr f.1).length) :
    baseCausality L (X.snoc g ⟨pc, .bulkWait mode remaining⟩ (fun _ => none)) x f ↔
      baseCausality L X x f :=
  baseCausality_snoc_old_of_not_arrive hX.cluster (.of_rfWf hX.rf) (by intros; nofun)
    (by intros; nofun) (by intros; nofun) (by intros; nofun) hf

theorem wait_extra (hX : Consistent L K A mem0 X) {pc : Nat} {mode : BulkGroup.WaitMode}
    {remaining : Nat} (hne : X.tr g ≠ []) :
    ExtensionObligations L A (X.snoc g ⟨pc, .bulkWait mode remaining⟩ (fun _ => none)) :=
  .snoc_frame hX (by intros; nofun) (by intros; nofun) nofun
    (hX.clc.snoc (.inl hne) (by intros; nofun))
    (hX.tmemPairResult.snoc_not_wr (by intros; nofun))
    (hX.tcRead_snoc (by intros; nofun) (by intros; nofun) (by intros; nofun) (by intros; nofun)
      (by intros; nofun))
    (hX.atomic.snoc hX.store hX.tma.1 (by intros; nofun))
    (hX.fenceSc_snoc (by intros; nofun) (by intros; nofun) (by intros; nofun) (by intros; nofun))
    (hX.matrix.snoc rfl) (by intros; nofun)

theorem wait_orderOk (hX : Consistent L K A mem0 X) {pc : Nat} {mode : BulkGroup.WaitMode}
    {remaining : Nat} :
    OrderOk L K A (X.snoc g ⟨pc, .bulkWait mode remaining⟩ (fun _ => none)) :=
  snoc_plain_orderOk hX (Kind.WaitFree.mk trivial (by intros; nofun)) (by intros; nofun) nofun
    rfl rfl (by intros; nofun) (by intro _ _ _ h; cases h)

/-- **Appending a bulk-group wait extends the execution by a counted event.** The thread's last
event is released. The wait's own readiness is not needed here: as the thread's last event it
has not returned. -/
theorem bulk_wait_counted_extension (hX : Consistent L K A mem0 X) {g pc : Nat}
    {mode : BulkGroup.WaitMode} {remaining : Nat} (hg : g < L.threads) (hne : X.tr g ≠ [])
    (hrel : Released L X g)
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.snoc g ⟨pc, .bulkWait mode remaining⟩ (fun _ => none)))
    {t t1 u : TState} (hrun : Run K A L g {} (X.tr g) (some t))
    (hl : Relation.ReflTransGen (Tau K A L g) t t1)
    (he : EStep K A L g t1 ⟨pc, .bulkWait mode remaining⟩ (some u)) :
    ∃ Y, Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < Y.size L := by
  have hshape : BulkShape (Event.mk pc (Kind.bulkWait mode remaining)).kind := True.intro
  have hns : ∀ m a b c recv ok, (Event.mk pc (Kind.bulkWait mode remaining)).kind ≠
      .shfl m a b c recv ok := by
    intros; nofun
  have hY : Consistent L K A mem0
      (X.snoc g (Event.mk pc (Kind.bulkWait mode remaining)) (fun _ => none)) :=
    consistent_snoc_preserving hX hg hrun hl he hns (by intro h; cases h) hrel.ready
      (fun h => (not_returned_new h).elim)
      (fun _ _ _ hv => (snoc_memReads hshape).mp hv)
      (fun _ _ _ => snoc_memWrites hshape)
      (fun _ _ _ hf => visibility_at_old hX hshape (wait_baseCausality hX)
        (refPresent_issuer_lt hX.effectValidity hf))
      (wait_orderOk hX) hasm (wait_tma hX) (wait_extra hX hne)
  refine ⟨X.snoc g (Event.mk pc (Kind.bulkWait mode remaining)) (fun _ => none), hY, le_snoc, ?_⟩
  rw [size_snoc hX hg (by rfl : (Event.mk pc (Kind.bulkWait mode remaining)).counts = true)]
  omega

end
end
end PTX.Step.BulkWait
