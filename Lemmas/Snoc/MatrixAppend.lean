-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Snoc.MatrixAppendFrame
public import Lemmas.Snoc.MatrixResult
public import Lemmas.Protocol.CountNth
public import Lemmas.Step.ExitLast

@[expose] public section

/-! # A warp-level matrix instance appended to the 32 lanes of its warp

A proof tool for the warp-level matrix instructions (`ldmatrix`, `stmatrix`, `movmatrix`,
`mma.sync`). The matrix event of a lane (`.matrix op own recv`) exists in a consistent execution
only together with the matrix events of the same per-thread ordinal of all 32 lanes of its warp
(DEP-ORDER; a lane that exited short of it is ERR-ALIGNED-MISMATCH), and each lane receives the
bytes `matrixRecv` computes from the contributions of all lanes (DEP-WARP-MATRIX). So a warp's
instance is appended to its 32 lanes at once.

* `matrixBatch L pc op parts recv` is the event of each thread: the lane `l` of the warp
  contributes `parts l` and receives `recv l`.
* `MatrixResultOk A op parts recv` says that the bytes `recv` are results of the instance: the
  clause of `Consistent.matrix` (`MatrixRecvOk`) for every lane. A result that cannot be computed
  constrains nothing (the instance is then `MatrixUnsafe`), so results always exist for the forms
  whose results read the 32 lanes only (`exists_matrixResultOk`).
* `matrixInstance_consistent`: when every thread of the warp of `g` can perform its event of the
  batch after local steps of its run, is released, has started or is launched, and has made `n`
  matrix events, the execution with the 32 events appended is consistent, extends `X` and is
  larger. The fields `thr`, `matrix` and `dependency` of `Consistent` are proved here; the others
  come from the frame lemmas of `Lemmas/Snoc/MatrixAppendFrame.lean` and from the lane-by-lane
  appends (`MatrixOpen`, the copy of `Step.WarpOpen` for the matrix kind).

The general lemma for any list of threads is `appendLanes_consistent_matrix`. -/

namespace PTX.Step
open PTX AsyncCopy
noncomputable section

/-! ### The obligations that each single append keeps -/

/-- The obligations of a consistent execution other than its traces, read sources, memory order,
dependency order, kernel assumptions, the matching and values of the warp collectives and the
matrix instances (DEP-WARP-MATRIX): `Step.WarpOpen` without its `matrix` field. Each single append
of a lane's matrix event keeps them (`MatrixOpen.snoc_lane`), while the matrix instances and the
readiness of the new events (DEP-ORDER) need all 32 lanes. -/
structure MatrixOpen (L : Launch) (A : List Assumption) (Z : Execution) : Prop where
  ctaBar : CtaBarHistoryOk L Z
  clusterHistory : ClusterHistoryOk L Z
  clc : ClcOk L Z
  tensor : TensorOk L Z
  store : TensorStoreOk L Z
  atomic : AtomicOk L Z
  fenceSc : FenceScOk L Z (baseCausality L Z)
  tmemPair : Tmem.Pair.HistoriesOk L Z
  tmemPairResult : Tmem.Pair.ResultOk L Z
  tcCommit : AsyncCopy.CommitOk Z
  tcRead : TcMma.ReadOk L A Z
  reduce : TensorStore.ReduceOk A Z
  tma : TmaOk Z

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {Z : Execution}
  {g : Nat} {e : Event} {r : Nat → Option Ref}

/-- A consistent execution has the obligations of `MatrixOpen`. -/
theorem _root_.PTX.Consistent.matrixOpen (h : Consistent L K A mem0 Z) : MatrixOpen L A Z :=
  ⟨h.ctaBar, h.cluster, h.clc, h.tensor, h.store, h.atomic, h.fenceSc, h.tmemPair,
    h.tmemPairResult, h.tcCommit, h.tcRead, h.reduce, h.tma⟩

/-- The asynchronous effects of an execution with the obligations of `MatrixOpen` are valid. -/
theorem MatrixOpen.effectValidity (h : MatrixOpen L A Z) : EffectValidity L Z :=
  ⟨h.tma, h.tensor, h.store, h.clc, h.tmemPair, h.tcCommit⟩

/-- Appending a matrix event adds no thread order into older events. -/
theorem baseCausality_snoc_old_matrix (hcl : ClusterHistoryOk L Z) (hw : e.kind.MatrixColl)
    {a b : EvId} (hbo : b.2 < (Z.tr b.1).length) :
    baseCausality L (Z.snoc g e r) a b ↔ baseCausality L Z a b :=
  ⟨fun h => baseCausality_old_of_step (fun hb => snoc_step_old_of hcl
    (.of_noWrite (fun _ _ => hw.ne id) (fun _ _ _ => hw.ne id))
    (fun _ _ => snoc_ctaBarK (fun _ _ _ => hw.ne id))
    (fun _ _ => snoc_ctaBarArrivalK (fun _ _ _ => hw.ne id)) hb
    (msync_snoc_old (fun _ _ _ _ => hw.ne id) hb) (fun _ _ he => (hw.ne id he).elim)
    (fun _ => hw.ne id)) h hbo, baseCausality_snoc⟩

/-- **One lane's matrix event keeps the obligations of `MatrixOpen`**, once the lane has started
or its cluster has been launched. -/
theorem MatrixOpen.snoc_lane (hZ : MatrixOpen L A Z) (hw : e.kind.MatrixColl)
    (hst : Z.tr g ≠ [] ∨ Launched L Z g) : MatrixOpen L A (Z.snoc g e r) := by
  have htc : ∀ k, e.kind ≠ .tc k := fun _ => hw.ne id
  have hbo : ∀ {x f : EvId}, f.2 < (Z.tr f.1).length →
      (baseCausality L (Z.snoc g e r) x f ↔ baseCausality L Z x f) :=
    fun hf => baseCausality_snoc_old_matrix hZ.clusterHistory hw hf
  have hv := hZ.effectValidity
  have le : Z.le (Z.snoc g e r) := le_snoc
  refine ⟨hZ.ctaBar.snoc, hZ.clusterHistory.preserving le rfl,
    hZ.clc.snoc hst (fun _ _ => hw.ne id), ?_, ?_,
    hZ.atomic.snoc hZ.store hZ.tma.1 (fun _ _ _ => hw.ne id),
    hZ.fenceSc.snoc (fun _ => hw.ne id) (fun _ _ hb h => (hbo hb).mp h),
    hZ.tmemPair.mono le (fun _ => rfl) rfl,
    hZ.tmemPairResult.snoc_not_wr (fun _ _ _ h => hw.ne id (congrArg Event.kind h)), ?_,
    readOk_snoc hZ.tcRead hZ.tcCommit hZ.tma.2.2.1 hZ.tma.2.1 hbo
      (fun _ _ _ _ h => (htc _ (congrArg Event.kind h)).elim),
    hZ.reduce.snoc (fun _ => hw.ne id),
    ⟨snoc_copy_wellFormed hZ.tma, tcEffectsOk_snoc hZ.tma.2.1,
      snoc_objects_unchanged hv htc (fun l => ?_), snoc_arriveOk hZ.tma.2.2.2⟩⟩
  · intro i o ho
    obtain ⟨⟨addr, j, hj⟩, rest⟩ := hZ.tensor i o ho
    exact ⟨⟨addr, j, Execution.le_get le hj⟩, rest⟩
  · intro i o ho
    obtain ⟨⟨addr, j, hj⟩, rest⟩ := hZ.store i o ho
    exact ⟨⟨addr, j, Execution.le_get le hj⟩, rest⟩
  · simp only [CommitOk, snoc_tracksMma_of_not_tc htc, snoc_commit htc, snoc_async]
    exact hZ.tcCommit
  · simp only [objectAction, snoc_get_new]
    obtain ⟨pc, k⟩ := e
    cases k <;> first | exact (hw : False).elim | rfl

/-! ### Matrix events appended to a list of threads -/

variable {X : Execution} {ds : List Nat} {ev : Nat → Event}

/-- A thread outside `ds` that has started, or whose cluster has been launched, still has. -/
theorem started_appendLanes_matrix (hw : ∀ h ∈ ds, (ev h).kind.MatrixColl) {h : Nat}
    (hh : h ∉ ds) (hst : X.tr h ≠ [] ∨ Launched L X h) :
    (X.appendLanes ds ev).tr h ≠ [] ∨ Launched L (X.appendLanes ds ev) h := by
  rw [appendLanes_tr_of_not_mem hh]
  refine hst.imp id (fun hl ⟨i, s, ts, pc, hi⟩ => hl ⟨i, s, ts, pc, ?_⟩)
  exact (appendLanes_get_kind (fun h' hm => (hw h' hm).ne id)).mp hi

/-- **An old event that `X` holds ready stays ready** after the matrix events are appended to
threads that have not exited: the exit of a lane that fills a need of a matrix event keeps its
matrix count (`ThreadAppend.need_of_old`). -/
theorem appendLanes_ready_old_matrix (hd : ds.Nodup) (hw : ∀ h ∈ ds, (ev h).kind.MatrixColl)
    (hnx : ∀ h ∈ ds, ∀ i pc, X.get (h, i) ≠ some ⟨pc, .exit⟩) {j : EvId}
    (hj : j.2 < (X.tr j.1).length) (hr : Ready L X j) : Ready L (X.appendLanes ds ev) j := by
  have ha := appendLanes_threadAppend (X := X) (ds := ds) (ev := ev)
  have hpres : ∀ i p, X.AsyncPresent i p → (X.appendLanes ds ev).AsyncPresent i p :=
    fun _ _ => (appendLanes_asyncPresent_matrix hd hw).mpr
  have hex : (∃ pc op own recv, X.get j = some ⟨pc, .matrix op own recv⟩) →
      ∀ v pc, X.get v = some ⟨pc, .exit⟩ →
      ((X.appendLanes ds ev).tr v.1).countP isMatrix ≤ (X.tr v.1).countP isMatrix := by
    intro _ v pc hv
    rw [appendLanes_tr]
    split_ifs with hm
    · exact absurd hv (hnx v.1 hm v.2 pc)
    · exact le_refl _
  intro n hn
  rcases ha.need_of_old hex (ha.not_new hj) hn with ⟨x, hx, fills, rfl, hf⟩ | ⟨n', hn', himp⟩
  · exact ⟨x, hx, hf⟩
  · have h' := hr n' hn'
    cases n' <;> cases n <;> simp only [NeedImp] at himp
    · obtain ⟨x, hx, hf⟩ := h'
      exact ⟨x, ha.present_mono hpres hx, himp x hx hf⟩
    · exact himp h'

/-- **Readiness after appending the matrix events** (DEP-ORDER): old events keep their
readiness, the previous last event of each lane is ready (`Released`), and the new events are
ready by hypothesis. -/
theorem appendLanes_ready_matrix (hX : Consistent L K A mem0 X) (hd : ds.Nodup)
    (hw : ∀ h ∈ ds, (ev h).kind.MatrixColl)
    (hnx : ∀ h ∈ ds, ∀ i pc, X.get (h, i) ≠ some ⟨pc, .exit⟩)
    (hrel : ∀ h ∈ ds, Released L X h)
    (hnew : ∀ h ∈ ds, Ready L (X.appendLanes ds ev) (h, (X.tr h).length)) :
    ∀ j, Returned (X.appendLanes ds ev) j → Ready L (X.appendLanes ds ev) j := by
  intro j hr
  by_cases hjn : j.1 ∈ ds ∧ j.2 = (X.tr j.1).length
  · obtain ⟨j1, j2⟩ := j
    obtain ⟨h1, h2⟩ := hjn
    simp only at h1 h2
    subst h2
    exact hnew j1 h1
  have hjo : (X.appendLanes ds ev).get j = X.get j := by
    rw [appendLanes_get, ite_eq_right hjn]
  refine appendLanes_ready_old_matrix hd hw hnx ?_ ?_
  · unfold Returned at hr
    rw [hjo] at hr
    cases hget : X.get j with
    | none => simp [hget] at hr
    | some q => exact len_of_get hget
  by_cases hrX : Returned X j
  · exact hX.dependency.ready j hrX
  unfold Returned at hr hrX
  rw [hjo] at hr
  cases hget : X.get j with
  | none => simp [hget] at hr
  | some q =>
  obtain ⟨pc, k⟩ := q
  simp only [hget] at hr hrX
  have hjold : j.2 < (X.tr j.1).length := len_of_get hget
  have finish : j.2 + 1 < ((X.appendLanes ds ev).tr j.1).length →
      ¬ j.2 + 1 < (X.tr j.1).length → k.resume = .blocking false → Ready L X j := by
    intro h1 h2 hres
    rw [appendLanes_len] at h1
    split_ifs at h1 with hjg
    · obtain ⟨j1, j2⟩ := j
      simp only at hjg h1 h2 hjold hget
      have hj2 : j2 = (X.tr j1).length - 1 := by omega
      subst hj2
      exact (hrel j1 hjg).ready pc k hget hres
    · exact absurd h1 h2
  split at hr
  · rename_i heq
    cases heq
    simp only at hrX
    exact absurd hr hrX
  · rename_i ev' hnw heq
    cases heq
    split at hrX
    · rename_i heq'
      cases heq'
      exact absurd rfl (hnw _ _ _ _ _ _)
    · rename_i heq'
      cases heq'
      cases hres : k.resume with
      | blocking c =>
        cases c
        · simp only [hres] at hr hrX
          exact finish hr hrX hres
        · simp only [hres] at hrX
          exact absurd trivial hrX
      | _ => simp only [hres] at hr
    · rename_i heq'
      cases heq'
  · exact hr.elim

/-- What the lane-by-lane appends keep: the obligations of `MatrixOpen` and the visibility into
every old event. -/
private theorem appendLanes_open_matrix (hX : Consistent L K A mem0 X) {ds' : List Nat}
    (hsub : ∀ h ∈ ds', h ∈ ds) (hd : ds'.Nodup) (hw : ∀ h ∈ ds, (ev h).kind.MatrixColl)
    (hst : ∀ h ∈ ds, X.tr h ≠ [] ∨ Launched L X h) :
    MatrixOpen L A (X.appendLanes ds' ev) ∧
      (∀ l v f, X.RefPresent f →
          (modelCausality L (X.appendLanes ds' ev) l v f ↔ modelCausality L X l v f)) ∧
      ∀ x f, f.2 < (X.tr f.1).length →
          (baseCausality L (X.appendLanes ds' ev) x f ↔ baseCausality L X x f) := by
  induction ds' with
  | nil =>
    rw [appendLanes_nil]
    exact ⟨hX.matrixOpen, fun _ _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl⟩
  | cons h ds' ih =>
    have hh : h ∈ ds := hsub h List.mem_cons_self
    have hn := (List.nodup_cons.mp hd).1
    obtain ⟨hO, hV, hH⟩ := ih (fun h' hm => hsub h' (List.mem_cons_of_mem _ hm))
      (List.nodup_cons.mp hd).2
    have hw' : ∀ h' ∈ ds', (ev h').kind.MatrixColl :=
      fun h' hm => hw h' (hsub h' (List.mem_cons_of_mem _ hm))
    have hbo : ∀ {x f : EvId}, f.2 < ((X.appendLanes ds' ev).tr f.1).length →
        (baseCausality L ((X.appendLanes ds' ev).snoc h (ev h) (fun _ => none)) x f ↔
          baseCausality L (X.appendLanes ds' ev) x f) :=
      fun hf => baseCausality_snoc_old_matrix hO.clusterHistory (hw h hh) hf
    rw [appendLanes_cons hn]
    have hold : ∀ {f : EvId}, f.2 < (X.tr f.1).length →
        f.2 < ((X.appendLanes ds' ev).tr f.1).length := fun {f} hf =>
      lt_of_lt_of_le hf ((le_appendLanes (X := X) (ds := ds') (ev := ev)).1 f.1).length_le
    refine ⟨hO.snoc_lane (hw h hh) (started_appendLanes_matrix hw' hn (hst h hh)),
      fun l v f hf => ?_, fun x f hf => (hbo (hold hf)).trans (hH x f hf)⟩
    rw [← hV l v f hf]
    apply (hw h hh).asyncSilent.modelCausality_snoc_old hbo
      (snoc_allocResultBefore_old_of_not_write (fun _ _ he => (hw h hh).ne id he))
    have := refPresent_issuer_lt hX.effectValidity hf
    have := (le_appendLanes (X := X) (ds := ds') (ev := ev)).1 f.issuer.1
    exact lt_of_lt_of_le ‹_› this.length_le

/-- **Matrix events appended to their lanes are consistent**, given that no new event matches an
old one (`MatrixMatch`), the readiness of the new events (DEP-ORDER) and the matrix rule on the
result (DEP-WARP-MATRIX). The other collective rules are those of `X`: the new events are no
shuffles, elections, warp barriers, votes or exits. -/
theorem appendLanes_consistent_matrix (hX : Consistent L K A mem0 X) (hd : ds.Nodup)
    (hlt : ∀ h ∈ ds, h < L.threads) (hw : ∀ h ∈ ds, (ev h).kind.MatrixColl)
    (hst : ∀ h ∈ ds, X.tr h ≠ [] ∨ Launched L X h) (hrel : ∀ h ∈ ds, Released L X h)
    (hrun : ∀ h ∈ ds, ∃ t t1 o, Run K A L h {} (X.tr h) (some t) ∧
      Relation.ReflTransGen (Tau K A L h) t t1 ∧ EStep K A L h t1 (ev h) o)
    (hfresh : ∀ h ∈ ds, ∀ j : EvId, j.2 < (X.tr j.1).length →
      ¬ MatrixMatch L (X.appendLanes ds ev) (h, (X.tr h).length) j)
    (hnew : ∀ h ∈ ds, Ready L (X.appendLanes ds ev) (h, (X.tr h).length))
    (hmatrix : MatrixOk L A (X.appendLanes ds ev))
    (hasm : ∀ a ∈ A, a.wf L mem0 (X.appendLanes ds ev)) :
    Consistent L K A mem0 (X.appendLanes ds ev) := by
  have le : X.le (X.appendLanes ds ev) := le_appendLanes
  obtain ⟨hO, hV, hH⟩ := appendLanes_open_matrix hX (fun h hm => hm) hd hw hst
  have hreads {v a bs} : (X.appendLanes ds ev).MemReads v a bs ↔ X.MemReads v a bs :=
    appendLanes_memReads_matrix hd hw
  have hwrites {v a bs} : (X.appendLanes ds ev).MemWrites v a bs ↔ X.MemWrites v a bs :=
    appendLanes_memWrites_matrix hd hw
  have hnx : ∀ h ∈ ds, ∀ i pc, X.get (h, i) ≠ some ⟨pc, .exit⟩ := by
    intro h hh i pc
    obtain ⟨t, -, -, hr, -⟩ := hrun h hh
    exact hr.no_exit
  have hlv : ∀ v pc k, (X.appendLanes ds ev).get v = some ⟨pc, k⟩ → k.laneValue = true →
      X.get v = some ⟨pc, k⟩ := fun v pc k h hk =>
    (appendLanes_get_kind (fun j hj hjk => by
      have := (hw j hj).laneValue
      rw [hjk, hk] at this
      cases this)).mp h
  have hex : ∀ v pc, (X.appendLanes ds ev).get v = some ⟨pc, .exit⟩ →
      X.get v = some ⟨pc, .exit⟩ :=
    fun v pc h => (appendLanes_get_kind (fun j hj => (hw j hj).ne (k' := .exit) id)).mp h
  apply consistent_preserving_extension hX le_appendLanes
  · intro h hh
    rw [appendLanes_tr]
    split_ifs with hm
    · obtain ⟨t, t1, o, hr, hl, he⟩ := hrun h hm
      exact ⟨o, hr.snoc hl he⟩
    · exact hX.thr h hh
  · intro h hh
    rw [appendLanes_tr, ite_eq_right (fun hm => by have := hlt h hm; omega)]
    exact hX.outside h hh
  · exact fun v a bs h => hreads.mp h
  · exact fun v a bs h => hwrites.mp h
  · exact fun v a bs h => hwrites.mpr h
  · exact fun v a bs h k => le.2.1 v k ⟨a, bs, hreads.mp h⟩
  · exact hV
  · exact appendLanes_ready_matrix hX hd hw hnx hrel hnew
  · exact appendLanes_shflOk_of_not_shfl hX (fun h hh _ _ _ _ _ _ => (hw h hh).ne id)
  · exact (appendLanes_sinkFrame_matrix hX hd hw hfresh hO.effectValidity hO.clusterHistory
      (fun x f hf => (hH x f hf).mp)).orderOk hX.orderOk
  · exact hasm
  · exact hO.tma
  · rfl
  · exact
      { ctaBar := hO.ctaBar, cluster := hO.clusterHistory,
        elect := appendLanes_electOk_of_not_elect hX (fun h hh _ _ _ => (hw h hh).ne id),
        vote := Execution.voteOk_mono hX.vote le_appendLanes hlv hex,
        warpValue := Execution.warpValueOk_mono hX.warpValue le_appendLanes hlv hex,
        warpBar := appendLanes_warpBarOk_of_not_warpBar hX (fun h hh _ _ => (hw h hh).ne id),
        matrix := hmatrix, clc := hO.clc,
        tensor := hO.tensor, store := hO.store, atomic := hO.atomic, fenceSc := hO.fenceSc,
        tmemPair := hO.tmemPair, tmemPairResult := hO.tmemPairResult,
        tmemPairCompletion :=
          Tmem.Pair.completionClosed_of_growth le rfl rfl hX.tmemPair hX.tmemPairCompletion,
        tcCommit := hO.tcCommit,
        mmaCompletion := TcMma.completionClosed_of_growth le rfl hX.tma.2.1 hX.mmaCompletion,
        tcRead := hO.tcRead, reduce := hO.reduce }

/-! ### The matrix events of the lanes of a warp -/

/-- A thread with more than `c` matrix events has its matrix event number `c`. -/
theorem exists_matrixK {g c : Nat} (h : c + 1 ≤ (X.tr g).countP isMatrix) :
    ∃ j, X.MatrixK (g, j) c := by
  obtain ⟨j, x, hx, hp, hc⟩ := MbarRing.Slot.exists_nth_countP isMatrix h
  exact ⟨j, ⟨x, hx, hp⟩, hc⟩

/-- A matrix event of `X` has, in every lane of its warp, the matrix event of the same ordinal,
or that lane exited short of it: a matrix event has returned, so its needs are filled (DEP-ORDER,
DEP-WARP-MATRIX). -/
theorem matrix_lane_of_ready (hX : Consistent L K A mem0 X) {g i n : Nat}
    (hk : X.MatrixK (g, i) n) {h : Nat} (hs : SameWarp L g h) :
    (∃ j, X.MatrixK (h, j) n) ∨ ∃ j, X.ExitedShort isMatrix (h, j) n := by
  obtain ⟨⟨q, hget, hm⟩, hcnt⟩ := id hk
  obtain ⟨pc, k⟩ := q
  cases k <;> simp only [isMatrix, Bool.false_eq_true] at hm
  have hr : Ready L X (g, i) := hX.dependency.ready _ (by simp [Returned, hget, Kind.resume])
  have hl : laneOf L h < 32 := Nat.mod_lt _ (by decide)
  obtain ⟨x, -, j, -, hx⟩ := hr (.node fun x => ∃ j, x = .thread (warpLane L g (laneOf L h), j) ∧
      (X.MatrixK (warpLane L g (laneOf L h), j) (((X.tr g).take i).countP isMatrix) ∨
        X.ExitedShort isMatrix (warpLane L g (laneOf L h), j)
          (((X.tr g).take i).countP isMatrix)))
    (by simp only [Needs, hget, KindNeeds]
        exact List.mem_map.mpr ⟨laneOf L h, List.mem_range.mpr hl, rfl⟩)
  simp only at hcnt
  rw [warpLane_of_sameWarp hs, hcnt] at hx
  exact hx.imp (fun h => ⟨j, h⟩) (fun h => ⟨j, h⟩)

/-- **A lane that has not exited has made at least as many matrix events as every lane of its
warp**: the first matrix event it has not made, of another lane, would wait for it. -/
theorem matrix_count_le (hX : Consistent L K A mem0 X) {g h : Nat} (hs : SameWarp L g h)
    (hlive : ∀ i pc, X.get (g, i) ≠ some ⟨pc, .exit⟩) :
    (X.tr h).countP isMatrix ≤ (X.tr g).countP isMatrix := by
  by_contra hlt
  obtain ⟨j, hj⟩ := exists_matrixK (X := X) (g := h) (c := (X.tr g).countP isMatrix) (by omega)
  rcases matrix_lane_of_ready hX hj (sameWarp_symm hs) with ⟨j', hk'⟩ | ⟨j', ⟨pc, hex⟩, -⟩
  · exact Nat.lt_irrefl _ (lt_countP_of_matrixK hk')
  · exact hlive j' pc hex

/-- **Two lanes of a warp that have not exited have made equally many matrix events.** -/
theorem matrix_count_eq (hX : Consistent L K A mem0 X) {g h : Nat} (hs : SameWarp L g h)
    (hg : ∀ i pc, X.get (g, i) ≠ some ⟨pc, .exit⟩)
    (hh : ∀ i pc, X.get (h, i) ≠ some ⟨pc, .exit⟩) :
    (X.tr h).countP isMatrix = (X.tr g).countP isMatrix :=
  Nat.le_antisymm (matrix_count_le hX hs hg) (matrix_count_le hX (sameWarp_symm hs) hh)

/-- The events of one instance of a warp-level matrix instruction at position `pc` with
operation `op`: the thread `h` contributes `parts l` and receives `recv l` for its lane
`l = laneOf L h`. -/
def matrixBatch (L : Launch) (pc : Nat) (op : MatrixOp) (parts recv : Nat → List (Option Byte))
    (h : Nat) : Event :=
  ⟨pc, .matrix op (parts (laneOf L h)) (recv (laneOf L h))⟩

section
variable {g pc n : Nat} {op : MatrixOp} {parts recv : Nat → List (Option Byte)}

local notation "Y" =>
  Execution.appendLanes X (warpThreads L g) (matrixBatch L pc op parts recv)

private theorem batch_kind (h : Nat) : (matrixBatch L pc op parts recv h).kind.MatrixColl :=
  trivial

/-- A matrix event of the extension is an old one, or the new event of a lane of the warp, whose
ordinal is the number `n` of matrix events its thread has made. -/
private theorem batch_matrixK_cases
    (hcnt : ∀ h, SameWarp L g h → (X.tr h).countP isMatrix = n) {v : EvId} {m : Nat}
    (hk : (Y).MatrixK v m) :
    (v.2 < (X.tr v.1).length ∧ X.MatrixK v m) ∨
      (SameWarp L g v.1 ∧ v.2 = (X.tr v.1).length ∧ m = n) := by
  obtain ⟨⟨q, hq, -⟩, -⟩ := id hk
  rcases appendLanes_get_cases hq with ⟨ho, -⟩ | ⟨hh, h2, -⟩
  · exact .inl ⟨ho, (appendLanes_matrixK_old ho).mp hk⟩
  · refine .inr ⟨mem_warpThreads.mp hh, h2, ?_⟩
    obtain ⟨v1, v2⟩ := v
    simp only at hh h2
    subst h2
    rw [(appendLanes_matrixK_new (fun h _ => batch_kind h) hh).mp hk,
      hcnt _ (mem_warpThreads.mp hh)]

/-- An old matrix event of a lane of the warp has an ordinal below `n`. -/
private theorem batch_old_lt (hcnt : ∀ h, SameWarp L g h → (X.tr h).countP isMatrix = n)
    {v : EvId} {m : Nat} (hs : SameWarp L g v.1) (hk : X.MatrixK v m) : m < n := by
  have := lt_countP_of_matrixK hk
  rwa [hcnt _ hs] at this

/-- **The matrix rule holds after the instance is appended** (DEP-WARP-MATRIX): an old matrix
event keeps its instance, since the lanes' new events have the ordinal `n` that no old event of
the warp has, and the instance of a new event is the appended one, whose results are those of
`MatrixResultOk`. -/
theorem matrixBatch_matrixOk (hX : Consistent L K A mem0 X) (hb : L.block % 32 = 0)
    (hcnt : ∀ h, SameWarp L g h → (X.tr h).countP isMatrix = n)
    (hres : MatrixResultOk A op parts recv) : MatrixOk L A Y := by
  have hthr {v : EvId} {q : Event} (hq : X.get v = some q) : v.1 < L.threads := by
    by_contra hn
    have := len_of_get hq
    rw [hX.outside v.1 (by omega)] at this
    simp at this
  intro g' i pc' op' own' recv' n' hget hK parts' hinst
  rcases batch_matrixK_cases hcnt hK with ⟨hio, hKX⟩ | ⟨hs, hi, rfl⟩
  · -- an old event: every event of its instance is old
    have hgX : X.get (g', i) = some ⟨pc', .matrix op' own' recv'⟩ := by
      rwa [appendLanes_get_old hio] at hget
    have hg' := hthr hgX
    refine hX.matrix g' i pc' op' own' recv' n' hgX hKX parts' (fun lane hl => ?_)
    obtain ⟨j, rv, hj, hjk⟩ := hinst lane hl
    rcases batch_matrixK_cases hcnt hjk with ⟨hjo, hjX⟩ | ⟨hsj, -, rfl⟩
    · exact ⟨j, rv, by rwa [appendLanes_get_old hjo] at hj, hjX⟩
    · have hs : SameWarp L g g' :=
        sameWarp_trans hsj (sameWarp_symm (sameWarp_lane hb hg' hl).1)
      exact absurd (batch_old_lt hcnt hs hKX) (lt_irrefl _)
  · -- a new event: its instance is the appended one
    simp only at hs hi
    subst hi
    rw [appendLanes_get_new (mem_warpThreads.mpr hs)] at hget
    simp only [matrixBatch, Option.some.injEq, Event.mk.injEq, Kind.matrix.injEq] at hget
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hget
    have hparts : ∀ lane < 32, parts' lane = parts lane := by
      intro lane hl
      obtain ⟨j, rv, hj, hjk⟩ := hinst lane hl
      obtain ⟨hsl, hll⟩ := sameWarp_lane hb hs.1.2.1 hl
      rcases batch_matrixK_cases hcnt hjk with ⟨-, hjX⟩ | ⟨hsj, hj2, -⟩
      · exact absurd (batch_old_lt hcnt (sameWarp_trans hs hsl) hjX) (lt_irrefl _)
      · simp only at hsj hj2
        subst hj2
        rw [appendLanes_get_new (mem_warpThreads.mpr hsj)] at hj
        simp only [matrixBatch, Option.some.injEq, Event.mk.injEq, Kind.matrix.injEq, hll,
          true_and] at hj
        exact hj.1.symm
    exact hres parts' hparts (laneOf L g') (Nat.mod_lt _ (by decide))

/-- **Every new event of the instance is ready** (DEP-ORDER): each of the 32 lanes of the warp
has its matrix event of the same ordinal, the appended one. -/
theorem matrixBatch_ready (hb : L.block % 32 = 0)
    (hcnt : ∀ h, SameWarp L g h → (X.tr h).countP isMatrix = n) {h : Nat}
    (hs : SameWarp L g h) : Ready L Y (h, (X.tr h).length) := by
  have hw : ∀ h ∈ warpThreads L g, (matrixBatch L pc op parts recv h).kind.MatrixColl :=
    fun h _ => batch_kind h
  intro nd hn
  simp only [Needs, appendLanes_get_new (mem_warpThreads.mpr hs), matrixBatch, KindNeeds,
    List.mem_map, List.mem_range] at hn
  obtain ⟨l, hl, rfl⟩ := hn
  have hs' : SameWarp L g (warpLane L h l) :=
    sameWarp_trans hs (sameWarp_lane hb hs.1.2.1 hl).1
  refine ⟨.thread (warpLane L h l, (X.tr (warpLane L h l)).length),
    ⟨_, appendLanes_get_new (mem_warpThreads.mpr hs')⟩, _, rfl, .inl ?_⟩
  rw [appendLanes_matrixK_new hw (mem_warpThreads.mpr hs'), hcnt _ hs',
    appendLanes_take (i := (h, (X.tr h).length)) le_rfl, List.take_length, hcnt _ hs]

/-- **A warp performs one instance of a warp-level matrix instruction: the consistency core.**
Let every thread of the warp of `g` (32 consecutive launched threads of one CTA, `hb`) be able to
perform its matrix event of the batch after local steps of its run (`hrun`; so none has exited),
with its last event released (`hrel`) and its cluster launched if it has not started (`hst`). Let
every lane have made `n` matrix events (`hcnt`) and let the received bytes be results of the
instance (`hres`). Then the execution with the 32 events appended is consistent, extends `X` and
is larger. -/
theorem matrixInstance_consistent (hX : Consistent L K A mem0 X) (hb : L.block % 32 = 0)
    (hg : g < L.threads)
    (hst : ∀ h, SameWarp L g h → X.tr h ≠ [] ∨ Launched L X h)
    (hrel : ∀ h, SameWarp L g h → Released L X h)
    (hrun : ∀ h, SameWarp L g h → ∃ t t1 o, Run K A L h {} (X.tr h) (some t) ∧
      Relation.ReflTransGen (Tau K A L h) t t1 ∧
      EStep K A L h t1 (matrixBatch L pc op parts recv h) o)
    (hcnt : ∀ h, SameWarp L g h → (X.tr h).countP isMatrix = n)
    (hres : MatrixResultOk A op parts recv)
    (hasm : ∀ a ∈ A, a.wf L mem0 Y) :
    Consistent L K A mem0 Y ∧ X.le Y ∧ X.size L < (Y).size L := by
  have hmw {h : Nat} : h ∈ warpThreads L g ↔ SameWarp L g h := mem_warpThreads
  have hw : ∀ h ∈ warpThreads L g, (matrixBatch L pc op parts recv h).kind.MatrixColl :=
    fun h _ => batch_kind h
  have hlt : ∀ h ∈ warpThreads L g, h < L.threads := fun h hh => (hmw.mp hh).1.2.1
  refine ⟨appendLanes_consistent_matrix hX (warpThreads_nodup g) hlt hw
    (fun h hh => hst h (hmw.mp hh)) (fun h hh => hrel h (hmw.mp hh))
    (fun h hh => hrun h (hmw.mp hh)) ?_ (fun h hh => matrixBatch_ready hb hcnt (hmw.mp hh))
    (matrixBatch_matrixOk hX hb hcnt hres) hasm, le_appendLanes, ?_⟩
  · -- no old event has the ordinal `n` of the new events of its warp
    rintro h hh j hj ⟨⟨l, hl, hjl⟩, m, hk, hkj⟩
    simp only at hjl
    have hjX := (appendLanes_matrixK_old hj).mp hkj
    have hj1 : j.1 < L.threads := by
      by_contra hn
      rw [hX.outside j.1 (by omega)] at hj
      simp at hj
    have hsj : SameWarp L g j.1 := by
      refine sameWarp_trans (hmw.mp hh) (sameWarp_symm ?_)
      rw [hjl]
      exact (sameWarp_lane hb hj1 hl).1
    have hm := (appendLanes_matrixK_new hw hh).mp hk
    rw [hcnt _ (hmw.mp hh)] at hm
    exact absurd (batch_old_lt hcnt hsj hjX) (by omega)
  · rw [size_appendLanes hX (warpThreads_nodup g) hlt (fun h hh => (hw h hh).counts)]
    have := List.length_pos_of_ne_nil (warpThreads_ne_nil hg)
    omega

end

end
end PTX.Step
