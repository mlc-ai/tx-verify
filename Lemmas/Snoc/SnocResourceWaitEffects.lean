-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Snoc.SnocAsyncSilent
public import Lemmas.Snoc.SnocObjectMemory
public import Lemmas.Snoc.SnocResourceWaiting
public import Lemmas.Snoc.SnocAsync
public import Lemmas.Snoc.SnocOrder
public import Lemmas.Tmem.TmemPairExtend
public import Lemmas.Tmem.TmemPairHistory
public import Lemmas.Cluster.ClusterBarrierExecution
public import Lemmas.Snoc.Collectives

@[expose] public section

/-! Appending a register request or a cluster barrier before its independent grant.

Such an event adds no asynchronous operation, memory event, collective metadata or
happens-before edge into older events. Every obligation outside its own resource history
and waiting graph is transported from the old execution, provided the thread's previous
last event is a cluster barrier. -/
namespace PTX
open AsyncCopy
noncomputable section

/-- A register-pool request or a cluster barrier: the event waits on its own resource only. -/
def Kind.ResourceWait : Kind → Prop
  | .setMaxReg .. | .cluster .. => True
  | _ => False

/-- All transported obligations outside the new event's own resource history and waiting
graph. No grant of the new event is required for this result. -/
structure NonResourceEffects (L : Launch) (A : List Assumption) (base result : Execution) : Prop
    where
  clusterHistory : ClusterHistoryOk L result
  elect : ElectOk L result
  warpBar : WarpBarOk L result
  clc : ClcOk L result
  tensor : TensorOk L result
  store : TensorStoreOk L result
  atomic : AtomicOk L result
  fenceSc : FenceScOk L result (baseCausality L result)
  matrix : MatrixOk L A result
  reduce : TensorStore.ReduceOk A result
  tmemPair : Tmem.Pair.HistoriesOk L result
  tmemPairResult : Tmem.Pair.ResultOk L result
  tcCommit : AsyncCopy.CommitOk result
  tcRead : TcMma.ReadOk L A result
  tma : TmaOk result
  readPreserved : TcMma.ReadPreserved L base result

namespace Kind.ResourceWait
variable {L : Launch} {A : List Assumption} {K : Kernel} {mem0 : Mem0} {X : Execution}
  {g : Nat} {e : Event} {r : Nat → Option Ref}

theorem ne {k : Kind} (hw : e.kind.ResourceWait) (hk : ¬k.ResourceWait) : e.kind ≠ k :=
  fun h => hk (h ▸ hw)

theorem asyncSilent (hw : e.kind.ResourceWait) : e.kind.AsyncSilent := by
  obtain ⟨pc, k⟩ := e
  cases k <;> simp_all [Kind.ResourceWait, Kind.AsyncSilent]

theorem noTc (hw : e.kind.ResourceWait) (k : TcKind) : e.kind ≠ .tc k := hw.ne id

theorem baseCausality_old (hw : e.kind.ResourceWait) (hc : ClusterHistoryOk L X) {x f : EvId}
    (hf : f.2 < (X.tr f.1).length) : baseCausality L (X.snoc g e r) x f ↔ baseCausality L X x f :=
  baseCausality_snoc_old_of_not_arrive hc
    (.of_noWrite (fun _ _ => hw.ne id) (fun _ _ _ => hw.ne id)) (fun _ _ => hw.ne id)
    (fun _ _ _ => hw.ne id) (fun _ _ _ _ => hw.ne id) (fun _ => hw.ne id) hf

private theorem clc (hw : e.kind.ResourceWait) (hX : Consistent L K A mem0 X)
    (hstarted : X.tr g ≠ []) : ClcOk L (X.snoc g e r) := by
  have hissue (i : EvId) (s : Clc.Spec) (ts : List Nat) :
      (X.snoc g e r).ClcIssue i s ts ↔ X.ClcIssue i s ts := hw.asyncSilent.snoc_clcIssue
  obtain ⟨ha, hr, he, hi, hl⟩ := hX.clc
  refine ⟨ha, ?_, ?_, ?_, ?_⟩
  · intro request answer hh
    obtain ⟨i, s, ts, hid, his⟩ := hr request answer hh
    exact ⟨i, s, ts, hid, (hissue ..).mpr his⟩
  · intro i hh
    obtain ⟨s, ts, his⟩ := he i hh
    exact ⟨s, ts, (hissue ..).mpr his⟩
  · intro i s ts hh
    exact hi i s ts ((hissue ..).mp hh)
  · rintro ⟨i, s, ts, his⟩ h hh hn
    apply hl ⟨i, s, ts, (hissue ..).mp his⟩ h hh
    by_cases hg : h = g
    · simpa only [hg] using hstarted
    · simpa only [snoc_tr, ite_eq_right hg] using hn

private theorem objectAction_eq (hw : e.kind.ResourceWait) (m : Loc) (id : Ref) :
    objectAction (X.snoc g e r) X.async m id = objectAction X X.async m id := by
  have hnew : X.get (g, (X.tr g).length) = none := List.getElem?_eq_none (le_refl _)
  cases id with
  | thread i =>
    simp only [objectAction]
    rw [snoc_get]
    split_ifs with hi
    · subst i; rw [hnew]
      obtain ⟨_, k⟩ := e
      cases k <;> first | rfl | exact (show False from hw).elim
    · rfl
  | async i p =>
    cases p <;> simp only [objectAction]
    all_goals first
      | rw [hw.asyncSilent.snoc_issuedBy]
      | (rw [snoc_get]
         split_ifs with hi
         · subst i; rw [hnew]
           obtain ⟨_, k⟩ := e
           cases k <;> first | rfl | exact (show False from hw).elim
         · rfl)

private theorem tma (hw : e.kind.ResourceWait) (hX : Consistent L K A mem0 X) :
    TmaOk (X.snoc g e r) := by
  refine ⟨?_, ?_, ?_, snoc_arriveOk hX.tma.2.2.2⟩
  · simpa only [hw.asyncSilent.snoc_issuedBy, snoc_async] using hX.tma.1
  · simpa only [TcEffectsOk, snoc_async, snoc_mmaIssue hw.noTc, snoc_cpIssue hw.noTc,
      snoc_shiftIssue hw.noTc] using hX.tma.2.1
  · intro m
    obtain ⟨hv, hm, hc⟩ := hX.tma.2.2.1 m
    refine ⟨hv, ?_, ?_⟩
    · intro rec hr
      simpa only [snoc_async, objectAction_eq hw] using hm rec hr
    · intro id action hi
      apply hc id action
      simpa only [snoc_async, objectAction_eq hw] using hi

/-- Complete non-resource effect transport for a lane that has started. Source, grants,
readiness and waiting acyclicity are assembled separately. -/
theorem preserved_of_started (hw : e.kind.ResourceWait) (hX : Consistent L K A mem0 X)
    (hstarted : X.tr g ≠ []) : NonResourceEffects L A X (X.snoc g e r) := by
  have hbo : ∀ {x f : EvId}, f.2 < (X.tr f.1).length →
      (baseCausality L (X.snoc g e r) x f ↔ baseCausality L X x
          f) := fun hf => hw.baseCausality_old hX.cluster hf
  have helect {i : EvId} {pc mask label leader : Nat} :
      (X.snoc g e r).Elect i pc mask label leader ↔ X.Elect i pc mask label leader :=
    ⟨fun h => snoc_get_not_kind h (hw.ne id), Execution.le_get le_snoc⟩
  have hwarp {i : EvId} {mask label : Nat} :
      (X.snoc g e r).WarpBar i mask label ↔ X.WarpBar i mask label := snoc_kind_iff (hw.ne id)
  have hmat : isMatrix e = false := by
    obtain ⟨pc, k⟩ := e
    cases k <;> simp_all [Kind.ResourceWait, isMatrix]
  refine ⟨hX.cluster.preserving le_snoc rfl, by simpa only [ElectOk, helect] using hX.elect,
    by simpa only [WarpBarOk, hwarp] using hX.warpBar, clc hw hX hstarted, ?_, ?_,
    hX.atomic.snoc hX.store hX.tma.1 (fun _ _ _ => hw.ne id),
    hX.fenceSc.snoc (fun _ => hw.ne id) fun _ _ hb h => (hbo hb).mp h,
    hX.matrix.snoc hmat, hX.reduce.snoc (fun _ => hw.ne id),
    hX.tmemPair.mono le_snoc (fun _ => rfl) rfl,
    hX.tmemPairResult.snoc_not_wr (fun _ _ _ h => hw.ne id (congrArg Event.kind h)),
    ?_, readOk_snoc hX.tcRead hX.tcCommit hX.tma.2.2.1 hX.tma.2.1 hbo
      (fun _ _ _ _ h => (hw.ne id (congrArg Event.kind h)).elim),
    tma hw hX, readPreserved_snoc hX.tcCommit hX.tma.2.2.1 hbo⟩
  · intro i observation hi
    obtain ⟨⟨addr, hissue⟩, rest⟩ := hX.tensor i observation hi
    exact ⟨⟨addr, hw.asyncSilent.snoc_tensorIssue.mpr hissue⟩, rest⟩
  · intro i observation hi
    obtain ⟨⟨addr, hissue⟩, rest⟩ := hX.store i observation hi
    exact ⟨⟨addr, hw.asyncSilent.snoc_storeIssue.mpr hissue⟩, rest⟩
  · simp only [CommitOk, snoc_tracksMma_of_not_tc hw.noTc, snoc_commit hw.noTc, snoc_async]
    exact hX.tcCommit

/-- A previous cluster barrier shows that the lane has started. -/
theorem preserved (hw : e.kind.ResourceWait) (hX : Consistent L K A mem0 X)
    {source : Nat} {op : ClusterOp}
    (hlast : X.get (g, (X.tr g).length - 1) = some ⟨source, .cluster op⟩) :
    NonResourceEffects L A X (X.snoc g e r) := by
  apply hw.preserved_of_started hX
  intro he
  simp [Execution.get, he] at hlast

end Kind.ResourceWait
end
end PTX
