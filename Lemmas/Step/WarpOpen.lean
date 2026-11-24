-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.WarpAppend
public import Lemmas.Step.Released
public import Lemmas.Snoc.ExtensionSnocFrame
public import Lemmas.Snoc.SnocObjectHistory
public import Lemmas.Snoc.SnocConsistent

@[expose] public section

/-! # The obligations a lane's collective keeps by itself

A proof tool. While the lanes of a lane collective (`Kind.LaneColl`: the warp collectives and the
ballot) are appended one by one, the intermediate executions break the readiness of the new events
(DEP-ORDER) and the values of the collective (DEP-WARP-SHUFFLE, DEP-WARP-VOTE), which need every
lane. Every
other obligation that does not compare against an older execution is kept by each single append
(`WarpOpen.snoc_lane`): `WarpOpen` collects them. Thread order into older events is unchanged
(`baseCausality_snoc_old_lane`) when a new warp barrier carries an instance label no earlier warp
barrier of the warp has. -/

namespace PTX.Step
open PTX AsyncCopy
noncomputable section

/-- The obligations of a consistent execution other than its traces, read sources, memory
order, dependency order, kernel assumptions and the matching and values of warp collectives. -/
structure WarpOpen (L : Launch) (A : List Assumption) (Z : Execution) : Prop where
  ctaBar : CtaBarHistoryOk L Z
  clusterHistory : ClusterHistoryOk L Z
  matrix : MatrixOk L A Z
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

theorem _root_.PTX.Consistent.warpOpen (h : Consistent L K A mem0 Z) : WarpOpen L A Z :=
  ⟨h.ctaBar, h.cluster, h.matrix, h.clc, h.tensor, h.store, h.atomic, h.fenceSc, h.tmemPair,
    h.tmemPairResult, h.tcCommit, h.tcRead, h.reduce, h.tma⟩

theorem WarpOpen.effectValidity (h : WarpOpen L A Z) : EffectValidity L Z :=
  ⟨h.tma, h.tensor, h.store, h.clc, h.tmemPair, h.tcCommit⟩

/-- A new warp barrier of thread `g` carries an instance label that no warp barrier of `g`'s warp
followed by another event has. -/
def FreshWarpBar (L : Launch) (Z : Execution) (g : Nat) (e : Event) : Prop :=
  ∀ mask inst, e.kind = .warpBar mask inst → ∀ j pc, j.2 + 1 < (Z.tr j.1).length →
    Z.get j = some ⟨pc, .warpBar mask inst⟩ → ¬ SameWarp L g j.1

/-- Appending a lane collective adds no thread order into older events, when a new warp barrier
has a fresh instance label. -/
theorem baseCausality_snoc_old_lane (hcl : ClusterHistoryOk L Z) (hw : e.kind.LaneColl)
    (hfresh : FreshWarpBar L Z g e) {a b : EvId} (hbo : b.2 < (Z.tr b.1).length) :
    baseCausality L (Z.snoc g e r) a b ↔ baseCausality L Z a b :=
  ⟨fun h => baseCausality_old_of_step (fun hb => snoc_step_old_of hcl
    (.of_noWrite (fun _ _ => hw.ne id) (fun _ _ _ => hw.ne id))
    (fun _ _ => snoc_ctaBarK (fun _ _ _ => hw.ne id))
    (fun _ _ => snoc_ctaBarArrivalK (fun _ _ _ => hw.ne id)) hb
    (msync_snoc_old (fun _ _ _ _ => hw.ne id) hb) hfresh
    (fun _ => hw.ne id)) h hbo, baseCausality_snoc⟩

/-- **One lane's collective or ballot keeps the obligations of `WarpOpen`**, once the lane has
started or its cluster has been launched. -/
theorem WarpOpen.snoc_lane (hZ : WarpOpen L A Z) (hw : e.kind.LaneColl)
    (hst : Z.tr g ≠ [] ∨ Launched L Z g) (hfresh : FreshWarpBar L Z g e) :
    WarpOpen L A (Z.snoc g e r) := by
  have htc : ∀ k, e.kind ≠ .tc k := fun _ => hw.ne id
  have hbo : ∀ {x f : EvId}, f.2 < (Z.tr f.1).length →
      (baseCausality L (Z.snoc g e r) x f ↔ baseCausality L Z x f) :=
    fun hf => baseCausality_snoc_old_lane hZ.clusterHistory hw hfresh hf
  have hv := hZ.effectValidity
  have le : Z.le (Z.snoc g e r) := le_snoc
  refine ⟨hZ.ctaBar.snoc, hZ.clusterHistory.preserving le rfl,
    hZ.matrix.snoc (by obtain ⟨pc, k⟩ := e; cases k <;> first | exact (hw : False).elim | rfl),
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

end
end PTX.Step
