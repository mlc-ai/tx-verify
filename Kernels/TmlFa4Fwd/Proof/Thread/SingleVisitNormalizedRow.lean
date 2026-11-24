-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SingleVisitNormalization
public import Kernels.TmlFa4Fwd.Proof.CorrectionFinalStageFrame
import Kernels.TmlFa4Fwd.Proof.CorrectionObservedRescaleEntry
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStatsExit
import Kernels.TmlFa4Fwd.Proof.Thread.AllocationBarrierOrder
import Lemmas.Step.ExitLast
import Kernels.TmlFa4Fwd.Proof.CorrectionLseWriters

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Correction
open PTX PTX.Proof PTX.Flow Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Correction
open PTX.Kernels.TmlFa4Fwd.Mma (trips)

noncomputable section

theorem finalStageZeroEntry {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g batch lane pos : Nat} {t : TState}
    (ht : At t 8447 (correctionBeforeRescale p l g batch lane))
    (hr : Run kernel Assumptions.all l (warpLane l g lane) t
      ((X.tr (warpLane l g lane)).drop pos) none) :
    ∃ u, At u (statsBarrierPc 0 false) (correctionFinalStageFacts p l g batch lane 0 0 0) ∧
      Run kernel Assumptions.all l (warpLane l g lane) u
        ((X.tr (warpLane l g lane)).drop (pos+1)) none := by
  let F := correctionBeforeRescale p l g batch lane
  have hFresh (rv : Nat × Value) (hm : rv ∈ F) : rv.1 ≠ 7134 ∧ rv.1 ≠ 9257 := by
    have hm' := List.mem_map_of_mem (f := Prod.fst) hm
    constructor <;> intro h <;> rw [h] at hm' <;>
      exact (of_decide_eq_true rfl : _ ∉ F.map Prod.fst) hm'
  obtain ⟨s,_,hs,hS⟩ := finalizeLayoutEntry hp ht
    (by simp [correctionBeforeRescale,tileSetupFrame,correctionTileGeometryFacts])
    (by simp [correctionBeforeRescale,tileSetupFrame,correctionActiveTileFacts,
      correctionTileFrame,afterCreditFacts,creditFacts])
    (by simp [correctionBeforeRescale,tileSetupFrame,correctionTileGeometryFacts])
    (by simp [correctionBeforeRescale,tileSetupFrame,correctionTileGeometryFacts])
    (by simp [correctionBeforeRescale,tileSetupFrame,correctionTileGeometryFacts])
    hFresh (by set_option maxRecDepth 100000 in kernel_rfl) hr
  exact ⟨s,hs,hS⟩

private theorem observedSingleVisitStageZeroEntry {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFootprint : OutputFootprint p X) {g batch lane index : Nat} (hg : g < l.threads)
    (hWarpLo : 8 ≤ warpIndex l g) (hWarpHi : warpIndex l g < 12) (hl : lane < 32)
    (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1) * p.heads)
    (hTrip : trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1)
    {event : Event} (hLate : 7988 < event.pc)
    (he : X.get (warpLane l g lane,index) = some event)
    (hExit : Exited X (warpLane l g lane)) :
    ∃ pos u, At u (statsBarrierPc 0 false) (correctionFinalStageFacts p l g batch lane 0 0 0) ∧
      Run kernel Assumptions.all l (warpLane l g lane) u
        ((X.tr (warpLane l g lane)).drop pos) none := by
  have hWork := hHi.trans_le (Nat.mul_le_mul_right p.heads
    (tilePrefix_mono p (show batch+1 ≤ p.batch by omega)))
  obtain ⟨hCuQ,hUsedK⟩ := hFootprint.metadataProtected hp
  obtain ⟨chosen,hChosen,hBegin,hEnd,ends,_,_,active,hActive⟩ :=
    correctionActiveTileOfEvent hp hX hg hWarpLo hWarpHi hl hWork
      (show 7884 < event.pc by omega) he
  obtain ⟨_,_,hUnique⟩ := tileBatch_existsUnique p hWork
  have hEq := (hUnique chosen ⟨hChosen,hBegin,hEnd⟩).trans (hUnique batch ⟨hb,hLo,hHi⟩).symm
  subst chosen
  have hRun := (active.continuation lane hl).after_local_nonempty
    (active.localSteps lane hl) hActive.nonempty
  obtain ⟨s,hs,hIndex,_,_,_,hSuffix⟩ := correctionLaneBeforeRescaleOfEvent hp hX hb hLo hHi
    (active.checkpoint lane hl) hRun hUsedK hActive.before hLate he
  obtain ⟨_,u,hLocal,hU⟩ := correctionLaneRescaleSetup hp hb hLo hHi hs
  have hAt : At u 8447 (correctionBeforeRescale p l g batch lane) := by
    simpa [correctionRescaleSetupFacts,hTrip] using hU
  obtain ⟨finish,⟨pc,kind⟩,hExit,hKind⟩ := hExit
  change kind = .exit at hKind
  subst kind
  have hLast := Execution.exit_last hX (event_thread_lt hX hExit) hExit
  have hExtent := (List.getElem?_eq_some_iff.mp he).1
  change index < (X.tr (warpLane l g lane)).length at hExtent
  let suffix := (X.tr (warpLane l g lane)).drop (active.pos lane+6)
  have hSuffixExit : suffix[finish-(active.pos lane+6)]? = some ⟨pc,.exit⟩ := by
    change finish+1 = (X.tr (warpLane l g lane)).length at hLast
    unfold suffix
    rwa [List.getElem?_drop,Nat.add_sub_of_le (show active.pos lane+6 ≤ finish by omega)]
  have hEnd : ends lane = none := by
    cases h : ends lane with
    | none => rfl
    | some final =>
      rw [h] at hSuffix
      exact (hSuffix.no_exit hSuffixExit).elim
  rw [hEnd] at hSuffix
  obtain ⟨state,hState,hRest⟩ := finalStageZeroEntry hp hAt (hSuffix.after_local (run_rtg hLocal))
  exact ⟨active.pos lane+7,state,hState,hRest⟩

/-- The correction lane produced the selected row's sixteen normalized chunks. -/
def SingleVisitNormalizedRow (p : Params) (l : Launch) (X : Execution)
    (g batch : Nat) (stage : Fin 2) (start : Nat) : Prop :=
  let coords := assignedCoordinates p batch (g/l.block)
  let row := stageRow coords.1 stage + rowOf l g
  ∃ (old : Fin 16 → Nat → ℝ) (reciprocal : ℝ),
    NormalizedOutput l X g start stage old reciprocal ∧
    ∀ (chunk : Fin 16) (k : Fin 8), old chunk k.val * reciprocal =
      attention p batch coords.2 row (8*chunk.val+k.val)

/-- A completed one-visit correction lane publishes the exact normalized row in every
valid stage. The selected coordinates and both stages use the lane's actual continuation. -/
theorem singleVisitNormalizedRowOfComplete {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X) (hFootprint : OutputFootprint p X) {g batch : Nat}
    (hg : g < l.threads) (hWarpLo : 8 ≤ warpIndex l g) (hWarpHi : warpIndex l g < 12)
    (stage : Fin 2) (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1) * p.heads)
    (hTrip : trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1)
    (hRow : stageRow (assignedCoordinates p batch (g/l.block)).1 stage + rowOf l g <
      p.qLength batch) : ∃ start, SingleVisitNormalizedRow p l X g batch stage start := by
  let lane := laneOf l g
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hSelf : warpLane l g lane = g :=
    Nat.sub_add_cancel ((Nat.mod_le ..).trans (Nat.mod_le ..))
  have hWork := hHi.trans_le (Nat.mul_le_mul_right p.heads
    (tilePrefix_mono p (show batch+1 ≤ p.batch by omega)))
  have hExit := exitedOfComplete hX hDone hg
  obtain ⟨finish,pc,hFinish⟩ : ∃ finish pc, X.get (g,finish) = some ⟨pc,.exit⟩ := by
    obtain ⟨finish,⟨pc,kind⟩,he,hKind⟩ := hExit
    change kind = .exit at hKind
    subst kind
    exact ⟨finish,pc,he⟩
  obtain ⟨arrival,_,mode,hArrival⟩ :=
    finalAllocationArrivalBeforeExit hp hX (by omega) ⟨pc,hFinish⟩
  have hAn := hArrival.correctionDecoded hp hX hWarpLo hWarpHi
  obtain ⟨index,addr,vals,he⟩ := correctionFinalOutputLoadOfActiveTail hp hX
    hWarpLo hWarpHi hWork hAn
  have hLate : 7988 < finalizeLoadPc 1 0 := by decide
  have he' : X.get (warpLane l g lane,index) = some
      ⟨finalizeLoadPc 1 0,.tc (.ld addr vals .s32x32b)⟩ := by rwa [hSelf]
  obtain ⟨pos,t,ht,hT⟩ :=
    observedSingleVisitStageZeroEntry hp hX hFootprint hg hWarpLo hWarpHi hl hb hLo hHi
      hTrip hLate he' (hSelf.symm ▸ hExit)
  rw [hSelf] at hT
  have hRow0 : stageRow (assignedCoordinates p batch (g/l.block)).1 0 + rowOf l g <
      p.qLength batch := by
    unfold stageRow at *
    omega
  have hFrame0 (sum maximum : ℝ) :
      FinalStageFrame l g 0 sum maximum (correctionFinalStageFacts p l g batch lane 0 0 0) := by
    simpa only [hSelf] using correctionFinalStageFrame p l g batch lane 0 0 sum maximum 0
  obtain ⟨sum0,max0,start0,v,_,hOut0,hExact0,hV,hRest0⟩ :=
    singleVisitNormalizedStage hp hX hDone hFootprint 0 hb hLo hHi hTrip hRow0 ht hFrame0 hT
  fin_cases stage
  · exact ⟨start0,_,_,hOut0,hExact0⟩
  · have hSecond : At v (statsBarrierPc 1 false)
        (correctionFinalStageFacts p l g batch lane sum0 max0 1) :=
      hV.mono ⟨hV.2.2.2.2.2.1,hV.2.2.2.2.2.2.2⟩
    have hFrame1 (sum maximum : ℝ) :
        FinalStageFrame l g 1 sum maximum
          (correctionFinalStageFacts p l g batch lane sum0 max0 1) := by
      simpa only [hSelf] using correctionFinalStageFrame p l g batch lane sum0 max0 sum maximum 1
    obtain ⟨sum,max,start,_,_,hOut,hExact,_,_⟩ :=
      singleVisitNormalizedStage hp hX hDone hFootprint 1 hb hLo hHi hTrip hRow
        hSecond hFrame1 hRest0
    exact ⟨start,_,_,hOut,hExact⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Correction
