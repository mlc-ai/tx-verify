-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningCorrectionStatistics
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionBallotWindow
import all Kernels.TmlFa4Fwd.Proof.Thread.Correction
import all Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTensorSchedule
import Lemmas.Flow.CountTake
import Kernels.TmlFa4Fwd.Proof.CorrectionLseWriters

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread

/-- Before the second opening statistics wait the correction warp has issued
its request-selection ballot. Neither rescale stage has yet issued a ballot. -/
theorem firstRescaleVoteBase {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} (hg : g < l.threads)
    (hw : 8 ≤ warpIndex l g ∧ warpIndex l g < 12)
    (hWork : g/l.block < tilePrefix p p.batch*p.heads)
    (hWait : CorrectionWaits X (g,j) .initial 1) :
    ((X.tr g).take (j+1)).countP isFullWarpVote = 1 := by
  obtain ⟨e,he,ha⟩ := hWait
  have hKind := correctionStatsWait hp hX he ha
  have hPc : e.pc = 7988 := statsLookup e .initial 1 (correctionAction_inv ha).1
  have hEvent : X.get (g,j) = some ⟨7988,.bar (statsBarrierId l g 1) (some 64) .sync⟩ := by
    rw [he]
    exact congrArg some (by cases e; simp_all)
  have hSelf : warpLane l g (laneOf l g) = g := Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  obtain ⟨_,_,_,_,_,_,active,follow⟩ := correctionActiveTileOfEventWithVote hp hX hg hw.1 hw.2
    (show laneOf l g < 32 from Nat.mod_lt _ (by decide)) hWork (by decide : 7884 < 7988)
    (hSelf.symm ▸ hEvent)
  have hOrd := correctionRescaleVoteOrdinalFromActive hX active follow (by decide : 7988 < 8447)
  dsimp only at hOrd
  rw [hSelf] at hOrd
  have hRange := follow.before
  have hz (stage : Fin 2) :
      (((X.tr g).drop (active.pos (laneOf l g))).take (j-active.pos (laneOf l g))).countP
        (isRescaleStageVote stage) = 0 := by
    apply List.countP_eq_zero.mpr
    intro f hf hm
    obtain ⟨n,hn⟩ := List.mem_iff_getElem?.mp hf
    have hBound := ((List.getElem?_eq_some_iff.mp hn).1).trans_le (List.length_take_le ..)
    rw [List.getElem?_take_of_lt hBound,List.getElem?_drop] at hn
    have hIn : f ∈ (X.tr g).take (j+1) := by
      apply List.mem_of_getElem? (i := active.pos (laneOf l g)+n)
      rwa [List.getElem?_take_of_lt (by omega)]
    exact List.countP_eq_zero.mp (noRescaleMarkerBeforeInitial hX hEvent stage) f hIn hm
  rw [hz 0,hz 1] at hOrd
  rw [countP_take_succ_false hEvent (by rfl)]
  exact hOrd

/-- The second initial statistics wait precedes every tensor collective in
the correction warp, so the first taken rescale body starts at ordinal zero. -/
theorem firstRescaleTensorBase {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} (hw : 8 ≤ warpIndex l g ∧ warpIndex l g < 12)
    (hWait : CorrectionWaits X (g,j) .initial 1) :
    ((X.tr g).take (j+1)).countP isTcColl = 0 := by
  obtain ⟨e,he,ha⟩ := hWait
  have hPc : e.pc = 7988 := statsLookup e .initial 1 (correctionAction_inv ha).1
  apply List.countP_eq_zero.mpr
  intro f hf hColl
  obtain ⟨r,hr⟩ := List.mem_iff_getElem?.mp hf
  have hR := ((List.getElem?_eq_some_iff.mp hr).1).trans_le (List.length_take_le ..)
  rw [List.getElem?_take_of_lt hR] at hr
  have hBand := correctionCollectiveBand hp hX hw.1 hw.2 hr hColl
  have hOrder := traceOrderOfSegmentFloor (floor := 7989) hX correctionBeforeRescaleFloor
    (fun site hSite hm => by
      simp only [Assumptions.swExp2Sites,List.mem_cons,List.not_mem_nil,or_false] at hm
      omega) he hr (by omega) (by omega)
  omega

end PTX.Kernels.TmlFa4Fwd.Correction
