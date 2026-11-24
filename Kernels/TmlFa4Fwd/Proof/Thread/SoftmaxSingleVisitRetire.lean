-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTerminalOrdinals
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxActiveGroupProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread Correction Protocol.Statistics

/-- The actual one-visit denominator and its terminal statistics generation. -/
structure SingleVisitTerminalInput (p : Params) (l : Launch) (X : Execution) (g : Nat) where
  cap : Nat
  past : Nat
  denominator : OpeningDenominatorCursor p l X g 1 cap past
  capPositive : 0 < cap
  capSigned : cap < 2^31
  pastSigned : past+256 < 2^31
  released : denominator.cursor.pos+3 = (X.tr g).length →
    CtaBarrier.Released l.block (X.barriers (g/l.block)) (3+warpIndex l g)
      (((X.tr g).take (denominator.cursor.pos+2)).countP (Execution.isBarId (3+warpIndex l g)))

theorem activeSchedulerGeometry {p : Params} {l : Launch} {X : Execution}
    {g first n : Nat} {warp : Fin 8} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 3212
      (fun lane => groupRouteFacts p l (warpLane l g lane) warp first) n 0 ends)
    (lane : Nat) (hl : lane < 32) :
    Nonempty (OpeningTripCursor l X (warpLane l g lane) 3212
      (RowDrainRole.softmax.frame p l (warpLane l g lane))) := by
  let u := terminalWarpLaneCursor cur lane hl
  have hFrame : Holds u.ready.regs (RowDrainRole.softmax.frame p l (warpLane l g lane)) := by
    dsimp only [RowDrainRole.frame,RowDrainRole.laneReg,RowDrainRole.ctaReg]
    refine ⟨holds_mem u.checkpoint.2.2.2.2 ?_,holds_mem u.checkpoint.2.2.2.2 ?_,
      holds_mem u.checkpoint.2.2.2.2 ?_,trivial⟩ <;>
      simp [groupRouteFacts,fallbackBaseFrame,schedulerEntry,dispatchOutput,dispatchInput]
  exact ⟨⟨u.pos,u.before,u.ready,u.ending,u.positive,u.bounded,u.released,
    u.checkpoint.mono hFrame,u.recorded,u.remaining,u.localSteps⟩⟩

/-- The actual single-visit softmax warp publishes its terminal row and runs the complete
scheduler rescan, retaining parity one until the final credit. -/
theorem terminalFinishedOfSingleVisitWarp {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) {g batch : Nat} (hg : g < l.threads)
    (hw : warpIndex l g < 8) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hInputs : ∀ lane < 32, Nonempty (SingleVisitTerminalInput p l X (warpLane l g lane))) :
    ∀ lane < 32, (∃ j, Scores.Publishes X (warpLane l g lane,j) .final) ∧
      TerminalSchedulerFinished l X (warpLane l g lane) ⟨warpIndex l g,hw⟩ 1 := by
  classical
  let warp : Fin 8 := ⟨warpIndex l g,hw⟩
  have hWork := hHi.trans_le
    (Nat.mul_le_mul_right p.heads (tilePrefix_mono p (Nat.succ_le_of_lt hb)))
  obtain ⟨_,_,_,_,_,⟨geometry⟩⟩ := activeGroupOfMaximal hp hMax hg hw hCuQ hWork
  obtain ⟨count,_,⟨active⟩⟩ := activeWarpOfMaximal hp hMax hg hw hCuQ hb hLo hHi
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hEach (lane : Nat) (hl : lane < 32) :
      ∃ drain : TerminalDrainLane p l X (warpLane l g lane) warp 1,
        (∃ j, Scores.Publishes X (warpLane l g lane,j) .final) ∧
        ((X.tr (warpLane l g lane)).take drain.first.pos).countP Execution.isShfl = count ∧
        ((X.tr (warpLane l g lane)).take drain.first.pos).countP isFullWarpVote = 1 := by
    let thread := warpLane l g lane
    have hSame := (Step.sameWarp_lane hBlock hg hl).1
    have hThread : thread < l.threads := hSame.1.2.1
    have hWarp : warp.val = warpIndex l thread := hSame.2
    have hSoft : warpIndex l thread < 8 := hWarp ▸ warp.isLt
    have hFin : (⟨warpIndex l thread,hSoft⟩ : Fin 8) = warp := Fin.ext hWarp.symm
    obtain ⟨source⟩ := activeSchedulerGeometry geometry lane hl
    obtain ⟨input⟩ := hInputs lane hl
    obtain ⟨row,hPos⟩ := input.denominator.terminalRowOfSingleVisit hp hSoft
      input.capPositive input.capSigned input.pastSigned source
    have hSync : row.pos+3 = (X.tr thread).length →
        CtaBarrier.Released l.block (X.barriers (thread/l.block)) (3+warpIndex l thread)
          (((X.tr thread).take (row.pos+2)).countP (Execution.isBarId (3+warpIndex l thread))) := by
      rw [hPos]
      exact input.released
    have hBytes : (scoreValue input.denominator.maximum).bytes = 4 := by
      cases input.denominator.maximum <;> rfl
    obtain ⟨hPub,⟨out⟩⟩ := terminalDrainLaneOfRow hp hMax hCuQ hThread
      ⟨warpIndex l thread,hSoft⟩ rfl rfl hBytes row hSync
    rw [hFin] at out
    have hOrd := terminalOrdinalsOfActiveCursor (terminalWarpLaneCursor active lane hl) out.first
    exact ⟨out,⟨_,hPub⟩,(hOrd.1.trans (active.ordinals.shfl lane hl)),
      (hOrd.2.trans (active.ordinals.vote lane hl))⟩
  choose drain hDrain using hEach
  have hFinish := terminalFinishedOfDrainLanes hp hMax hCuQ hg hw hWork (fun _ => 1) drain
    (fun lane hl => (hDrain lane hl).2)
  exact fun lane hl => ⟨(hDrain lane hl).1,hFinish lane hl⟩

/-- The completed correction cohort releases the single-visit softmax warp's actual
allocation rendezvous arrivals. -/
theorem allocationArrivalsOfSingleVisitWarp {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) (hDeps : CreditAcquireDependencies l X) {g batch : Nat}
    (hg : g < l.threads) (hw : warpIndex l g < 8) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTrips : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1)
    (hCredits : TerminalCorrectionCredits l X (g/l.block) (stageOf ⟨warpIndex l g,hw⟩) 1)
    (hInputs : ∀ lane < 32, Nonempty (SingleVisitTerminalInput p l X (warpLane l g lane))) :
    ∀ lane < 32, ∃ j, FinalAllocationArrival X (warpLane l g lane,j) .arrive := by
  let warp : Fin 8 := ⟨warpIndex l g,hw⟩
  have hFinish := terminalFinishedOfSingleVisitWarp hp hMax hCuQ hg hw hb hLo hHi hInputs
  have hCredit := terminalStatisticsPhaseOfCredits hp hMax.1 hDeps hb hLo hHi (stageOf warp)
  rw [hTrips] at hCredit
  obtain ⟨state,hState,hPhase⟩ := hCredit hCredits
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  intro lane hl
  let thread := warpLane l g lane
  have hSame := (Step.sameWarp_lane hBlock hg hl).1
  have hCta : thread/l.block = g/l.block := hSame.1.2.2.symm
  have hAvailable : TerminalCreditAvailable l X thread (stageOf warp) 1 := by
    unfold TerminalCreditAvailable
    rw [hCta]
    exact ⟨state,hState,by rw [hPhase]; decide⟩
  exact finalAllocationArrivalOfSchedulerFinished hp hMax hSame.1.2.1 warp
    (by decide) (hFinish lane hl).2 hAvailable

end PTX.Kernels.TmlFa4Fwd.Softmax
