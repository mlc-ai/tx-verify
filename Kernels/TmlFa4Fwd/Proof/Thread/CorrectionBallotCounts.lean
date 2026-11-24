-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionRescaleOrdinal
public import Kernels.TmlFa4Fwd.Proof.CorrectionLseWriters
import Kernels.TmlFa4Fwd.Proof.CorrectionObservedRescaleEntry
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NotClc
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.Flow Epilogue Prologue
open _root_.PTX.Kernels.TmlFa4Fwd.Correction

private theorem noRescaleBallotBeforeInitialWait {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g pos : Nat}
    (hWait : X.get (g,pos+5) = some ⟨7988,.bar (statsBarrierId l g 1) (some 64) .sync⟩)
    (stage : Fin 2) : ((X.tr g).take (pos+6)).countP (isRescaleStageVote stage) = 0 := by
  have hFloor :
      (kernel.code.drop 7989).all (fun i => Thread.staysPastEvent 7989 i.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hSegments (site : Nat) (hLo : 7989 ≤ site) (hSite : site ∈ Assumptions.swExp2Sites) :
      ∀ seg, PTX.Assumption.cuteExp2.matchAt kernel site = some seg → 7989 ≤ seg.stop := by
    simp only [Assumptions.swExp2Sites, List.mem_cons, List.not_mem_nil, or_false] at hSite
    omega
  apply List.countP_eq_zero.mpr
  intro e hMem hVote
  obtain ⟨j,hGet⟩ := List.mem_iff_getElem?.mp hMem
  have hj : j < pos+6 := ((List.getElem?_eq_some_iff.mp hGet).1).trans_le (List.length_take_le ..)
  rw [List.getElem?_take_of_lt hj] at hGet
  have hMark : e.pc = correctionRescaleMarkPc stage + 3 := beq_iff_eq.mp hVote
  have hLate : 7989 ≤ e.pc := by rw [hMark]; fin_cases stage <;> decide
  have hOrder := traceOrderOfSegmentFloor hX hFloor hSegments hWait hGet
    (show 7988 < 7989 by decide) hLate
  omega

/-- A correction lane reaching any event after the rescale loop has executed exactly one
rescale ballot per remaining KV block and stage. The request is the one actually selected. -/
theorem correctionRescaleBallotCountOfTail {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} {e : Event} (hLo : 8 ≤ warpIndex l g) (hHi : warpIndex l g < 12)
    (hWork : g / l.block < tilePrefix p p.batch * p.heads)
    (hUsedK : ∀ i < p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.usedKBase + 4*i)).at k))
    (he : X.get (g,j) = some e) (hTail : 8447 ≤ e.pc) (stage : Fin 2) :
    ∃ batch < p.batch, tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch+1) * p.heads ∧
      (X.tr g).countP (isRescaleStageVote stage) =
        Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 - 1 := by
  let lane := laneOf l g
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hg := event_thread_lt hX he
  have hSelf : warpLane l g lane = g := Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  have he' : X.get (warpLane l g lane,j) = some e := hSelf.symm ▸ he
  obtain ⟨batch,hBatch,hCtaLo,hCtaHi,ends,shuffles,votes,active,hActive⟩ :=
    correctionActiveTileOfEvent hp hX hg hLo hHi hl hWork (by omega) he'
  have hr := (active.continuation lane hl).after_local_nonempty
    (active.localSteps lane hl) hActive.nonempty
  obtain ⟨u,hU,hPos,_,_,hInit,hRun⟩ := correctionLaneBeforeRescaleOfEvent
    hp hX hBatch hCtaLo hCtaHi (active.checkpoint lane hl) hr hUsedK hActive.before
      (by omega) he'
  have hPre := noRescaleBallotBeforeInitialWait hX hInit stage
  have hMember : e ∈ (X.tr (warpLane l g lane)).drop (active.pos lane+6) := by
    apply List.mem_of_getElem? (i := j-(active.pos lane+6))
    rwa [List.getElem?_drop,Nat.add_sub_of_le hPos]
  obtain ⟨_, hWalk⟩ := Mma.walkFromRun hRun
  obtain ⟨_, v, hv, hV⟩ := correctionLaneRescaleSetup hp hBatch hCtaLo hCtaHi hU
  rcases Mma.advanceWalkLocals hv hWalk with hNil | ⟨_,_,_,hRest⟩
  · rw [hNil] at hMember
    cases hMember
  let tile := (assignedCoordinates p batch (g/l.block)).1
  let blocks := Mma.trips p batch tile
  have hEntry : v.pc = (if blocks < 2 then 8447 else 8006) := hV.1
  have hCount : ((X.tr (warpLane l g lane)).drop (active.pos lane+6)).countP
      (isRescaleStageVote stage) = blocks-1 := by
    by_cases hSkip : blocks < 2
    · have hPc : v.pc = 8447 := hEntry.trans (ite_eq_left hSkip)
      rw [correctionRescaleVoteNone stage hPc.ge hRest]
      omega
    · have hPc : v.pc = 8006 := hEntry.trans (ite_eq_right hSkip)
      have hSeed : v.regs 7278 = some (b32 (2^32-blocks)) := by
        have h := hV.2.2.2.2
        unfold correctionRescaleSetupFacts at h
        rw [ite_eq_right hSkip] at h
        exact h.1
      have hK := (hp.lengths batch hBatch).2.2
      have hTrips : blocks ≤ (p.kLength batch+127)/128 :=
        (Mma.trips_bounds hp hBatch (assignedCoordinates_valid hp hCtaLo hCtaHi).1).2.1
      exact correctionRescaleVoteCount stage hPc (by rw [hV.2.1]; decide)
        (Nat.le_of_not_gt hSkip) (by omega) hSeed hRest hMember hTail
  refine ⟨batch,hBatch,hCtaLo,hCtaHi,?_⟩
  calc
    (X.tr g).countP (isRescaleStageVote stage) =
        (X.tr (warpLane l g lane)).countP (isRescaleStageVote stage) := by rw [hSelf]
    _ = blocks-1 := by
      rw [← List.take_append_drop (active.pos lane+6) (X.tr (warpLane l g lane)),
        List.countP_append, hPre, hCount, Nat.zero_add]

end PTX.Kernels.TmlFa4Fwd.Thread
