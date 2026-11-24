-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvPacketProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.SchedulerWarpProgress
public import Kernels.TmlFa4Fwd.Proof.MmaPvEntry
import Kernels.TmlFa4Fwd.Proof.EpilogueCoordinateFrame
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSharedFootprint

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Proof PTX.Flow Epilogue Prologue
open PTX.Kernels.TmlFa4Fwd.Correction (OpeningTripCursor)

/-- Each elected lane carries its elected predicate and its packet operands into the setup. -/
def pvElectedFrame (l : Launch) (g : Nat) (block : Fin 4) (use phase : Nat)
    (accum : Bool) (extra : List (Nat × Value)) (lane : Nat) (leader : Fin 32) :
    List (Nat × Value) :=
  ((pvSite block).guard,.pred (laneOf l (warpLane l g lane) == leader.val)) ::
    (pvEntryFacts l block use phase accum ++ extra)

/-- A single elected lane issued each fragment of the specified packet. -/
def PvPacketIssues (l : Launch) (X : Execution) (g : Nat)
    (block : Fin 4) (use : Nat) (accum : Bool) : Prop :=
  ∃ issuer, SameWarp l g issuer ∧ ∀ step : Fin 8, ∃ index,
    Thread.PvInstruction X (issuer,index) block step (outputColumn (pvSite block).stage)
      (pvOperands l issuer block step use) (if step.val = 0 then accum else true)
      (List.replicate 4 0)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g shuffles votes : Nat} (hg : g < l.threads)
    (block : Fin 4) (use phase : Nat) (accum : Bool) (hParity : phase < 2) (leader : Fin 32)
    {extra : List (Nat × Value)}
    (hExtra : ∀ pair ∈ extra, pair.1 ≠ (pvSite block).b-2 ∧ pair.1 ≠ (pvSite block).b ∧
      pair.1 ≠ (waitSite (pvTailWait block)).result)
    (hSetup : ((kernel.code.drop ((electSite (pvElection block)).pc+1)).take 7).all
      (fun ins => (extra.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g ((electSite (pvElection block)).pc+1)
      (fun lane => pvElectedFrame l g block use phase accum extra lane leader) shuffles votes ends)
include hp hMax hg block use phase accum hParity leader hExtra hSetup cur

/-- Assemble and execute one elected PV block in all lanes. The ordinary MMA issues and
mbarrier waits preserve the shuffle and ballot ordinals used by the later warp collectives. -/
theorem pvWarpPacketWithPollCounts
    (hReady : ∀ lane < 32, PvTailReadyWithOrdinal l X (warpLane l g lane) block phase extra
      (cur.pos lane)) :
    ∃ newEnds, ∃ next : SchedulerWarpReached l X g (pvPc block 7+1)
      (fun _ => extra) shuffles votes newEnds,
      PvPacketIssues l X g block use accum ∧
      ∀ lane < 32,
        elections X (warpLane l g lane) (next.pos lane) =
          elections X (warpLane l g lane) (cur.pos lane) ∧
        cur.pos lane ≤ next.pos lane ∧
        PvPollDelta X (warpLane l g lane) (cur.pos lane) (next.pos lane)
          ⟨.shared,(warpLane l g lane)/l.block,pvTailAddress l block⟩ true := by
  classical
  let thread := warpLane l g
  let _ : Nonempty TState := ⟨cur.state 0⟩
  have hInfo := pvEntrySites block
  have hStraight : ((kernel.code.drop ((electSite (pvElection block)).pc+1)).take 6).all
      (fun ins => schedulerFallsThrough ins.op) = true := by
    set_option maxRecDepth 100000 in
    fin_cases block <;> kernel_rfl
  have hEach (lane : Nat) (hl : lane < 32) :
      ∃ pos before state ending,
        At state (pvPc block 7+1) extra ∧ 0 < pos ∧ pos ≤ (X.tr (thread lane)).length ∧
        (pos = (X.tr (thread lane)).length → Step.Released l X (thread lane)) ∧
        Run kernel Assumptions.all l (thread lane) {}
          ((X.tr (thread lane)).take pos) (some before) ∧
        Run kernel Assumptions.all l (thread lane) before ((X.tr (thread lane)).drop pos) ending ∧
        Relation.ReflTransGen (Tau kernel Assumptions.all l (thread lane)) before state ∧
        PvOrdinalsPreserved X (thread lane) (cur.pos lane) pos ∧ cur.pos lane ≤ pos ∧
        PvPollDelta X (thread lane) (cur.pos lane) pos
          ⟨.shared,(thread lane)/l.block,pvTailAddress l block⟩ true ∧
        (lane = leader.val → ∀ step : Fin 8, ∃ index,
          Thread.PvInstruction X (thread lane,index) block step (outputColumn (pvSite block).stage)
            (pvOperands l (thread lane) block step use) (if step.val = 0 then accum else true)
            (List.replicate 4 0)) := by
    let lead := laneOf l (thread lane) == leader.val
    have hSame := (Step.sameWarp_lane (by rw [hp.block]) hg hl).1
    have hThread : thread lane < l.threads := hSame.1.2.1
    have ht := cur.checkpoint lane hl
    have hF := (holds_append ..).mp ht.2.2.2.2.2
    have ht' : At (cur.state lane) ((electSite (pvElection block)).pc+1)
        (((pvSite block).guard,.pred lead) :: pvEntryFacts l block use phase accum) :=
      ht.mono ⟨ht.2.2.2.2.1,hF.1⟩
    obtain ⟨u,hr,hu⟩ := pvLocalSetup hp (thread lane) block use phase accum lead _ ht'
    have hAll := localRun hInfo.2.2.2.1 (hInfo.1.trans_le hInfo.2.2.2.2) ht.1 hStraight hr
    have huExtra : Holds u.regs extra := by
      apply holdsSchedulerFrame (regs := extra.map Prod.fst) hF.2
      · exact fun _ h => schedulerLocalFrame (len := 7) hSetup hStraight hr ht.1.ge
          (by rw [ht.1]) h
      · exact fun _ => List.mem_map_of_mem
    let atFirst : OpeningTripCursor l X (thread lane) (pvPc block 0)
        (pvIssueFrame l block use phase accum lead 0 ++ extra) :=
      ⟨cur.pos lane,cur.before lane,u,ends lane,cur.positive lane hl,cur.bounded lane hl,
        cur.released lane hl,hu.mono ((holds_append ..).mpr ⟨hu.2.2.2.2,huExtra⟩),
        cur.recorded lane hl,cur.continuation lane hl,(cur.localSteps lane hl).trans (run_rtg hAll)⟩
    obtain ⟨after,hCounts,hEnd,hPolls,hEvents⟩ := pvLanePacketOfMaximalWithPollCounts hp hMax
      hThread block use phase accum lead hParity 0 hExtra atFirst (fun _ => hReady lane hl)
    refine ⟨after.pos,after.before,after.ready,after.ending,
      after.checkpoint.mono ((holds_append ..).mp after.checkpoint.2.2.2.2).2,
      after.positive,after.bounded,after.released,after.recorded,after.remaining,
      after.localSteps,hCounts,hEnd,hPolls,?_⟩
    intro hLeader step
    have hLane := (Step.sameWarp_lane (by rw [hp.block]) hg hl).2
    have hLead : lead = true := beq_iff_eq.mpr (hLane.trans hLeader)
    obtain ⟨index,_,_,he⟩ := hEvents step (Nat.zero_le _) hLead
    exact ⟨index,Thread.PvInstruction.of_decoded he⟩
  choose! pos before state ending hAt hPos hBound hReleased hPrefix hTail hLocal
    hCounts hEnds hPolls hIssued using hEach
  have hOrd : WarpOrdinals l X g pos shuffles votes :=
    ⟨fun lane hl => (hCounts lane hl).1.trans (cur.ordinals.shfl lane hl),
      fun lane hl => (hCounts lane hl).2.1.trans (cur.ordinals.vote lane hl)⟩
  exact ⟨ending,⟨⟨pos,before,state,hOrd,hTail,hLocal,hAt⟩,hPos,hBound,hReleased,hPrefix⟩,
    ⟨thread leader.val,(Step.sameWarp_lane (by rw [hp.block]) hg leader.isLt).1,
      hIssued leader.val leader.isLt rfl⟩,fun lane hl =>
        ⟨(hCounts lane hl).2.2,hEnds lane hl,hPolls lane hl⟩⟩

theorem pvWarpPacketAtFrontierWithOrdinals
    (hReady : ∀ lane < 32, PvTailReadyAtFrontier l X (warpLane l g lane) block phase extra) :
    ∃ newEnds, ∃ next : SchedulerWarpReached l X g (pvPc block 7+1)
      (fun _ => extra) shuffles votes newEnds,
      PvPacketIssues l X g block use accum ∧
      ∀ lane < 32, elections X (warpLane l g lane) (next.pos lane) =
        elections X (warpLane l g lane) (cur.pos lane) := by
  obtain ⟨ending,next,hIssued,hCount⟩ := pvWarpPacketWithPollCounts hp hMax hg block use phase
    accum hParity leader hExtra hSetup cur (fun lane hl => .inl (hReady lane hl))
  exact ⟨ending,next,hIssued,fun lane hl => (hCount lane hl).1⟩

/-- Assemble and execute one elected PV block in all lanes. The ordinary MMA issues and
mbarrier waits preserve the shuffle and ballot ordinals used by the later warp collectives. -/
theorem pvWarpPacketFromElectedWithOrdinals
    (hReady : let log := X.objects ⟨.shared,g/l.block,pvTailAddress l block⟩
      ∃ s, MBarrier.stateBefore log log.length = some s ∧ s.phase%2 ≠ phase%2) :
    ∃ newEnds, ∃ next : SchedulerWarpReached l X g (pvPc block 7+1)
      (fun _ => extra) shuffles votes newEnds,
      PvPacketIssues l X g block use accum ∧
      ∀ lane < 32, elections X (warpLane l g lane) (next.pos lane) =
        elections X (warpLane l g lane) (cur.pos lane) := by
  apply pvWarpPacketAtFrontierWithOrdinals hp hMax hg block use phase accum hParity leader
    hExtra hSetup cur
  intro lane hl t u _ _ _
  have hCta : (warpLane l g lane)/l.block = g/l.block :=
    (Step.sameWarp_lane (by rw [hp.block]) hg hl).1.1.2.2.symm
  simpa only [hCta] using hReady

/-- Assemble and execute one elected PV block in all lanes. The ordinary MMA issues and
mbarrier waits preserve the shuffle and ballot ordinals used by the later warp collectives. -/
theorem pvWarpPacketFromElected
    (hReady : let log := X.objects ⟨.shared,g/l.block,pvTailAddress l block⟩
      ∃ s, MBarrier.stateBefore log log.length = some s ∧ s.phase%2 ≠ phase%2) :
    ∃ newEnds, Nonempty (SchedulerWarpReached l X g (pvPc block 7+1)
      (fun _ => extra) shuffles votes newEnds) ∧ PvPacketIssues l X g block use accum := by
  obtain ⟨ends,after,hPacket,_⟩ := pvWarpPacketFromElectedWithOrdinals hp hMax hg block use phase
    accum hParity leader hExtra hSetup cur hReady
  exact ⟨ends,⟨after⟩,hPacket⟩

end PTX.Kernels.TmlFa4Fwd.Mma
