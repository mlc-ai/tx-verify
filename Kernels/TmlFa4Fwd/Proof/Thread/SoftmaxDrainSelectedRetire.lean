-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxDrainIndex

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread Correction

/-- Extract a lane's terminal scheduler continuation from the reached warp. -/
theorem terminalFinishedOfReachedWarp {l : Launch} {X : Execution}
    {g shuffles votes : Nat} {warp : Fin 8} {parity : Nat → Nat}
    {ends : Nat → Option TState} (cur : SchedulerWarpReached l X g 7733
      (fun lane => terminalRetained l warp (parity lane)) shuffles votes ends)
    (lane : Nat) (hl : lane < 32) :
    TerminalSchedulerFinished l X (warpLane l g lane) warp (parity lane) :=
  TerminalSchedulerFinished.ofCursor
    ⟨cur.pos lane,cur.before lane,cur.state lane,ends lane,cur.positive lane hl,
      cur.bounded lane hl,cur.released lane hl,cur.checkpoint lane hl,cur.recorded lane hl,
      cur.continuation lane hl,cur.localSteps lane hl⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
include hp hMax

/-- A selected terminal group actually reaches the end of scheduling in every lane. -/
theorem terminalFinishedOfSelectedGroup {g first shuffles votes : Nat} (hg : g < l.threads)
    (hFirst : first < p.batch) (hLow : tilePrefix p first*p.heads ≤ g/l.block)
    (hHigh : g/l.block < tilePrefix p (min p.batch (first+31))*p.heads) (warp : Fin 8)
    (parity : Nat → Nat) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 7720
      (fun lane => let t := warpLane l g lane
        (7262,b32 (groupLaneTiles p first (laneOf l t)))::
          (terminalSelectedGroup p l t first ++ terminalRetained l warp (parity lane)))
      shuffles votes ends) :
    ∀ lane < 32, TerminalSchedulerFinished l X (warpLane l g lane) warp (parity lane) := by
  obtain ⟨n,hn,⟨ballot⟩⟩ := terminalSelectedGroupBallotEntry hp hg hFirst hLow hHigh warp parity cur
  obtain ⟨finished⟩ := terminalIndexOfMaximal hp hMax hg hn warp parity _ _ ballot
  exact terminalFinishedOfReachedWarp finished

/-- After the correction credits are released, a terminal softmax lane issues its actual
allocation-barrier arrival. -/
theorem finalAllocationArrivalOfSchedulerFinished {g parity : Nat} (hg : g < l.threads)
    (warp : Fin 8) (hParity : parity < 2) (hFinished : TerminalSchedulerFinished l X g warp parity)
    (hCredit : TerminalCreditAvailable l X g (stageOf warp) parity) :
    ∃ j, FinalAllocationArrival X (g,j) .arrive := by
  obtain ⟨poll⟩ := terminalPollOfSchedulerFinished hp warp parity hFinished
  obtain ⟨j,_,hArrival,_⟩ :=
    finalAllocationArrivalOfTerminalCredit hp hMax hg warp hParity poll hCredit
  exact ⟨j,hArrival⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
