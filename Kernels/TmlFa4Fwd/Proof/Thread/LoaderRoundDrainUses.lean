-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderRoundUseRank
public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderRoundReusePhase
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderDrainNoReentry
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.ContinuingEvent
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

/-- At the drain entry every recurring publication of a lane lies before its cursor, so the
cursor's shuffle rank bounds the ring positions that the lane has published. -/
theorem recurringUsesBelowOfDrainCursor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch bound shuffles votes lane : Nat}
    (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hl : lane < 32) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 1744 F shuffles votes ends)
    (hRank : shuffles < primingSearchShuffleCount batch+32+32*bound) :
    Protocol.Loader.RecurringUsesBelow X (warpLane l g lane) bound := by
  intro j e he hMark
  let t := warpLane l g lane
  have hShuffles := recurringPublicationShuffleRank hp hX hFrame hg hw hl hb hLo hHi he hMark
  by_cases hj : j < cur.pos lane
  · have hMono := countP_take_mono Execution.isShfl (X.tr t) hj.le
    have hCur := cur.ordinals.shfl lane hl
    change ((X.tr t).take j).countP Execution.isShfl = _ at hShuffles
    change ((X.tr t).take (cur.pos lane)).countP Execution.isShfl = shuffles at hCur
    omega
  · exfalso
    have hIn : e ∈ (X.tr t).drop (cur.pos lane) := by
      apply List.mem_of_getElem? (i := j-cur.pos lane)
      rw [List.getElem?_drop,Nat.add_sub_of_le (by omega)]
      exact he
    have hRun := (cur.continuation lane hl).after_local_nonempty (cur.localSteps lane hl)
      (List.ne_nil_of_mem hIn)
    obtain ⟨_,hWalk⟩ := Mma.walkFromRun hRun
    have hLate := walkAfterDrain (le_of_eq (cur.checkpoint lane hl).1.symm) hWalk e hIn
    obtain ⟨site,loc,rfl⟩ := (recurringPublicationMark_iff e).mp hMark
    have hEarly : Loader.reuseArrival site < 1744 := by fin_cases site <;> decide
    exact (Nat.not_lt_of_ge hLate) hEarly

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
