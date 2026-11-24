-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyTailCommits
import all Kernels.TmlFa4Fwd.Proof.Thread.MmaTailOutputBase
import Kernels.TmlFa4Fwd.Proof.Thread.MmaDescriptorAbi
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor
import Lemmas.Flow.ReturningPrefix

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

private theorem finalOutputBaseOfMainReturned {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g visit shuffles votes : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12)
    {ends : Nat → Option TState}
    (c : SchedulerWarpReached l X g 2551 (fun _ => steadyTailValueFrame l visit)
      shuffles votes ends)
    (hMain : ∀ lane < 32, X.get (warpLane l g lane,c.pos lane-1) = some
      ⟨2548,.wait (Thread.Scores.probabilityObject l (g/l.block) 0 0) (visit%2) true true .cta⟩)
    (lane : Nat) (hl : lane < 32) :
    (c.state lane).regs 6495 = some (b32 (l.sharedBase+144)) := by
  let thread := warpLane l g lane
  have hSame := (Step.sameWarp_lane (by rw [hp.block]) hg hl).1
  obtain ⟨t,_,_,he,_,ht,hRecorded,_⟩ :=
    schedulerAbiAtDescriptorWithOrdinal hp hMax hSame.1.2.1 (hSame.2.symm.trans hw)
  have hPrior := Thread.traceOrderOfPcFloor hMax.1 (floor := 1917)
    (by set_option maxRecDepth 100000 in kernel_rfl) (by kernel_rfl) he (hMain lane hl)
    (by change 1916 < 1917; decide) (by change 1917 ≤ 2548; decide)
  change descriptorShufflePos (laneOf l thread) < c.pos lane-1 at hPrior
  let n := descriptorShufflePos (laneOf l thread)+1
  have hBound : n ≤ c.pos lane := by
    dsimp only [n]
    omega
  let pre := (X.tr thread).take (c.pos lane)
  have hSplit := List.take_append_drop n pre
  rw [show pre.take n = (X.tr thread).take n from by
    dsimp [pre]; rw [List.take_take,Nat.min_eq_left hBound]] at hSplit
  have hPrefix : Run kernel Assumptions.all l thread {} pre (some (c.before lane)) :=
    c.recorded lane hl
  rw [← hSplit] at hPrefix
  have hRest := hRecorded.after_returned_prefix hPrefix
  have hReach := hRest.returning_reach.append (TraceReach.of_local (c.localSteps lane hl))
  have hBase : t.regs 6495 = some (b32 (l.sharedBase+144)) :=
    holds_mem ht.2.2.2.2 (by simp [entryFacts,startupFacts])
  exact (outputBaseStable hReach (by rw [ht.1]; decide)
    (by rw [(c.checkpoint lane hl).1]; decide)).trans hBase

end
end PTX.Kernels.TmlFa4Fwd.Mma
