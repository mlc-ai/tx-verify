-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderDrainSelected
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderSingleVisitDrainStart
import Kernels.TmlFa4Fwd.Flow.Code.Part029

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader (terminalLoaderFrame)

private theorem prepareSelectedDrain {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g use shuffles votes : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 1862
      (fun lane => (7192,b32 0)::firstDrainTail p l (warpLane l g lane) use) shuffles votes ends) :
    Nonempty (SchedulerWarpReached l X g 1863
      (fun _ => drainCarry l use ++ (terminalLoaderFrame l (warpIndex l g) 0).tail)
      shuffles votes ends) := by
  apply cur.advanceLocal
  intro lane hl
  let t := warpLane l g lane
  let warp := warpIndex l g
  let F := drainCarry l use ++ [(7192,b32 0),(1062,b32 warp)]
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hSame : warp = warpIndex l t := (Step.sameWarp_lane hBlock hg hl).1.2
  have hWarp : warp = 14 ∨ warp = 15 := by
    have hLimit := warpIndex_lt hp g
    dsimp only [warp]
    omega
  have ht := cur.checkpoint lane hl
  have hAt : At (cur.state lane) 1862 ([(1062,b32 warp)] ++ F) := by
    have hRegs : Holds (cur.state lane).regs ((7192,b32 0)::firstDrainTail p l t use) := ht.2.2.2.2
    have hReg : (cur.state lane).regs 1062 = some (b32 warp) := by
      rw [hSame]
      exact hRegs.2.1
    have hState : Holds (cur.state lane).regs (drainCarry l use) :=
      (holds_append ..).mp hRegs.2.2 |>.1
    have hBoth : Holds (cur.state lane).regs F :=
      (holds_append _ (drainCarry l use) [(7192,b32 0),(1062,b32 warp)]).mpr
        ⟨hState,hRegs.1,hReg,trivial⟩
    exact ht.mono ⟨hReg,hBoth⟩
  have hSeg : Seg kernel [] l t 1 1862 [(1062,b32 warp)]
      1863 [(258,.pred (decide (warp ≠ 14)))] := by
    intro s hs
    rcases hWarp with h | h <;> rw [h] at hs ⊢ <;> seg_fp hs using rfl
  obtain ⟨u,hu,hU⟩ := linearFramed (by decide) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hSeg hAt
  have hRegs := hU.2.2.2.2
  have hCarry := (holds_append _ (drainCarry l use) [(7192,b32 0),(1062,b32 warp)]).mp hRegs.2
  refine ⟨u,run_rtg hu,hU.mono ?_⟩
  exact (holds_append _ (drainCarry l use) ((terminalLoaderFrame l warp 0).tail)).mpr
    ⟨hCarry.1,hRegs.1,hCarry.2⟩

/-- A loader assigned within the first group retires after its
actual scan, elections, and generation waits, once its releases are ready. -/
theorem CacheDrainNeighbors.exitOfFirstGroup {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g use : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    (c : CacheDrainNeighbors p l X g use)
    (hFirst : g/l.block < tilePrefix p (min p.batch 31)*p.heads)
    (hCache : CacheDrainReady l X g use)
    (hQuery : warpIndex l g = 14 → QueryDrainReady l X g 0) : Thread.Exited X g := by
  obtain ⟨total⟩ := c.firstGroupTotalOfMaximal hp hMax hg
  obtain ⟨selected⟩ := firstDrainGroupSelected hp hg hFirst total
  have hLow : tilePrefix p 0*p.heads ≤ g/l.block := by simp [tilePrefix]
  obtain ⟨n,hn,⟨entry⟩⟩ := drainSelectedBallotEntry hp hg hp.shape.1 hLow hFirst selected
  obtain ⟨indices⟩ := drainSelectedIndicesOfMaximal hp hMax hg hn entry
  obtain ⟨ready⟩ := prepareSelectedDrain hp hg hw indices
  exact activeLoaderExitOfDrainReached hp hMax hg hw (by decide) hCache hQuery ready

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
