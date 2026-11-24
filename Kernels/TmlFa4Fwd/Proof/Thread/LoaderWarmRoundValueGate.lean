-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmRoundKeyPublication
import Kernels.TmlFa4Fwd.Flow.Code.Part017
import Kernels.TmlFa4Fwd.Flow.Code.Part018

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader

/-- A lane-private cell keeps its value across a span of events that write nothing. -/
theorem PrimingCellValue.ofQuietSpan {X : Execution} {g a b pc : Nat} {cell : Acc}
    {data : List Byte} (h : PrimingCellValue X g a pc cell data) (hab : a ≤ b)
    (hQuiet : ∀ i, a ≤ i → i < b → ∀ d, ¬ X.Access (g,i) d true) :
    PrimingCellValue X g b pc cell data := by
  obtain ⟨w,hw,hGet,hLast⟩ := h
  refine ⟨w,by omega,hGet,fun byte hb j hj dst hA hc => ?_⟩
  by_cases hOld : j < a
  · exact hLast byte hb j hOld dst hA hc
  · exact absurd hA (hQuiet j (by omega) hj dst)

/-- The K-to-V transition words name the ring position that follows the K use. -/
theorem vTransitionWordsOfUse (use : Nat) :
    recurringVTransitionFacts 0 (kvUseStage use) (kvEmptyPhase use) =
      [(1139,b32 (kvUseStage (use+1)).val),(2064,loaderPhaseWord (kvEmptyPhase (use+1)))] := by
  have h := loaderRingWordsOfUse use
  exact congrArg (fun words : List (Nat × Value) =>
    [(1139,(words[0]?.map Prod.snd).getD (b32 0)),
     (2064,(words[1]?.map Prod.snd).getD (b32 0))]) h

set_option maxRecDepth 4096 in
/-- Warp 15 bypasses the Bias block and reaches the V gate of warm round `round` with the
stage and parity of the use after the K use. -/
theorem WarmRoundKeyPublished.valueGateSecondWarp {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) {g batch round : Nat} (hw : warpIndex l g = 15)
    (c : WarmRoundKeyPublished p l X g batch round) :
    ∃ gate : RecurringCacheGate l X g 1 (cacheUseOfRound round+1)
        (warmRoundValueCarry p l g batch round) c.shuffles c.votes c.ends,
      gate.pos = c.reached.pos := by
  obtain ⟨entry,hEntry⟩ := c.valueEntry
  let use := cacheUseOfRound round
  obtain ⟨gate,hGate⟩ := entry.advanceLocalWithPosition
    (pc' := (recurringEmptyWait 1).pc)
    (G := fun lane => recurringBarrierFacts l 1 (kvUseStage (use+1)) (cacheEmptyParity (use+1)) ++
      warmRoundValueCarry p l g batch round lane) (by
    intro lane hl
    let t := warpLane l g lane
    let F := warmRoundValueCarry p l g batch round lane
    have hs := entry.checkpoint lane hl
    have hF : Holds (entry.state lane).regs F := hs.2.2.2.2
    have hRole : (entry.state lane).regs 123 = some (.pred true) := by
      have h : (entry.state lane).regs 123 =
          some (.pred (decide (warpIndex l g ≠ 14))) := holds_mem hF (by
            simp [F,warmRoundValueCarry,warmRoundKeyCarry,warmRoundPagesFrame,warmRoundFrame,
              openingWarmFrame])
      simpa only [hw,show decide ((15 : Nat) ≠ 14) = true by decide] using h
    obtain ⟨u,hu,hU⟩ := run_bra (K := kernel) (A := []) (L := l) (g := t)
      Flow.code_1143 true hs hRole (by simp)
    have huA := (loaderLinear (regs := []) (by decide) (by decide) hs.1
      (by set_option maxRecDepth 100000 in kernel_rfl) rfl hu).1
    have hWords : Holds u.regs
        [(1139,b32 (kvUseStage (use+1)).val),(2064,loaderPhaseWord (kvEmptyPhase (use+1)))] := by
      have h : Holds u.regs (recurringVTransitionFacts 0 (kvUseStage use) (kvEmptyPhase use)) :=
        ((holds_append ..).mp hU.2.2.2.2).1
      rwa [vTransitionWordsOfUse] at h
    have ht : At u 1203
        (recurringBarrierInput l 1 (kvUseStage (use+1)) (cacheEmptyParity (use+1))++F) := by
      refine hU.mono ((holds_append ..).mpr ⟨⟨hWords.1,holds_mem hU.2.2.2.2 ?_,hWords.2.1,
        trivial⟩,hU.2.2.2.2⟩)
      simp [warmRoundValueCarry,warmRoundKeyCarry,warmRoundPagesFrame,warmRoundFrame,
        openingWarmFrame,warmStartFrame]
    obtain ⟨v,hv,hV⟩ := roundStraightFrameAll (by decide) (by decide)
      (by set_option maxRecDepth 100000 in kernel_rfl)
      (by set_option maxRecDepth 100000 in kernel_rfl)
      (recurringBarrierPrep hp (g := t) 1 (kvUseStage (use+1)) (cacheEmptyParity (use+1))) ht
    exact ⟨v,run_rtg (run_comp huA hv),hV⟩)
  exact ⟨gate,hGate.trans hEntry⟩

/-- Warp 15 passes the V poll of warm round `round` once the MMA has delivered the earlier
generations of the V slot. -/
theorem WarmRoundKeyPublished.valueAcquireSecondWarpOfMaximal {p : Params} {l : Launch}
    {m : Mem0} {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch round : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 15) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hReleased : (cacheUseOfRound round+1)/3 ≤
      Protocol.Loader.cacheEmptyUnits l X g (kvUseStage (cacheUseOfRound round+1)))
    (c : WarmRoundKeyPublished p l X g batch round) :
    ∃ done : RecurringCacheAcquired l X g 1 (cacheUseOfRound round+1)
        (warmRoundValueCarry p l g batch round) c.shuffles c.votes c.ends,
      ∀ lane < 32, (∃ index, c.reached.pos lane ≤ index ∧ index+1 = done.pos lane ∧
        EmptyAcquire l X (warpLane l g lane,index) (kvUseStage (cacheUseOfRound round+1))
          (cacheEmptyParity (cacheUseOfRound round+1))) ∧
        ∀ slot isRow, warmRoundMetadata p l X g batch round lane (done.pos lane) slot isRow := by
  obtain ⟨gate,hPos⟩ := c.valueGateSecondWarp hp hw
  have hFresh : ∀ lane < 32, (recurringEmptyWait 1).result ∉
      (warmRoundValueCarry p l g batch round lane).map Prod.fst :=
    fun _ _ => of_decide_eq_true rfl
  obtain ⟨done,hDone⟩ := gate.acquireOfReleases hp hMax hFrame hg (by omega) hb hLo hHi 1 hFresh
    (by rw [c.rank]; unfold cacheUseOfRound; omega) (by unfold cacheUseOfRound; omega) hReleased
  refine ⟨done,fun lane hl => ?_⟩
  obtain ⟨index,hLe,hIdx,hAcq⟩ := (hDone lane hl).1
  refine ⟨⟨index,congrFun hPos lane ▸ hLe,hIdx,hAcq⟩,fun slot isRow => ?_⟩
  have hCell := c.metadata lane hl slot isRow
  rw [← congrFun hPos lane] at hCell
  exact PrimingCellValue.ofQuietSpan hCell (by omega) (hDone lane hl).2

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
