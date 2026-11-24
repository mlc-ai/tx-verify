-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderValuePacketProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderOpeningValueMasks
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderKeyPublicationProgress
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderOpeningBiasGuard
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Lemmas.Flow.RecordedCheckpointPath

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow PTX.Assumption Prologue Epilogue

set_option maxRecDepth 15000 in
private theorem afterValueCommitCode :
    (kernel.code.drop 903).all (fun i => Thread.staysPastEvent 903 i.op) = true := by kernel_rfl

private theorem afterValueCommitSegments :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (903 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

set_option maxRecDepth 15000 in
private theorem afterValueCommitNextCode :
    (kernel.code.drop 904).all (fun i => Thread.staysPastEvent 904 i.op) = true := by kernel_rfl

private theorem afterValueCommitNextSegments :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (904 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem valueCommitBaseCode :
    ((kernel.code.drop 785).take (904-785)).all
      (fun ins => loaderPipelineCutOp 785 904 904 [2535] ins.op) = true := by kernel_rfl

private theorem valueCommitBase {l : Launch} {g : Nat} {s u : TState} {events : List Event}
    (h : TraceReach kernel Assumptions.all l g s events u)
    (hLo : 785 ≤ s.pc) (hEnd : u.pc = 903) (hShape : RingShape s)
    (hRegs : Holds s.regs [(2535,b32 l.sharedBase)]) :
    Holds u.regs [(2535,b32 l.sharedBase)] := by
  have below {v : TState} {es : List Event}
      (hr : TraceReach kernel Assumptions.all l g v es u) : v.pc < 904 := by
    by_contra! hHigh
    have := Thread.Loader.traceRetainsFloor afterValueCommitNextCode
      afterValueCommitNextSegments hr hHigh
    omega
  induction h with
  | refl => exact hRegs
  | tau ht hTail ih =>
    obtain ⟨hLow,_,hRing,hKeep⟩ := pipelineCutStep (F := [(2535,b32 l.sharedBase)])
      (lower := 785) (cut := 904) (branch := 904) (by decide) (by decide)
      ⟨hLo,below (.tau ht hTail)⟩ valueCommitBaseCode (.inl ⟨rfl,ht⟩) hShape hRegs
    exact ih hLow hEnd hRing hKeep below
  | event he hTail ih =>
    obtain ⟨hLow,_,hRing,hKeep⟩ := pipelineCutStep (F := [(2535,b32 l.sharedBase)])
      (lower := 785) (cut := 904) (branch := 904) (by decide) (by decide)
      ⟨hLo,below (.event he hTail)⟩ valueCommitBaseCode (.inr ⟨_,rfl,he⟩) hShape hRegs
    exact ih hLow hEnd hRing hKeep below

/-- All lanes at the complete opening V packet issue the real commit and ready arrive-on. -/
theorem openingValuePublishOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch tile warp shuffles votes startShuffles startVotes : Nat} (hg : g < l.threads)
    {bases residual : Nat → Nat} {endsStart ends : Nat → Option TState}
    (opening : OpeningValueAcquired l X g startShuffles startVotes endsStart)
    (cur : OpeningValueCommitReached p l X g batch tile warp shuffles votes bases residual ends) :
    ∀ lane < 32, Thread.Loader.PrimingPublication l X (warpLane l g lane,cur.pos lane+1) 1 := by
  intro lane hl
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hThread := (Step.sameWarp_lane hBlock hg hl).1.1.2.1
  have hStart := opening.checkpoint lane hl
  have hEnd := cur.checkpoint lane hl
  have hNoBack es : ¬ TraceReach kernel Assumptions.all l (warpLane l g lane) (cur.state lane)
      es (opening.state lane) := by
    intro hr
    have h := Thread.Loader.traceRetainsFloor afterValueCommitCode afterValueCommitSegments
      hr (Nat.le_of_eq hEnd.1.symm)
    rw [hStart.1] at h
    omega
  obtain ⟨_,hr⟩ := recordedCheckpointsPath (opening.bounded lane hl) (cur.bounded lane hl)
    (opening.recorded lane hl) (opening.localSteps lane hl) (cur.recorded lane hl)
    (cur.localSteps lane hl) hNoBack
  have hRegs : Holds (opening.state lane).regs [(2535,b32 l.sharedBase)] := by
    exact ⟨((holds_append ..).mp hStart.2.2.2.2).2.1,trivial⟩
  have hBase := valueCommitBase hr hStart.1.ge hEnd.1 (ringShapeOfAt hStart) hRegs
  have hAt : At (cur.state lane) (copyCommitPc 1)
      [((copyArrivalAddress 1).1,b32 l.sharedBase)] := hEnd.mono hBase
  have hWidth : l.sharedBase+(copyArrivalAddress 1).2 < 2^32 := by
    have := hp.shared.2.1
    change l.sharedBase+40 < 2^32
    omega
  have hAlign : l.sharedBase%8 = 0 := by have := hp.shared.1; omega
  exact (copyCommitAndArriveOfMaximal hMax hThread 1 hAt hWidth hAlign
    (cur.localSteps lane hl) (cur.recorded lane hl) (cur.continuation lane hl)
    (cur.positive lane hl) (cur.bounded lane hl) (cur.released lane hl)).2.1

end PTX.Kernels.TmlFa4Fwd.Loader
