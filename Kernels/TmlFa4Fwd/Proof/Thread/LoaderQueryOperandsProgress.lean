-- SPDX-License-Identifier: Apache-2.0
module

import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVAdmission

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderQueryExpectationProgress
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingProgress
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
import Kernels.TmlFa4Fwd.Proof.PrologueNonzeroTrace
import Kernels.TmlFa4Fwd.Proof.LoaderPipelineCut
import Lemmas.Flow.ReturningPrefix
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.Assumption Prologue Epilogue

/-- The selected Q group's ABI pointer and row/head operands live through both box elections. -/
def queryPrimingOperands (l : Launch) (row head : Nat) : List (Nat × Value) :=
  [(7291,.ptr 64 false (.param (param 9)) 0),(2535,b32 l.sharedBase),
   (1087,b32 row),(7169,b32 head)]

set_option maxRecDepth 100000 in
private theorem beyondOpeningQueriesCode :
    (kernel.code.drop 765).all (fun i => Thread.staysPastEvent 765 i.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem beyondOpeningQueriesSegments :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (765 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

set_option maxRecDepth 3000 in
private theorem beyondOpeningQueries {l : Launch} {g : Nat} {s t : TState} {events : List Event}
    (h : TraceReach kernel Assumptions.all l g s events t) (hs : 765 ≤ s.pc) : 765 ≤ t.pc := by
  induction h with
  | refl => exact hs
  | tau ht _ ih => exact ih (Thread.eventTailStepOfAudit beyondOpeningQueriesCode
      beyondOpeningQueriesSegments hs (.inl ⟨rfl,ht⟩))
  | event he _ ih => exact ih (Thread.eventTailStepOfAudit beyondOpeningQueriesCode
      beyondOpeningQueriesSegments hs (.inr ⟨_,rfl,he⟩))

set_option maxRecDepth 3000 in
private theorem frameIntoOpeningQueries {l : Launch} {g lo : Nat} {s u : TState}
    {F : List (Nat × Value)} {events : List Event}
    (hLo : 174 ≤ lo)
    (hCode : ((kernel.code.drop lo).take (765-lo)).all
      (fun i => loaderPipelineCutOp lo 765 0 (F.map Prod.fst) i.op) = true)
    (reach : TraceReach kernel Assumptions.all l g s events u)
    (hu : u.pc < 765) (hs : lo ≤ s.pc) (hShape : RingShape s) (hRegs : Holds s.regs F) :
    Holds u.regs F := by
  induction reach with
  | refl => exact hRegs
  | @tau t v u es ht hRest ih =>
    have hUpper : t.pc < 765 := by
      by_contra! h
      exact (Nat.not_le_of_lt hu) (beyondOpeningQueries (.tau ht hRest) h)
    obtain ⟨hLow,_,hNext,hKeep⟩ := pipelineCutStep (cut := 765) (branch := 0) hLo (by decide)
      ⟨hs,hUpper⟩ hCode (.inl ⟨rfl,ht⟩) hShape hRegs
    exact ih hu hLow hNext hKeep
  | @event t v u es e he hRest ih =>
    have hUpper : t.pc < 765 := by
      by_contra! h
      exact (Nat.not_le_of_lt hu) (beyondOpeningQueries (.event he hRest) h)
    obtain ⟨hLow,_,hNext,hKeep⟩ := pipelineCutStep (cut := 765) (branch := 0) hLo (by decide)
      ⟨hs,hUpper⟩ hCode (.inr ⟨_,rfl,he⟩) hShape hRegs
    exact ih hu hLow hNext hKeep

private theorem actualReachBetween {l : Launch} {X : Execution} {g i j : Nat}
    {s t u : TState} (hPos : i ≤ j)
    (hStart : Run kernel Assumptions.all l g {} ((X.tr g).take i) (some s))
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take j) (some t))
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u) :
    ∃ events, TraceReach kernel Assumptions.all l g s events u := by
  have hSplit : (X.tr g).take i ++ ((X.tr g).take j).drop i = (X.tr g).take j := by
    simpa only [List.take_take,Nat.min_eq_left hPos] using
      List.take_append_drop i ((X.tr g).take j)
  exact ⟨_,(hStart.after_returned_prefix (hSplit.symm ▸ hPrefix)).returning_reach.append
    (TraceReach.of_local hLocal)⟩

private theorem queryOperandsFromPrimingFrontier {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g batch site startCount shuffles votes : Nat} (hg : g < l.threads) (hw : warpIndex l g = 14)
    (hSite : site < 754) (hSh : 5 ≤ shuffles) (hAfter : startCount < shuffles)
    {F : Nat → List (Nat × Value)} {ends firstEnds : Nat → Option TState}
    (start : SchedulerWarpReached l X g 415 (loaderPrimingFrontierFacts p l g batch)
      startCount 1 firstEnds)
    (cur : SchedulerWarpReached l X g site F shuffles votes ends) :
    let coords := assignedCoordinates p batch (g / l.block)
    ∀ lane < 32, Holds (cur.state lane).regs
      (queryPrimingOperands l (p.qOffset batch + 256 * coords.1) coords.2) := by
  dsimp only
  intro lane hl
  let thread := warpLane l g lane
  let coords := assignedCoordinates p batch (g/l.block)
  let row := p.qOffset batch+256*coords.1
  let selector := [(1087,b32 row),(7169,b32 coords.2)]
  let abi := [(7291,.ptr 64 false (.param (param 9)) 0),(2535,b32 l.sharedBase)]
  have hStart := start.checkpoint lane hl
  have hEnd := cur.checkpoint lane hl
  have hPos : start.pos lane ≤ cur.pos lane := by
    by_contra! hBad
    have hMon := countP_take_mono Execution.isShfl (X.tr thread) hBad.le
    rw [cur.ordinals.shfl lane hl,start.ordinals.shfl lane hl] at hMon
    omega
  have hSizes := cur.bounded lane hl
  have hNonempty : start.pos lane < cur.pos lane := by
    by_contra! h
    have hEq := Nat.le_antisymm hPos h
    have hCount := start.ordinals.shfl lane hl
    rw [hEq,cur.ordinals.shfl lane hl] at hCount
    omega
  have hSplit : (X.tr thread).take (start.pos lane) ++
      ((X.tr thread).take (cur.pos lane)).drop (start.pos lane) =
      (X.tr thread).take (cur.pos lane) := by
    simpa only [List.take_take,Nat.min_eq_left hPos] using
      List.take_append_drop (start.pos lane) ((X.tr thread).take (cur.pos lane))
  have hMid := (start.recorded lane hl).after_returned_prefix
    (hSplit.symm ▸ cur.recorded lane hl)
  have hNotNil : ((X.tr thread).take (cur.pos lane)).drop (start.pos lane) ≠ [] := by
    rw [ne_eq,List.drop_eq_nil_iff,List.length_take,Nat.min_eq_left hSizes]
    omega
  have hTail := hMid.after_local_nonempty (start.localSteps lane hl) hNotNil
  have hSelTrace := hTail.returning_reach.append (TraceReach.of_local (cur.localSteps lane hl))
  have hSelector : Holds (start.state lane).regs selector := by
    have hFields := hStart.2.2.2.2
    refine ⟨holds_mem hFields ?_,holds_mem hFields ?_,trivial⟩
    · simp [loaderPrimingFrontierFacts,primingKAddressFacts,primingKAddressCarry,row,coords]
    · simp [loaderPrimingFrontierFacts,primingKAddressFacts,addressPreludeInputs,coords]
  have hKept := frameIntoOpeningQueries (lo := 415) (F := selector) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl) hSelTrace (by rw [hEnd.1]; omega)
    (by rw [hStart.1]) (ringShapeOfAt hStart) hSelector
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hSame := (Step.sameWarp_lane hBlock hg hl).1
  have hWarp : 0 < warpIndex l thread := by
    have h := hSame.2
    change warpIndex l g = warpIndex l thread at h
    omega
  have hOld : 5 ≤ cur.pos lane := by
    have hCount := cur.ordinals.shfl lane hl
    have hn := List.countP_le_length (p := Execution.isShfl)
      (l := (X.tr thread).take (cur.pos lane))
    rw [hCount,List.length_take] at hn
    omega
  obtain ⟨base,_,hBase,_,hPast,_⟩ := nonzeroCommonPrefix hp hX hSame.1.2.1
    hWarp (hOld.trans hSizes)
  obtain ⟨_,hAbiTrace⟩ := actualReachBetween hOld hPast
    (cur.recorded lane hl) (cur.localSteps lane hl)
  have hAbi : Holds base.regs abi := by
    have hFields := hBase.2.2.2.2
    refine ⟨holds_mem hFields ?_,hFields.2.1,trivial⟩
    simp [nonzeroBarrierFacts,abiFacts]
  have hKeptAbi := frameIntoOpeningQueries (lo := 174) (F := abi) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl) hAbiTrace (by rw [hEnd.1]; omega)
    (by rw [hBase.1]) (ringShapeOfAt hBase) hAbi
  exact (holds_append ..).mpr ⟨hKeptAbi,hKept⟩

/-- The opening Bias boxes read the selected row, head, and zero priming residual. -/
def openingBiasOperands (l : Launch) (row head : Nat) : List (Nat × Value) :=
  [(7289,.ptr 64 false (.param (param 11)) 0),(2535,b32 l.sharedBase),
   (1087,b32 row),(7169,b32 head),(1090,b32 0)]

private theorem biasOperandsFromPrimingFrontier {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g batch site startCount shuffles votes : Nat} (hg : g < l.threads) (hw : warpIndex l g = 14)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hSite : site < 765) (hSh : 5 ≤ shuffles) (hAfter : startCount < shuffles)
    {F : Nat → List (Nat × Value)} {ends firstEnds : Nat → Option TState}
    (start : SchedulerWarpReached l X g 415 (loaderPrimingFrontierFacts p l g batch)
      startCount 1 firstEnds)
    (cur : SchedulerWarpReached l X g site F shuffles votes ends) :
    let coords := assignedCoordinates p batch (g / l.block)
    ∀ lane < 32, Holds (cur.state lane).regs
      (openingBiasOperands l (p.qOffset batch + 256 * coords.1) coords.2) := by
  dsimp only
  intro lane hl
  let thread := warpLane l g lane
  let coords := assignedCoordinates p batch (g/l.block)
  let row := p.qOffset batch+256*coords.1
  let selector := [(1087,b32 row),(7169,b32 coords.2)]
  let abi := [(7289,.ptr 64 false (.param (param 11)) 0),(2535,b32 l.sharedBase)]
  have hStart := start.checkpoint lane hl
  have hEnd := cur.checkpoint lane hl
  have hPos : start.pos lane ≤ cur.pos lane := by
    by_contra! hBad
    have hMon := countP_take_mono Execution.isShfl (X.tr thread) hBad.le
    rw [cur.ordinals.shfl lane hl,start.ordinals.shfl lane hl] at hMon
    omega
  have hSizes := cur.bounded lane hl
  have hNonempty : start.pos lane < cur.pos lane := by
    by_contra! h
    have hEq := Nat.le_antisymm hPos h
    have hCount := start.ordinals.shfl lane hl
    rw [hEq,cur.ordinals.shfl lane hl] at hCount
    omega
  have hSplit : (X.tr thread).take (start.pos lane) ++
      ((X.tr thread).take (cur.pos lane)).drop (start.pos lane) =
      (X.tr thread).take (cur.pos lane) := by
    simpa only [List.take_take,Nat.min_eq_left hPos] using
      List.take_append_drop (start.pos lane) ((X.tr thread).take (cur.pos lane))
  have hMid := (start.recorded lane hl).after_returned_prefix
    (hSplit.symm ▸ cur.recorded lane hl)
  have hNotNil : ((X.tr thread).take (cur.pos lane)).drop (start.pos lane) ≠ [] := by
    rw [ne_eq,List.drop_eq_nil_iff,List.length_take,Nat.min_eq_left hSizes]
    omega
  have hTail := hMid.after_local_nonempty (start.localSteps lane hl) hNotNil
  have hSelTrace := hTail.returning_reach.append (TraceReach.of_local (cur.localSteps lane hl))
  have hBound := assignedCoordinates_valid hp hLo hHi
  have hStartAt : At (start.state lane) 415
      (primingKAddressFacts p l batch coords.2 coords.1 (warpIndex l g) lane) :=
    hStart.mono ((holds_append ..).mp hStart.2.2.2.2).1
  obtain ⟨_,scratch,hScratch,hAtScratch⟩ := primingVAdmissionWithTripsLane hp hb
    (hBound.2.trans hp.heads_signed) hBound.1 hl (g := thread) hStartAt
  have hScratchRun := hTail.after_local_nonempty hScratch hNotNil
  have hScratchReach := hScratchRun.returning_reach.append
    (TraceReach.of_local (cur.localSteps lane hl))
  have hResidual : Holds scratch.regs [(1090,b32 0)] := by
    refine ⟨holds_mem hAtScratch.2.2.2.2 ?_,trivial⟩
    simp [primingVTripFrame]
  have hResidualKept := frameIntoOpeningQueries (lo := 488) (F := [(1090,b32 0)])
    (by decide) (by set_option maxRecDepth 100000 in kernel_rfl) hScratchReach
    (by rw [hEnd.1]; exact hSite) (by rw [hAtScratch.1]) (ringShapeOfAt hAtScratch) hResidual
  have hSelector : Holds (start.state lane).regs selector := by
    have hFields := hStart.2.2.2.2
    refine ⟨holds_mem hFields ?_,holds_mem hFields ?_,trivial⟩
    · simp [loaderPrimingFrontierFacts,primingKAddressFacts,primingKAddressCarry,row,coords]
    · simp [loaderPrimingFrontierFacts,primingKAddressFacts,addressPreludeInputs,coords]
  have hKept := frameIntoOpeningQueries (lo := 415) (F := selector) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl) hSelTrace (by rw [hEnd.1]; exact hSite)
    (by rw [hStart.1]) (ringShapeOfAt hStart) hSelector
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hSame := (Step.sameWarp_lane hBlock hg hl).1
  have hWarp : 0 < warpIndex l thread := by
    have h := hSame.2
    change warpIndex l g = warpIndex l thread at h
    omega
  have hOld : 5 ≤ cur.pos lane := by
    have hCount := cur.ordinals.shfl lane hl
    have hn := List.countP_le_length (p := Execution.isShfl)
      (l := (X.tr thread).take (cur.pos lane))
    rw [hCount,List.length_take] at hn
    omega
  obtain ⟨base,_,hBase,_,hPast,_⟩ := nonzeroCommonPrefix hp hX hSame.1.2.1
    hWarp (hOld.trans hSizes)
  obtain ⟨_,hAbiTrace⟩ := actualReachBetween hOld hPast
    (cur.recorded lane hl) (cur.localSteps lane hl)
  have hAbi : Holds base.regs abi := by
    have hFields := hBase.2.2.2.2
    refine ⟨holds_mem hFields ?_,hFields.2.1,trivial⟩
    simp [nonzeroBarrierFacts,abiFacts]
  have hKeptAbi := frameIntoOpeningQueries (lo := 174) (F := abi) (by decide)
    (by set_option maxRecDepth 100000 in kernel_rfl) hAbiTrace (by rw [hEnd.1]; exact hSite)
    (by rw [hBase.1]) (ringShapeOfAt hBase) hAbi
  exact (holds_append ..).mpr ⟨hKeptAbi,(holds_append ..).mpr ⟨hKept,hResidualKept⟩⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc) {g batch site shuffles votes : Nat}
    (hg : g < l.threads) (hw : warpIndex l g = 14) (hBatch : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
include hp hMax writes hg hw hBatch hLo hHi

/-- The opening Bias packet uses its ABI descriptor and exact selected row, head and residual. -/
theorem selectedOpeningBiasOperandsOfMaximal (hSite : site < 765)
    (hSh : 10 + 7 * (batch / 31) + (if 31 * (batch / 31) < batch then 1 else 0) + 1 < shuffles)
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g site F shuffles votes ends) :
    let coords := assignedCoordinates p batch (g / l.block)
    ∀ lane < 32, Holds (cur.state lane).regs
      (openingBiasOperands l (p.qOffset batch + 256 * coords.1) coords.2) := by
  obtain ⟨_,⟨start⟩⟩ := selectedPrimingAddressesOfMaximal hp hMax writes hg (by omega)
    hBatch hLo hHi
  exact biasOperandsFromPrimingFrontier hp hMax.1 hg hw hBatch hLo hHi hSite
    (by omega) hSh start cur

/-- Either opening query keeps the selected request operands through its box elections. -/
theorem selectedOpeningQueryOperandsOfMaximal (hSite : site < 754)
    (hSh : 10 + 7 * (batch / 31) + (if 31 * (batch / 31) < batch then 1 else 0) + 1 < shuffles)
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g site F shuffles votes ends) :
    let coords := assignedCoordinates p batch (g / l.block)
    ∀ lane < 32, Holds (cur.state lane).regs
      (queryPrimingOperands l (p.qOffset batch + 256 * coords.1) coords.2) := by
  obtain ⟨_,⟨start⟩⟩ := selectedPrimingAddressesOfMaximal hp hMax writes hg (by omega)
    hBatch hLo hHi
  exact queryOperandsFromPrimingFrontier hp hMax.1 hg hw hSite (by omega) hSh start cur

/-- The first Q box election uses the exact selected request, including later groups. -/
theorem selectedQueryBoxOperandsOfMaximal (hSite : site < 701)
    (hSh : 10 + 7 * (batch / 31) + (if 31 * (batch / 31) < batch then 1 else 0) + 1 < shuffles)
    {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g site F shuffles votes ends) :
    let coords := assignedCoordinates p batch (g / l.block)
    ∀ lane < 32, Holds (cur.state lane).regs
      (queryPrimingOperands l (p.qOffset batch + 256 * coords.1) coords.2) := by
  exact selectedOpeningQueryOperandsOfMaximal hp hMax writes hg hw hBatch hLo hHi
    (by omega) hSh cur

end PTX.Kernels.TmlFa4Fwd.Loader
