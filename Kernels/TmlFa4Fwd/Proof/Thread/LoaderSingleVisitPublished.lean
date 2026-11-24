-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSingleVisitDrainStart
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderValuePacketProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.PrimingLoaderPublication
import all Kernels.TmlFa4Fwd.Proof.LoaderFirstTiles
import all Kernels.TmlFa4Fwd.Proof.LoaderBiasTailGuard
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderDrainWords
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSchedulerProgress
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderKeyPublicationProgress
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderOpeningBiasGuard
import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVAdmission
import Lemmas.Flow.RecordedCheckpointPath
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof PTX.Assumption Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader
  (loaderCuQFacts loaderEntryFacts loaderBarrierFacts loaderDownTemplate loaderLinear
    loaderPrimingFrontierFacts loaderPipelineCutOp pipelineCutStep ringShapeOfAt RingShape
    OpeningValueCommitReached vPrimingResidual primingVAdmissionWithTripsLane
    primingVAdmissionCarry primingVTripFrame)

private def schedulerRootFrame (p : Params) (l : Launch) (g : Nat) : List (Nat × Value) :=
  [(1062,b32 (warpIndex l g)),(2535,b32 l.sharedBase)] ++ drainSchedulerFrame p l g

private theorem schedulerRootsOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hCuQ : DrainCuQProtected p X) :
    ∃ ends, Nonempty (SchedulerWarpReached l X g 194
      (fun lane => schedulerRootFrame p l (warpLane l g lane)) 4 0 ends) := by
  obtain ⟨ends,⟨head⟩⟩ := Loader.firstShuffleOfMaximal hp hMax hg hw hCuQ
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hLane (lane : Nat) (hl : lane < 32) : laneOf l (warpLane l g lane) = lane :=
    (Step.sameWarp_lane hBlock hg hl).2
  obtain ⟨down⟩ := head.consumeShuffle (dst := 1707) hp hMax hg .down
    (fun lane => b32 (drainCuQ p lane)) (fun _ => 1) (fun _ => 31)
    (fun lane _ _ hm heq => by
      have hMem := List.mem_map_of_mem (f := Prod.fst) hm
      rw [heq] at hMem
      exact (of_decide_eq_true rfl : 1707 ∉
        (loaderCuQFacts p l (warpLane l g lane) (warpIndex l g)).map Prod.fst) hMem)
    (fun lane hl => by
      simpa only [hLane lane hl] using loaderDownTemplate hp (head.checkpoint lane hl))
  refine ⟨ends,down.advanceLocal ?_⟩
  intro lane hl
  let g' := warpLane l g lane
  let F := loaderCuQFacts p l g' (warpIndex l g)
  let a := drainCuQ p lane
  let b := drainCuQ p (shflSource .down lane 1 31).1
  have hAt := down.checkpoint lane hl
  obtain ⟨ha,hb,_,_,_⟩ := drainWordTiles hp 0 lane
  simp only [Nat.zero_add] at ha hb
  have hInputs : At (down.state lane) 188
      [(1073,b32 lane),(7170,b32 p.batch),(7159,b32 a),(1707,b32 b)] := by
    apply hAt.mono
    have hRegs := hAt.2.2.2.2
    refine ⟨?_,?_,?_,hRegs.1,trivial⟩
    · simpa only [hLane lane hl] using hRegs.2.2.1
    · exact hRegs.2.2.2.1
    · simpa only [hLane lane hl] using hRegs.2.1
  obtain ⟨u,hu,hU⟩ := Loader.loaderFirstTileGate l g' hl hp.shape.2.1 ha hb _ hInputs
  obtain ⟨hLocal,hKeep⟩ := loaderLinear (regs := F.map Prod.fst)
    (by decide) (by decide) hInputs.1
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hu
  have hSave : Holds u.regs F := holdsSchedulerFrame hAt.2.2.2.2.2 hKeep
    (fun _ hm => List.mem_map_of_mem hm)
  have hWarp : warpIndex l g = warpIndex l g' := (Step.sameWarp_lane hBlock hg hl).1.2
  refine ⟨u,run_rtg hLocal,hU.mono ⟨?_,?_,?_,?_,?_,?_,trivial⟩⟩
  · rw [← hWarp]
    exact holds_mem hSave (by simp [F,loaderCuQFacts,loaderEntryFacts,loaderBarrierFacts])
  · exact holds_mem hSave (by simp [F,loaderCuQFacts,loaderEntryFacts,loaderBarrierFacts])
  · exact hSave.2.1
  · exact holds_mem hSave (by
      simp [F,loaderCuQFacts,loaderEntryFacts,loaderBarrierFacts,abiFacts])
  · exact hSave.2.2.2.1
  · change u.regs 64 = some (.pred (!decide (laneHasRequest (laneOf l g') p.batch)))
    rw [hLane lane hl]
    exact hU.2.2.2.2.2.2.2.1

private def auditedFloor (floor : Nat) : Prop :=
  (kernel.code.drop floor).all (fun i => Thread.staysPastEvent floor i.op) = true ∧
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (floor ≤ seg.stop)
      | none => false) = true

private theorem floor903 : auditedFloor 903 := by
  constructor <;> set_option maxRecDepth 100000 in kernel_rfl

private theorem floor904 : auditedFloor 904 := by
  constructor <;> set_option maxRecDepth 100000 in kernel_rfl

private theorem boundOnPath {l : Launch} {g floor : Nat} {s t : TState} {events : List Event}
    (hf : auditedFloor floor) (hEnd : t.pc < floor)
    (hr : TraceReach kernel Assumptions.all l g s events t) : s.pc < floor := by
  by_contra! hs
  exact Nat.not_le_of_gt hEnd (traceRetainsFloor hf.1 hf.2 hr hs)

private theorem retainLoaderFrame {l : Launch} {g lower cut : Nat} {s t : TState}
    {events : List Event} {F : List (Nat × Value)}
    (hLower : 174 ≤ lower) (hUpper : cut ≤ 1901)
    (hAudit : ((kernel.code.drop lower).take (cut-lower)).all
      (fun ins => loaderPipelineCutOp lower cut cut (F.map Prod.fst) ins.op) = true)
    (hFloor : auditedFloor cut) (hEnd : t.pc < cut)
    (hPath : TraceReach kernel Assumptions.all l g s events t)
    (hStart : lower ≤ s.pc) (hShape : RingShape s) (hRegs : Holds s.regs F) :
    Holds t.regs F := by
  induction hPath with
  | refl => exact hRegs
  | tau ht hTail ih =>
    have hBound := boundOnPath hFloor hEnd (.tau ht hTail)
    obtain ⟨hLo,_,hShape,hF⟩ :=
      pipelineCutStep hLower hUpper ⟨hStart,hBound⟩ hAudit (.inl ⟨rfl,ht⟩) hShape hRegs
    exact ih hEnd hLo hShape hF
  | event he hRest ih =>
    have hBound := boundOnPath hFloor hEnd (.event he hRest)
    obtain ⟨hLo,_,hShape,hF⟩ :=
      pipelineCutStep hLower hUpper ⟨hStart,hBound⟩ hAudit (.inr ⟨_,rfl,he⟩) hShape hRegs
    exact ih hEnd hLo hShape hF

private theorem preserveStartupAtCommit {p : Params} {l : Launch} {X : Execution}
    {g startShuffles startVotes shuffles votes : Nat} {F : Nat → List (Nat × Value)}
    {endsStart ends : Nat → Option TState}
    (first : SchedulerWarpReached l X g 194
      (fun lane => schedulerRootFrame p l (warpLane l g lane)) startShuffles startVotes endsStart)
    (commit : SchedulerWarpReached l X g 903 F shuffles votes ends)
    (lane : Nat) (hl : lane < 32) :
    Holds (commit.state lane).regs (schedulerRootFrame p l (warpLane l g lane)) := by
  have hAt := commit.checkpoint lane hl
  have hOld := first.checkpoint lane hl
  obtain ⟨_,hr⟩ := recordedCheckpointsPath (first.bounded lane hl) (commit.bounded lane hl)
    (first.recorded lane hl) (first.localSteps lane hl) (commit.recorded lane hl)
    (commit.localSteps lane hl) (fun _ hBack =>
      Nat.not_lt_of_ge hAt.1.ge (boundOnPath floor903 (by rw [hOld.1]; decide) hBack))
  have hKeep : ((kernel.code.drop 194).take (904-194)).all
      (fun ins => loaderPipelineCutOp 194 904 904
        ((schedulerRootFrame p l (warpLane l g lane)).map Prod.fst) ins.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  exact retainLoaderFrame (by decide) (by decide) hKeep floor904 (by rw [hAt.1]; decide)
    hr hOld.1.ge (ringShapeOfAt hOld) hOld.2.2.2.2

private theorem traceStartClean {l : Launch} {g : Nat} {t u : TState} {events : List Event}
    (hr : TraceReach kernel Assumptions.all l g t events u) (hClean : u.fault = none) :
    t.fault = none := by
  cases hr with
  | refl => exact hClean
  | tau ht _ =>
    cases hFault : t.fault with
    | none => rfl
    | some fault => simp [Tau,out,hFault] at ht
  | event ht _ =>
    cases hFault : t.fault with
    | none => rfl
    | some fault =>
      obtain ⟨_,hOut,hFire⟩ := ht
      simp only [out,hFault,Out.ev.injEq] at hOut
      subst_vars
      cases hFire.2

private theorem tripInputsAtCommit {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {g batch seedShuffles seedVotes shuffles votes : Nat}
    {F : Nat → List (Nat × Value)} {endsSeed ends : Nat → Option TState}
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (seed : SchedulerWarpReached l X g 415 (loaderPrimingFrontierFacts p l g batch)
      seedShuffles seedVotes endsSeed)
    (commit : SchedulerWarpReached l X g 903 F shuffles votes ends) (lane : Nat) (hl : lane < 32) :
    let co := assignedCoordinates p batch (g/l.block)
    let n := Mma.trips p batch co.1
    let residual := vPrimingResidual p batch co.1
    Holds (commit.state lane).regs
      [(1088,b32 n),(1091,b32 (n-1)),(164,.pred (Loader.residueFlag residual))] := by
  dsimp only
  let co := assignedCoordinates p batch (g/l.block)
  let n := Mma.trips p batch co.1
  let residual := vPrimingResidual p batch co.1
  let thread := warpLane l g lane
  have ⟨hTile,hHead⟩ := assignedCoordinates_valid hp hLo hHi
  have hSeed := seed.checkpoint lane hl
  have hStart : At (seed.state lane) 415
      (Loader.primingKAddressFacts p l batch co.2 co.1 (warpIndex l g) lane) :=
    hSeed.mono ((holds_append ..).mp hSeed.2.2.2.2).1
  obtain ⟨s,hLocal,hs⟩ := (primingVAdmissionWithTripsLane hp hb (hHead.trans hp.heads_signed)
    hTile (g := thread) hl hStart).2
  have hs' : At s 488 [(1088,b32 n),(1091,b32 (n-1)),(1089,b32 residual)] := by
    apply hs.mono
    repeat' apply And.intro
    all_goals first | trivial |
      (apply holds_mem hs.2.2.2.2; simp [co,n,residual,primingVAdmissionCarry,primingVTripFrame])
  have hAt := commit.checkpoint lane hl
  obtain ⟨_,hPath⟩ := recordedCheckpointsPath (seed.bounded lane hl) (commit.bounded lane hl)
    (seed.recorded lane hl) (seed.localSteps lane hl) (commit.recorded lane hl)
    (commit.localSteps lane hl) (fun _ hBack =>
      Nat.not_lt_of_ge hAt.1.ge (boundOnPath floor903 (by rw [hSeed.1]; decide) hBack))
  have hReach := hPath.afterLocalOfNoBack hLocal (fun hBack =>
    Nat.not_lt_of_ge hAt.1.ge
      (boundOnPath floor903 (by rw [hs'.1]; decide) (TraceReach.of_local hBack)))
  have hFinish : (commit.state lane).pc < 904 := by rw [hAt.1]; decide
  have hBefore : Holds (commit.state lane).regs
      [(1088,b32 n),(1091,b32 (n-1)),(1089,b32 residual)] :=
    retainLoaderFrame (lower := 488) (by decide) (by decide)
      (by set_option maxRecDepth 100000 in kernel_rfl) floor904 hFinish hReach hs'.1.ge
      (ringShapeOfAt hs') hs'.2.2.2.2
  have hBound : 803 ≤ (commit.state lane).pc ∧ (commit.state lane).pc ≤ 903 := by
    rw [hAt.1]
    decide
  have hProjected : At s 488 [(1089,b32 residual)] := hs'.mono ⟨hs'.2.2.2.2.2.2.1,trivial⟩
  obtain ⟨v,_,_,_,hPc,hSub,hAcc,hRegs,_,hSuffix⟩ :=
    Thread.Loader.loaderCutOfObservedPath hReach (low := 488) (cut := 803) (bypass := 903)
      (by decide) (by decide) (by set_option maxRecDepth 100000 in kernel_rfl)
      (fun hPath hAfter => by
        have hFloor := traceRetainsFloor floor904.1 floor904.2 hPath (by omega)
        omega)
      (by rw [hs'.1]; decide) (ringShapeOfAt hProjected) (fun _ => hs'.2.1)
      hProjected.2.2.2.2 hBound
  have hFlagStart : At v 803 [(1089,b32 residual)] :=
    ⟨hPc,hSub,hAcc,traceStartClean hSuffix hAt.2.2.2.1,hRegs⟩
  have hRes : residual < 2^32 := Nat.mod_lt _ (by decide)
  obtain ⟨u,hu,hU⟩ := (Loader.residualFlagCore l thread residual hRes).apply hFlagStart
  have hRun := (loaderLinear (regs := []) (by decide) (by decide) hFlagStart.1
    (by simp) (by decide) hu).1
  have hAfter := hSuffix.afterLocalOfNoBack (run_rtg hRun) (fun hBack =>
    Nat.not_lt_of_ge hAt.1.ge
      (boundOnPath floor903 (by rw [hU.1]; decide) (TraceReach.of_local hBack)))
  have hFlag : Holds (commit.state lane).regs [(164,.pred (Loader.residueFlag residual))] :=
    retainLoaderFrame (lower := 804) (by decide) (by decide)
      (by set_option maxRecDepth 100000 in kernel_rfl) floor904 hFinish hAfter hU.1.ge
      (ringShapeOfAt hU) hU.2.2.2.2
  exact ⟨hBefore.1,hBefore.2.1,hFlag.1,trivial⟩

/-- The actual opening V commit and publication retain the scheduler roots and
selected single-visit trip count, and return each lane at the drain branch. -/
theorem singleVisitAfterValuePublication {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch shuffles votes seedShuffles seedVotes : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hCuQ : DrainCuQProtected p X)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hSingle : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1)
    {endsSeed ends : Nat → Option TState}
    (seed : SchedulerWarpReached l X g 415 (loaderPrimingFrontierFacts p l g batch)
      seedShuffles seedVotes endsSeed)
    {F : Nat → List (Nat × Value)} (commit : SchedulerWarpReached l X g 903 F shuffles votes ends) :
    let frame := fun (rest : Bool) lane => let t := warpLane l g lane
      [(1088,b32 1),(1091,b32 0),(164,.pred rest),(1062,b32 (warpIndex l t)),
        (2535,b32 l.sharedBase)] ++ drainSchedulerFrame p l t
    ∃ rest : Bool, ∃ after : SchedulerWarpReached l X g 905 (frame rest) shuffles votes ends,
      ∀ lane < 32, after.pos lane = commit.pos lane+2 ∧
        Thread.Loader.PrimingPublication l X (warpLane l g lane,commit.pos lane+1) 1 := by
  dsimp only
  let co := assignedCoordinates p batch (g/l.block)
  let rest := Loader.residueFlag (vPrimingResidual p batch co.1)
  let thread := warpLane l g
  let frame (lane : Nat) := [(1088,b32 1),(1091,b32 0),(164,.pred rest)] ++
    schedulerRootFrame p l (thread lane)
  let post (lane : Nat) := next (next (commit.state lane))
  obtain ⟨_,⟨first⟩⟩ := schedulerRootsOfMaximal hp hMax hg hw hCuQ
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hLane (lane : Nat) (hl : lane < 32) :
      X.get (thread lane,commit.pos lane) = some ⟨903,.asyncCommit⟩ ∧
      Thread.Loader.PrimingPublication l X (thread lane,commit.pos lane+1) 1 ∧
      At (post lane) 905 (frame lane) ∧
      Run kernel Assumptions.all l (thread lane) {}
        ((X.tr (thread lane)).take (commit.pos lane+2)) (some (post lane)) ∧
      Run kernel Assumptions.all l (thread lane) (post lane)
        ((X.tr (thread lane)).drop (commit.pos lane+2)) (ends lane) := by
    have hs := commit.checkpoint lane hl
    have hf := preserveStartupAtCommit first commit lane hl
    have hInputs := tripInputsAtCommit hp hb hLo hHi seed commit lane hl
    dsimp only at hInputs
    rw [hSingle] at hInputs
    have hAt : At (commit.state lane) 903 (frame lane) :=
      hs.mono ((holds_append ..).mpr ⟨hInputs,hf⟩)
    have hBase := hf.2.1
    have hC : At (commit.state lane) (Loader.copyCommitPc 1)
        [((Loader.copyArrivalAddress 1).1,b32 l.sharedBase)] := hs.mono ⟨hBase,trivial⟩
    have hWidth : l.sharedBase+(Loader.copyArrivalAddress 1).2 < 2^32 := by
      have := hp.shared.2.1
      change l.sharedBase+40 < 2^32
      omega
    have hAlign : l.sharedBase%8 = 0 := by have := hp.shared.1; omega
    obtain ⟨he,hPub,hPre,hRest⟩ := Loader.copyCommitAndArriveOfMaximal hMax
      (Step.sameWarp_lane hBlock hg hl).1.1.2.1 1 hC hWidth hAlign
      (commit.localSteps lane hl) (commit.recorded lane hl) (commit.continuation lane hl)
      (commit.positive lane hl) (commit.bounded lane hl) (commit.released lane hl)
    exact ⟨he,hPub,hAt.next.next,hPre,hRest⟩
  have hCounts (pred : Event → Bool)
      (hCommit : pred ⟨903,.asyncCommit⟩ = false)
      (hArrival : ∀ loc, pred ⟨904,.asyncArrive loc true⟩ = false)
      (lane : Nat) (hl : lane < 32) :
      ((X.tr (thread lane)).take (commit.pos lane+2)).countP pred =
        ((X.tr (thread lane)).take (commit.pos lane)).countP pred := by
    obtain ⟨hC,hA,_,_,_⟩ := hLane lane hl
    rw [countP_take_succ_false hA (hArrival _),countP_take_succ_false hC hCommit]
  let after : SchedulerWarpReached l X g 905 frame shuffles votes ends :=
    ⟨⟨fun lane => commit.pos lane+2,post,post,
      ⟨fun lane hl => (hCounts _ rfl (fun _ => rfl) lane hl).trans (commit.ordinals.shfl lane hl),
        fun lane hl => (hCounts _ rfl (fun _ => rfl) lane hl).trans (commit.ordinals.vote lane hl)⟩,
      fun lane hl => (hLane lane hl).2.2.2.2,fun _ _ => .refl,
      fun lane hl => (hLane lane hl).2.2.1⟩,fun _ _ => Nat.succ_pos _,
      fun lane hl => len_of_get (hLane lane hl).2.1,
      fun lane hl => releasedIfLast (hLane lane hl).2.1 (by intro h; cases h),
      fun lane hl => (hLane lane hl).2.2.2.1⟩
  exact ⟨rest,after,fun lane hl => ⟨rfl,(hLane lane hl).2.1⟩⟩

/-- The active loader has reached its terminal scan with its final ring positions and
the actual protected endpoints from the first request group. -/
structure CacheDrainNeighbors (p : Params) (l : Launch) (X : Execution) (g use : Nat) where
  shuffles : Nat
  votes : Nat
  ends : Nat → Option TState
  reached : SchedulerWarpReached l X g 1752
    (fun lane =>
      let thread := warpLane l g
      let words := fun i => b32 (drainCuQ p (laneOf l (thread i)))
      (2239,words (shflSource .down lane 1 31).1)::firstDrainWordsFrame p l (thread lane) use)
    shuffles votes ends

abbrev SingleVisitDrainNeighbors (p : Params) (l : Launch) (X : Execution) (g : Nat) :=
  CacheDrainNeighbors p l X g 2

/-- The terminal scheduler consumes its first neighbor exchange after any number of cache uses. -/
theorem cacheDrainNeighborsOfStart {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g use shuffles votes : Nat} (hg : g < l.threads) (hCuQ : DrainCuQProtected p X)
    {ends : Nat → Option TState} (cur : SchedulerWarpReached l X g 1744
      (fun lane => firstDrainTail p l (warpLane l g lane) use) shuffles votes ends) :
    Nonempty (CacheDrainNeighbors p l X g use) := by
  obtain ⟨ready⟩ := firstDrainNeighborsOfMaximal hp hMax hg hCuQ cur
  exact ⟨⟨shuffles+1,votes,ends,ready⟩⟩

/-- Two priming cache packets, the selected trip word and the protected CuQ
advance a single-visit warp into the final group scan. -/
theorem singleVisitDrainNeighborsOfValueCommit {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch shuffles votes seedShuffles seedVotes : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hCuQ : DrainCuQProtected p X)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hSingle : Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 = 1)
    {endsSeed ends : Nat → Option TState}
    (seed : SchedulerWarpReached l X g 415 (loaderPrimingFrontierFacts p l g batch)
      seedShuffles seedVotes endsSeed)
    {F : Nat → List (Nat × Value)} (commit : SchedulerWarpReached l X g 903 F shuffles votes ends) :
    Nonempty (SingleVisitDrainNeighbors p l X g) := by
  obtain ⟨_,cur,_⟩ := singleVisitAfterValuePublication hp hMax hg hw hCuQ hb hLo hHi
    hSingle seed commit
  obtain ⟨begun⟩ := singleVisitDrainStartOfPublished hp hg hw cur
  exact cacheDrainNeighborsOfStart hp hMax hg hCuQ begun

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
