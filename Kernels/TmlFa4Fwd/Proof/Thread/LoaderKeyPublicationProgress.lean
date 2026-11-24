-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderKeySecondProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.PrimingLoaderPublication
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
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
import Kernels.TmlFa4Fwd.Assumptions.WellFormed
import Lemmas.Step.CpAsyncIssueProgress
import Lemmas.Step.DrainInOrder

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.Assumption Prologue Epilogue

/-- A maximal loader at the end of a packet records its commit and actual arrive-on issue. -/
theorem copyCommitAndArriveOfMaximal {l : Launch} {m : Mem0} {X : Execution}
    (hMax : Maximal l kernel Assumptions.all m X) {g pos base : Nat} (hg : g < l.threads)
    (site : Fin 6) {s t : TState} {ending : Option TState}
    (ht : At t (copyCommitPc site) [((copyArrivalAddress site).1,b32 base)])
    (hWidth : base+(copyArrivalAddress site).2 < 2^32) (hAlign : base%8 = 0)
    (hSteps : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t)
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some s))
    (hTail : Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending)
    (hPos : 0 < pos) (hBound : pos ≤ (X.tr g).length)
    (hRelease : pos = (X.tr g).length → Step.Released l X g) :
    let loc : Loc := ⟨.shared,g/l.block,base+(copyArrivalAddress site).2⟩
    X.get (g,pos) = some ⟨copyCommitPc site,.asyncCommit⟩ ∧
    X.get (g,pos+1) = some ⟨copyCommitPc site+1,.asyncArrive loc true⟩ ∧
    Run kernel Assumptions.all l g {} ((X.tr g).take (pos+2)) (some (next (next t))) ∧
    Run kernel Assumptions.all l g (next (next t)) ((X.tr g).drop (pos+2)) ending := by
  let loc : Loc := ⟨.shared,g/l.block,base+(copyArrivalAddress site).2⟩
  obtain ⟨hc,ha⟩ := copyCommitTemplates (g := g) site ht hWidth hAlign
  have hn₀ : Next kernel Assumptions.all l g s t (.asyncCommit (next t)) := ⟨hSteps,hc⟩
  obtain ⟨he₀,hPast,hRest⟩ := Step.cp_async_issue_of_maximal hMax hg hn₀
    (fun _ _ => Iff.rfl) (.inr (.inl rfl)) hPrefix hTail hPos hBound hRelease
    (Assumptions.wfStep.quiet hMax.1 le_snoc rfl (Execution.noNewRead_snoc rfl))
  have hn₁ : Next kernel Assumptions.all l g (next t) (next t)
      (.asyncArrive loc true (next (next t))) := ⟨.refl,ha⟩
  obtain ⟨he₁,hDone,hPending⟩ := Step.cp_async_issue_of_maximal hMax hg hn₁
    (fun _ _ => Iff.rfl) (.inr (.inr ⟨loc,rfl⟩)) hPast hRest (by omega)
    (len_of_get he₀) (releasedIfLast he₀ (by intro h; cases h))
    (Assumptions.wfStep.quiet hMax.1 le_snoc rfl (Execution.noNewRead_snoc rfl))
  refine ⟨ht.1 ▸ he₀, ?_, hDone, hPending⟩
  simpa [next, ht.1] using he₁

set_option maxRecDepth 100000 in
private theorem primingCommitRegisterCode :
    ((kernel.code.drop 174).take (674-174)).all
      (fun ins => loaderPipelineCutOp 174 674 0 [2535] ins.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem primingCommitFinalCode :
    (kernel.code.drop 674).all (fun ins => Thread.staysPastEvent 674 ins.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem primingCommitFinalSegments :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some segment => decide (674 ≤ segment.stop)
      | none => false) = true := by kernel_rfl

private theorem remainsPastPrimingCommit {l : Launch} {g : Nat} {s u : TState}
    {events : List Event} (reach : TraceReach kernel Assumptions.all l g s events u)
    (hs : 674 ≤ s.pc) : 674 ≤ u.pc := by
  induction reach with
  | refl => exact hs
  | tau ht _ ih => exact ih (Thread.eventTailStepOfAudit primingCommitFinalCode
      primingCommitFinalSegments hs (.inl ⟨rfl,ht⟩))
  | event he _ ih => exact ih (Thread.eventTailStepOfAudit primingCommitFinalCode
      primingCommitFinalSegments hs (.inr ⟨_,rfl,he⟩))

set_option maxRecDepth 3000 in
private theorem sharedToPrimingCommit {l : Launch} {g : Nat} {s u : TState}
    {events : List Event} (reach : TraceReach kernel Assumptions.all l g s events u)
    (hu : u.pc = 673) (hs : 174 ≤ s.pc) (hShape : RingShape s)
    (hRegs : Holds s.regs [(2535,b32 l.sharedBase)]) : u.regs 2535 = some (b32 l.sharedBase) := by
  induction reach with
  | refl => exact hRegs.1
  | @tau t v u es ht hRest ih =>
    have hWhole := TraceReach.tau ht hRest
    have hUpper : t.pc < 674 := by
      by_contra! h
      have hPast := remainsPastPrimingCommit hWhole h
      omega
    obtain ⟨hLow,_,hNext,hKeep⟩ := pipelineCutStep (lower := 174) (cut := 674)
      (branch := 0) (F := [(2535,b32 l.sharedBase)]) (by decide) (by decide)
      ⟨hs,hUpper⟩ primingCommitRegisterCode (.inl ⟨rfl,ht⟩) hShape hRegs
    exact ih hu hLow hNext hKeep
  | @event t v u es e he hRest ih =>
    have hWhole := TraceReach.event he hRest
    have hUpper : t.pc < 674 := by
      by_contra! h
      have hPast := remainsPastPrimingCommit hWhole h
      omega
    obtain ⟨hLow,_,hNext,hKeep⟩ := pipelineCutStep (lower := 174) (cut := 674)
      (branch := 0) (F := [(2535,b32 l.sharedBase)]) (by decide) (by decide)
      ⟨hs,hUpper⟩ primingCommitRegisterCode (.inr ⟨_,rfl,he⟩) hShape hRegs
    exact ih hu hLow hNext hKeep

private theorem sharedAtPrimingCommit {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g pos : Nat} (hg : g < l.threads) (hw : 0 < warpIndex l g)
    (hPos : 5 ≤ pos) (hLength : pos ≤ (X.tr g).length) {t u : TState}
    (hPrefix : Run kernel Assumptions.all l g {} ((X.tr g).take pos) (some t))
    (hSteps : Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u)
    (hu : u.pc = 673) : u.regs 2535 = some (b32 l.sharedBase) := by
  obtain ⟨start,_,hStart,_,hPast,_⟩ := nonzeroCommonPrefix hp hX hg hw (hPos.trans hLength)
  have hTake : (X.tr g).take 5 ++ ((X.tr g).take pos).drop 5 = (X.tr g).take pos := by
    simpa only [List.take_take,Nat.min_eq_left hPos] using
      List.take_append_drop 5 ((X.tr g).take pos)
  have hReach := (hPast.after_returned_prefix (hTake.symm ▸ hPrefix)).returning_reach.append
    (TraceReach.of_local hSteps)
  exact sharedToPrimingCommit hReach hu (by rw [hStart.1])
    (ringShapeOfAt hStart) ⟨hStart.2.2.2.2.2.1,trivial⟩

/-- A reached first K commit advances each loader lane past its actual ready issue. -/
theorem primingKeyCursorAfterArrivalOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    (hShuffles : 5 ≤ shuffles) {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 673 F shuffles votes ends) :
    ∃ done : SchedulerWarpReached l X g 675 F shuffles votes ends,
      ∀ lane < 32, done.pos lane = cur.pos lane+2 ∧
        Thread.Loader.PrimingPublication l X (warpLane l g lane,cur.pos lane+1) 0 := by
  let after (lane : Nat) := next (next (cur.state lane))
  have hLane (lane : Nat) (hl : lane < 32) :
      let thread := warpLane l g lane
      X.get (thread,cur.pos lane) = some ⟨673,.asyncCommit⟩ ∧
      Thread.Loader.PrimingPublication l X (thread,cur.pos lane+1) 0 ∧
      Run kernel Assumptions.all l thread {} ((X.tr thread).take (cur.pos lane+2))
        (some (after lane)) ∧
      Run kernel Assumptions.all l thread (after lane) ((X.tr thread).drop (cur.pos lane+2))
        (ends lane) := by
    have hBlock : l.block%32 = 0 := by rw [hp.block]
    have hSame := (Step.sameWarp_lane hBlock hg hl).1
    have hLane : 0 < warpIndex l (warpLane l g lane) := by
      rw [show warpIndex l (warpLane l g lane) = warpIndex l g from hSame.2.symm]
      omega
    let thread := warpLane l g lane
    have hPos : 5 ≤ cur.pos lane := by
      have hBound : ((X.tr thread).take (cur.pos lane)).countP Execution.isShfl
          ≤ ((X.tr thread).take (cur.pos lane)).length := List.countP_le_length
      rw [cur.ordinals.shfl lane hl,List.length_take] at hBound
      omega
    have hs := cur.checkpoint lane hl
    have hBase := sharedAtPrimingCommit hp hMax.1 hSame.1.2.1 hLane hPos (cur.bounded lane hl)
      (cur.recorded lane hl) (cur.localSteps lane hl) hs.1
    have hAt : At (cur.state lane) (copyCommitPc 0)
        [((copyArrivalAddress 0).1,b32 l.sharedBase)] := hs.mono ⟨hBase,trivial⟩
    have hWidth : l.sharedBase+(copyArrivalAddress 0).2 < 2^32 := by
      have := hp.shared.2.1
      change l.sharedBase+32 < 2^32
      omega
    have hAlign : l.sharedBase%8 = 0 := by have := hp.shared.1; omega
    exact copyCommitAndArriveOfMaximal hMax hSame.1.2.1 0 hAt hWidth hAlign
      (cur.localSteps lane hl) (cur.recorded lane hl) (cur.continuation lane hl)
      (cur.positive lane hl) (cur.bounded lane hl) (cur.released lane hl)
  have hCounts (p : Event → Bool)
      (hCommit : p ⟨673,.asyncCommit⟩ = false)
      (hArrive : ∀ loc, p ⟨674,.asyncArrive loc true⟩ = false) :
      ∀ lane < 32, ((X.tr (warpLane l g lane)).take (cur.pos lane+2)).countP p =
        ((X.tr (warpLane l g lane)).take (cur.pos lane)).countP p := by
    intro lane hl
    obtain ⟨hc,ha,_,_⟩ := hLane lane hl
    rw [countP_take_succ_false ha (hArrive _),countP_take_succ_false hc hCommit]
  have hShuffles (lane : Nat) (hl : lane < 32) :
      ((X.tr (warpLane l g lane)).take (cur.pos lane+2)).countP Execution.isShfl = shuffles :=
    (hCounts _ rfl (fun _ => rfl) lane hl).trans (cur.ordinals.shfl lane hl)
  have hVotes (lane : Nat) (hl : lane < 32) :
      ((X.tr (warpLane l g lane)).take (cur.pos lane+2)).countP isFullWarpVote = votes :=
    (hCounts _ rfl (fun _ => rfl) lane hl).trans (cur.ordinals.vote lane hl)
  let done : SchedulerWarpReached l X g 675 F shuffles votes ends :=
    ⟨⟨fun lane => cur.pos lane+2,after,after,⟨hShuffles,hVotes⟩,
      fun lane hl => (hLane lane hl).2.2.2,fun _ _ => .refl,
      fun lane hl => (cur.checkpoint lane hl).next.next⟩,
      fun _ _ => Nat.zero_lt_succ _,fun lane hl => len_of_get (hLane lane hl).2.1,
      fun lane hl => releasedIfLast (hLane lane hl).2.1 (by intro h; cases h),
      fun lane hl => (hLane lane hl).2.2.1⟩
  exact ⟨done,fun lane hl => ⟨rfl,(hLane lane hl).2.1⟩⟩

/-- At the reached first K commit, every loader lane actually issues its ready notification. -/
theorem primingKeyArriveOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    (hShuffles : 5 ≤ shuffles) {F : Nat → List (Nat × Value)} {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 673 F shuffles votes ends) :
    ∀ lane < 32, ∃ arrive, Thread.Loader.PrimingPublication l X (warpLane l g lane,arrive) 0 := by
  obtain ⟨_,hDone⟩ := primingKeyCursorAfterArrivalOfMaximal hp hMax hg hw hShuffles cur
  intro lane hl
  exact ⟨cur.pos lane+1,(hDone lane hl).2⟩

end PTX.Kernels.TmlFa4Fwd.Loader
