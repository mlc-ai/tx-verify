-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderQueryBoxProgress
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPollProgress
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
import Kernels.TmlFa4Fwd.Flow.Code.Part011
import Lemmas.Flow.ReturningPrefix

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.EventFrame PTX.MBarrier
open Prologue Epilogue Thread.Loader

noncomputable section

private def secondBiasWaitSite : DrainWaitSite := ⟨756,9610,1917,1918⟩

private def secondBiasWaitFrame (l : Launch) : List (Nat × Value) :=
  [(1917,b32 (l.sharedBase+344)),(1918,b32 1)] ++ secondQueryBaseFrame l

private theorem secondBiasWaitLocal {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {s : TState} (hs : At s 754 (secondQueryBaseFrame l)) :
    ∃ t, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t ∧
      At t 756 (secondBiasWaitFrame l) := by
  have hAddr : l.sharedBase+344 < 2^32 := by have := hp.shared.2.1; omega
  have hSeg : Seg kernel [] l g 2 754 (secondQueryBaseFrame l) 756 (secondBiasWaitFrame l) := by
    intro t ht
    dsimp [secondBiasWaitFrame,secondQueryBaseFrame] at *
    seg_fp ht using first | rfl | norm_bits [Nat.mod_eq_of_lt hAddr]
  obtain ⟨t,ht,hAt⟩ := hSeg s hs
  exact ⟨t,run_rtg ((loaderLinear (regs := []) (by decide) (by decide) hs.1
    (by decide +kernel) (by decide +kernel) ht).1),hAt⟩

private theorem secondBiasElectOut {l : Launch} {g : Nat} {s : TState}
    (hPc : s.pc = 759) (hFault : s.fault = none) :
    out kernel Assumptions.all l g s =
      .ev (.elect 4294967295 (inputElectReturn l g s 1919 158)) :=
  inputElectOut hPc hFault (by decide) (by decide) Flow.code_759

private theorem secondBiasElectFloor {l : Launch} {g : Nat} {s t : TState} {events : List Event}
    (h : TraceReach kernel Assumptions.all l g s events t) (hs : 760 ≤ s.pc) : 760 ≤ t.pc := by
  induction h with
  | refl => exact hs
  | tau ht _ ih =>
    exact ih (Thread.eventTailStepOfAudit (by decide +kernel) (by decide +kernel) hs
      (.inl ⟨rfl,ht⟩))
  | event he _ ih =>
    exact ih (Thread.eventTailStepOfAudit (by decide +kernel) (by decide +kernel) hs
      (.inr ⟨_,rfl,he⟩))

private theorem secondBiasChoice {l : Launch} {g : Nat} (take : Bool) {s : TState}
    (hs : At s 760 ((158,.pred take) :: secondQueryBaseFrame l)) :
    ∃ t, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t ∧
      At t (if take then 762 else 764) (secondQueryBaseFrame l) :=
  inputBoxChoice take (by decide) (by decide) Flow.code_760 Flow.code_761
    (by simp [secondQueryBaseFrame]) hs

private theorem secondBiasExpectationNext {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    {g : Nat} {s : TState} (hs : At s 760 ((158,.pred true) :: secondQueryBaseFrame l)) :
    ∃ t u, t.pc = 763 ∧ At u 764 (secondQueryBaseFrame l) ∧
      Next kernel Assumptions.all l g s t
        (.arrive (biasReadyObject l (g/l.block) 1) 32768 u 1 true .cta) := by
  let F := secondQueryBaseFrame l
  obtain ⟨w,hw,hAt⟩ := secondBiasChoice (g := g) true hs
  have hSetup : Seg kernel [] l g 1 762 F 763 ((1920,b32 32768) :: F) := by
    intro t ht
    dsimp [F,secondQueryBaseFrame] at *
    seg_fp ht using rfl
  obtain ⟨t,ht,hT⟩ := hSetup w hAt
  have hLocal := (loaderLinear (regs := []) (by decide) (by decide) hAt.1
    (by simp) (by decide) ht).1
  let loc := biasReadyObject l (g/l.block) 1
  let u := next (mbarStateDest t (some 7594))
  have hOut : out kernel Assumptions.all l g t = .ev (.arrive loc 32768 u 1 true .cta) := by
    rw [loaderOutCore (by rw [hT.1]; decide) (by rw [hT.1]; decide)]
    rw [out_event hT.2.2.2.1 (by rw [hT.1]; exact Flow.code_763) rfl rfl]
    have hBase : l.sharedBase+328 < 2^32 := by have := hp.shared.2.1; omega
    have hAlign : (l.sharedBase+328)%8 = 0 := by have := hp.shared.1; omega
    have hEff : effAddr l g t .shared 2535 328 = .ok loc :=
      effAddr_b32_off hT.2.2.2.2.2.1 hBase
    have hLoc : mbarLoc l g t 2535 328 = .ok loc := by
      simp [mbarLoc,hEff,loc,biasReadyObject,hAlign,bind,Except.bind,pure,Except.pure]
    have hOne : readBits l g t 32 (.imm 1) = .ok 1#64 := rfl
    simp [eventTmpl,widenMbarScope,tmaTmpl,hLoc,readBits_b32 hT.2.2.2.2.1 (by decide),
      hOne,u,bind,Except.bind,pure,Except.pure,ofExec]
  have hU : At u 764 F := by
    refine ⟨by change t.pc+1 = 764; rw [hT.1],hT.2.1,hT.2.2.1,hT.2.2.2.1,?_⟩
    simp [Holds,F,secondQueryBaseFrame,u,mbarStateDest,next,hT.2.2.2.2.2.1]
  exact ⟨t,u,hT.1,hU,hw.trans (run_rtg hLocal),hOut⟩

/-- The stage-one Bias expectation has been recorded and its boxes are next. -/
def OpeningSecondBiasBoxesReached (l : Launch) (X : Execution) (g shuffles votes : Nat)
    (ends : Nat → Option TState) : Prop :=
  Nonempty (SchedulerWarpReached l X g 764 (fun _ => secondQueryBaseFrame l) shuffles votes ends)

/-- The selected loader acquires its opening stage-one Bias buffer and records an expectation. -/
theorem openingSecondBiasExpectedOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) {ends : Nat → Option TState}
    (hStart : OpeningSecondBiasReached l X g shuffles votes ends)
    (hReady : ∀ lane < 32, OpeningSecondBiasBlocked l X (warpLane l g lane) →
      let log := X.objects (biasEmptyObject l (g/l.block) 1)
      ∃ s, stateBefore log log.length = some s ∧ s.phase = 0) :
    OpeningSecondBiasBoxesReached l X g shuffles votes ends ∧
      ∃ issue, X.Arrive issue (biasReadyObject l (g/l.block) 1) 32768 1 true .cta := by
  obtain ⟨start⟩ := hStart
  obtain ⟨cur⟩ := start.advanceLocal (pc' := 756) (G := fun _ => secondBiasWaitFrame l)
    (fun lane hl => secondBiasWaitLocal hp (g := warpLane l g lane) (start.checkpoint lane hl))
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hAddr : l.sharedBase+344 < 2^32 := by have := hp.shared.2.1; omega
  have hAlign : (l.sharedBase+344)%8 = 0 := by have := hp.shared.1; omega
  have hCode : LoaderWaitCode secondBiasWaitSite := ⟨Flow.code_756,Flow.code_757,Flow.code_758⟩
  obtain ⟨atElection⟩ := loaderWarpWaitOfReadyLast hMax hg hBlock hCode
    (by decide) hAddr hAlign cur (fun _ _ => by simp [secondBiasWaitFrame,secondBiasWaitSite,
      secondQueryBaseFrame]) (fun _ _ => by simp [secondBiasWaitFrame,secondBiasWaitSite])
    (fun _ _ => by simp [secondBiasWaitFrame,secondBiasWaitSite])
    (fun lane hl {_ _} hRun hLocal hAt => hReady lane hl ⟨_,_,hRun,hLocal,hAt.1⟩)
  let post := fun lane => inputElectReturn l (warpLane l g lane) (atElection.state lane) 1919 158
  let frame := fun (lane leader : Nat) => (158,.pred (lane == leader)) :: secondQueryBaseFrame l
  have hFresh (lane : Nat) (hl : lane < 32) (j : Nat) (hj : j < atElection.pos lane)
      (mask inst leader : Nat) : ¬ X.Elect (warpLane l g lane,j) 759 mask inst leader := by
    intro he
    have hTrace := (atElection.recorded lane hl).returning_reach.append
      (TraceReach.of_local (atElection.localSteps lane hl))
    have hGet : ((X.tr (warpLane l g lane)).take (atElection.pos lane))[j]? =
        some ⟨759,.elect mask inst leader⟩ := by rwa [List.getElem?_take_of_lt hj]
    exact inputElectionFresh secondBiasElectOut secondBiasElectFloor hTrace
      (atElection.checkpoint lane hl).1 mask inst leader
      (List.mem_append_left [] (List.mem_of_getElem? hGet))
  obtain ⟨leader,elected,_⟩ := atElection.consumeElection hp hMax hg post frame
    hFresh (fun lane hl => secondBiasElectOut (atElection.checkpoint lane hl).1
      (atElection.checkpoint lane hl).2.2.2.1) (fun lane hl leader => by
      have hAt := atElection.checkpoint lane hl
      have hLane : laneOf l (warpLane l g lane) = lane := (Step.sameWarp_lane hBlock hg hl).2
      have hBase := hAt.2.2.2.2.2.2.1
      exact ⟨by simp [post,inputElectReturn,next,setReg,hAt.1,secondBiasWaitSite],
        hAt.2.1,hAt.2.2.1,hAt.2.2.2.1,by
          simp [Holds,frame,post,inputElectReturn,next,setReg,secondQueryBaseFrame,hBase,hLane]⟩)
  obtain ⟨hWarp,issue,he⟩ := expectationOfElectedWarp hp hMax hg
    (fun cta => biasReadyObject l cta 1)
    (site := 763) (F := fun _ => secondQueryBaseFrame l) elected leader
    (by
      apply secondBiasExpectationNext hp (g := warpLane l g leader)
      simpa [frame,secondBiasWaitSite] using elected.checkpoint leader leader.isLt)
    (fun lane hl hLeader => by
      have hAt : At (elected.state lane) 760 ((158,.pred false) :: secondQueryBaseFrame l) := by
        simpa only [frame,secondBiasWaitSite,beq_eq_false_iff_ne.mpr hLeader] using
          elected.checkpoint lane hl
      exact secondBiasChoice (g := warpLane l g lane) false hAt)
  exact ⟨hWarp,issue,763,he⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
