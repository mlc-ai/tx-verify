-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSecondBiasProgress
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderSecondBiasProgress
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

/-- The selected loader records its opening stage-one Bias expectation at its decoded site. -/
theorem openingSecondBiasExpectedAtOfMaximal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) {ends : Nat → Option TState}
    (hStart : OpeningSecondBiasReached l X g shuffles votes ends)
    (hReady : ∀ lane < 32, OpeningSecondBiasBlocked l X (warpLane l g lane) →
      let log := X.objects (biasEmptyObject l (g/l.block) 1)
      ∃ s, stateBefore log log.length = some s ∧ s.phase = 0) :
    OpeningSecondBiasBoxesReached l X g shuffles votes ends ∧
      ∃ issue, X.get issue =
        some ⟨763,.arrive (biasReadyObject l (g/l.block) 1) 32768 1 true .cta⟩ := by
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
  exact ⟨hWarp,issue,he⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
