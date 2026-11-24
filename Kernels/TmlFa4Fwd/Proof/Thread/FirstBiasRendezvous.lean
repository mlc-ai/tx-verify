-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.BiasBarrierProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.BiasFirstVisit
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderBiasCredits
import Kernels.TmlFa4Fwd.Proof.Thread.BiasReadRendezvous
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
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxBiasRelease
import Kernels.TmlFa4Fwd.Proof.PollSafety
import Kernels.TmlFa4Fwd.Proof.MarkedBarrierCut
import Kernels.TmlFa4Fwd.Flow.Code.Part055
import Lemmas.Order.DependencyWitness

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Proof PTX.Flow PTX.MBarrier PTX.AsyncCopy PTX.Assumption PTX.EventFrame
open Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Softmax
open PTX.Kernels.TmlFa4Fwd.Thread.Loader (biasEmptyObject)

set_option maxRecDepth 100000 in
private theorem afterFirstBiasBarrier :
    (kernel.code.drop 3584).all (fun i => Thread.staysPastEvent 3584 i.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem afterFirstBiasSegments :
    Assumptions.swExp2Sites.all (fun pc =>
      match cuteExp2.matchAt kernel pc with
      | some seg => decide (3584 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

private theorem firstBiasBarrierNoRepeat {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g earlier later id : Nat} (hBefore : earlier < later)
    (hEarlier : X.get (g,earlier) = some ⟨3583,.bar id (some 128) .sync⟩)
    (hLater : X.get (g,later) = some ⟨3583,.bar id (some 128) .sync⟩) : False := by
  obtain ⟨_,hr⟩ := hX.thr g (event_thread_lt hX hEarlier)
  have hLen : later < (X.tr g).length := len_of_get hLater
  obtain ⟨s,u,hStep,hRest⟩ := hr.after_event hEarlier (by omega)
  have hPc : s.pc = 3583 := (estep_source_pc hStep).symm
  have hNext : u.pc = 3584 := by
    rw [followsMarkedBarrier hPc Flow.code_3583 rfl hStep,hPc]
  obtain ⟨vs,hWalk⟩ := Mma.walkFromRun hRest
  let e : Event := ⟨3583,.bar id (some 128) .sync⟩
  have hDone : e ∈ (X.tr g).drop (earlier+1) := by
    apply List.mem_of_getElem? (i := later-(earlier+1))
    rwa [List.getElem?_drop,Nat.add_sub_of_le (show earlier+1 ≤ later by omega)]
  have hLate := Thread.eventTailEventsOfSegmentFloor afterFirstBiasBarrier
    (fun site _ hSite seg hMatch => by
      have h := List.all_eq_true.mp afterFirstBiasSegments site hSite
      rw [hMatch,decide_eq_true_eq] at h
      exact h) hWalk hNext.ge e hDone
  exact (by decide : ¬ 3584 ≤ 3583) hLate

/-- A lane's first Bias arrival has generation zero. -/
theorem firstBiasBarrierOrdinal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g pos : Nat} (stage : Fin 2)
    (he : X.get (g,pos) = some ⟨3583,.bar (11+stage.val) (some 128) .sync⟩) :
    observedBarrierOrdinal X (g,pos) (11+stage.val) = 0 := by
  apply List.countP_eq_zero.mpr
  intro e hMem hMark
  obtain ⟨j,hGet⟩ := List.mem_iff_getElem?.mp hMem
  have hLen := (List.getElem?_eq_some_iff.mp hGet).1
  rw [List.length_take] at hLen
  have hBefore : j < pos := by omega
  rw [List.getElem?_take_of_lt hBefore] at hGet
  obtain ⟨pc,count,mode,rfl⟩ := NamedBar.isBarId_form hMark
  change X.get (g,j) = some _ at hGet
  obtain ⟨hSite,hCount,hMode,_,_⟩ := actualNamedBarrier hp hX hGet
  have hId : 11+stage.val = 11 ∨ 11+stage.val = 12 := by fin_cases stage <;> decide
  obtain ⟨_,_,hCount',_⟩ := biasArrivalStage hp hX hId ⟨_,hGet,rfl⟩
  rcases biasCountSite hSite (hCount.symm.trans hCount') with rfl | rfl
  · rw [hCount',hMode] at hGet
    exact firstBiasBarrierNoRepeat hX hBefore hGet he
  · have hAfter := traceOrderOfPcFloor hX afterFirstBiasBarrier afterFirstBiasSegments
      he hGet (show 3583 < 3584 by decide) (show 3584 ≤ 5271 by decide)
    omega

/-- A recorded Bias-empty return depends on each participating lane's first
acquire, including in a prefix whose lanes may still be running. -/
theorem FirstBiasAcquire.beforeBiasReturnInPrefix {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X)
    {g wait : Nat} {stage : Fin 2} (hWait : FirstBiasAcquire l X g wait stage)
    (hWork : g/l.block < tilePrefix p p.batch*p.heads) (hWarp : warpIndex l g < 8)
    {empty : EvId} (hEmpty : X.Arrive empty (biasEmptyObject l (g/l.block) stage) 0 1 true .cta) :
    Relation.TransGen (DepStep l kernel X) (.thread (g,wait),true) (.thread empty,false) := by
  obtain ⟨h,j⟩ := empty
  obtain ⟨y,hEarly,hPeer,hPeerOrd⟩ := biasReturnInitialRendezvous hp hX stage hEmpty
  obtain ⟨site,hEmpty⟩ := hEmpty
  have hReady : X.get (g,wait) = some ⟨3498,.wait (waitLoc l g stage 2) 0 true true .cta⟩ :=
    hWait
  have hAddr := congrArg Loc.addr (biasReadyWaitAddress hp hX hReady (by decide))
  have hStage : warpIndex l g/4 = stage.val := by
    change l.sharedBase+(320+8*stage.val) = l.sharedBase+(320+8*(warpIndex l g/4)) at hAddr
    omega
  have hSite := actualBiasEmptyArrivalSite hp hX stage hEmpty rfl
  obtain ⟨_,_,_,_,_,hTarget⟩ := biasEmptyArriveFacts hp hX hEmpty hSite
  have hCta : g/l.block = h/l.block := congrArg Loc.cta hTarget
  have hLast := len_of_get hEmpty
  have hPass : y+1 < (X.tr h).length := by
    change y < j at hEarly
    change j < (X.tr h).length at hLast
    omega
  let id := 11+stage.val
  let hSrc := biasBarrierSources hp hX stage
  let hShape := biasBarrierShape hp stage
  have hMember : warpIndex l g ∈ biasParticipants stage :=
    (biasParticipantIff stage (warpIndex l g)).mpr ⟨hWarp,hStage⟩
  obtain ⟨x,mode,hOwn,hOwnOrd⟩ :=
    memberBarrierArrival hX hSrc hShape hPeer hPass hCta hMember (by
      intro hExit
      obtain ⟨k,hAt⟩ := firstBiasDecodedArrivalOfActiveExit hp hX hCuQ hWork hWarp hExit
      rw [hStage] at hAt
      exact ⟨k,.sync,⟨_,hAt,rfl⟩,(firstBiasBarrierOrdinal hp hX stage hAt).trans hPeerOrd.symm⟩)
  have hOwnBefore : TraceBefore X (g,wait) (g,x) := by
    obtain ⟨⟨ownSite,kind⟩,hGet,hKind⟩ := hOwn
    change kind = _ at hKind
    subst kind
    obtain ⟨hOwnSite,hCount,_,_,_⟩ := actualNamedBarrier hp hX hGet
    have hFloor : 3583 ≤ ownSite := by
      rcases biasCountSite hOwnSite hCount.symm with rfl | rfl <;> decide
    exact ⟨rfl,orderAtInitialBiasRendezvous hX hReady hGet
      (show 3498 < 3583 by decide) hFloor,len_of_get hGet⟩
  obtain ⟨key,hKey,hReleased⟩ := barrierSyncReturned hX hPeer hPass
  have hKeyEq : key = id := by
    obtain ⟨⟨peerSite,kind⟩,he,hKind⟩ := hPeer
    change kind = _ at hKind
    subst kind
    have h := hSrc.arrival_key hX hShape he (CtaBarK.arrival hKey)
    change key = id + 16 * observedBarrierOrdinal X (_,y) id at h
    rw [hPeerOrd,Nat.mul_zero,Nat.add_zero] at h
    exact h
  have hRelease : CtaBarrier.Released l.block (X.barriers (g/l.block)) id 0 := by
    unfold CtaBarDone at hReleased
    rw [hKeyEq,Nat.mod_eq_of_lt hShape.id_lt,Nat.div_eq_of_lt hShape.id_lt,← hCta] at hReleased
    exact hReleased
  have hOwnKey := barrierArrivalKeyOfReleased hX hSrc hShape hOwn
    ((hOwnOrd.trans hPeerOrd).symm ▸ hRelease)
  rw [hOwnOrd,hPeerOrd,Nat.mul_zero,Nat.add_zero] at hOwnKey
  change CtaBarArrivalK l X (g,x) id at hOwnKey
  rw [← hKeyEq] at hOwnKey
  obtain ⟨_,hRecord⟩ := hReleased
  have hWitness := Witness.of_ctaBarCounted hKey hRecord hOwnKey hCta
  obtain ⟨next,hNext⟩ := actualCanonicalPoll hX hReady
  have hFrom : Resumes kernel X (g,wait) (g,x) := ⟨hOwnBefore,by
    simp only [hReady,Option.map_some,Kind.resume]
    exact ⟨_,next,_,_,_,_,hReady,hNext,hOwnBefore⟩⟩
  obtain ⟨⟨peerSite,kind⟩,hPeerGet,hKind⟩ := hPeer
  change kind = _ at hKind
  subst kind
  have hTo : Resumes kernel X (h,y) (h,j) := Resumes.of_blocking hPeerGet rfl ⟨rfl,hEarly,hLast⟩
  exact ((Relation.TransGen.single (DepStep.of_resumes l hFrom)).tail
    (DepStep.of_witness l hWitness)).tail (DepStep.of_resumes l hTo)

end PTX.Kernels.TmlFa4Fwd.Thread.Scores
