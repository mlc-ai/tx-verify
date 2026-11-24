-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaAllocatorExit
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
import Lemmas.Order.WaitOrderEnables
import Lemmas.Step.WarpLanes
import Lemmas.Flow.Shuffle
import Lemmas.Flow.WarpScan
import Lemmas.Tcgen05.TcCollectiveOrdinaryWaiting
import Lemmas.Tmem.TmemPairHistory

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.Flow PTX.Assumption Prologue

noncomputable section

set_option maxRecDepth 100000 in
private theorem exitFloor :
    (kernel.code.drop 2763).all (fun i => staysPastEvent 2763 i.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem exitSegmentFloor :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (2763 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

private theorem deallocationPeer {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g h free : Nat}
    (hw : SameWarp l g h) (hLate : free+1 < (X.tr h).length)
    (hFree : X.get (h,free) = some ⟨2766,.tc (.resource .one none (.dealloc 0 512))⟩) :
    ∃ j, X.get (g,j) = some ⟨2766,.tc (.resource .one none (.dealloc 0 512))⟩ ∧
      Witness l X (.thread (g,j)) (h,free) := by
  have hReady := hX.dependency.ready _ (returned_of_tcColl hFree rfl hLate)
  obtain ⟨cta,request,member,lane,hLane⟩ := (Tmem.Pair.ReturnReady.of_ready hFree hReady).1
  have hW := ((hX.tmemPair.1 cta).1 request member).2.2
  have hHere := PTX.Tmem.Pair.WarpRequest.event_props hW lane
  rw [hLane] at hHere
  have hCta := hw.1.2.2.trans hHere.1
  have hWarp := hw.2.trans hHere.2.1
  let gl : Fin 32 := ⟨laneOf l g,Nat.mod_lt _ (by decide)⟩
  let j := request.own.indices gl
  have hj : request.own.event l gl = (g,j) := by
    have h1 := Nat.div_add_mod g l.block
    have h2 := Nat.div_add_mod (g % l.block) 32
    rw [hCta] at h1
    change g % l.block / 32 = request.own.warp at hWarp
    rw [hWarp] at h2
    change (request.own.cta*l.block+request.own.warp*32+(g % l.block)%32,j) = (g,j)
    rw [Nat.mul_comm request.own.cta, Nat.mul_comm request.own.warp]
    congr 1
    omega
  have hEvent := hW.2.2.1 lane
  rw [hLane,hFree] at hEvent
  have hPeer := hW.2.2.1 gl
  rw [hj,← Option.some.inj hEvent] at hPeer
  obtain ⟨k,hK⟩ := hW.2.2.2
  have hK₀ := hK lane
  have hKg := hK gl
  rw [hLane] at hK₀
  rw [hj,← hK₀.2] at hKg
  have hNeed := tcNeed_mem hFree (by rfl) (mem_warpLanes_of_sameWarp hw)
  exact ⟨j,hPeer,Witness.of_need l hNeed ⟨_,hPeer⟩ ⟨j,rfl,hKg⟩⟩

/-- A warp-12 lane cannot supply the early-exit alternative of another lane's
actual MMA-role shuffle. The exiting lane's full-warp deallocation would
require a later event of the receiving lane. -/
theorem mmaShufflePeerCannotExit {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g h index site rank b c : Nat} {mode : ShflMode} {sent recv : Value} {ok : Bool}
    (hw : SameWarp l g h) (hWarp : warpIndex l g = 12)
    (hShfl : X.get (g,index) = some ⟨site,.shfl mode sent b c recv ok⟩)
    (hRank : X.ShflK (g,index) rank) (hSite : site < 2763) :
    ¬ ShflExited X h rank := by
  rintro ⟨exit,exitSite,hExit,hBeforeRank⟩
  have hExitLength : exit < (X.tr h).length := PTX.len_of_get hExit
  have hPeerWarp : warpIndex l h = 12 := hw.2.symm.trans hWarp
  obtain ⟨free,hEarlier,hFree⟩ := mmaDeallocBeforeExit hp hX hPeerWarp hExit
  obtain ⟨j,hLater,hDeallocNeed⟩ := deallocationPeer hX hw (by omega) hFree
  have hShflEarlier := traceOrderOfPcFloor hX exitFloor exitSegmentFloor hShfl hLater hSite
    (show 2763 ≤ 2766 by decide)
  have hFirst : DepStep l kernel X (.thread (g,index),true) (.thread (g,j),false) :=
    .of_resumes l (Resumes.of_blocking hShfl rfl ⟨rfl,hShflEarlier,PTX.len_of_get hLater⟩)
  have hSecond : DepStep l kernel X (.thread (g,j),false) (.thread (h,free),true) :=
    .of_witness l hDeallocNeed
  have hThird : DepStep l kernel X (.thread (h,free),true) (.thread (h,exit),false) :=
    .of_resumes l (Resumes.of_blocking hFree rfl ⟨rfl,hEarlier,hExitLength⟩)
  have hLane : laneOf l h < 32 := Nat.mod_lt _ (by decide)
  have hBit : (2^32-1 : Nat).testBit (laneOf l h) = true := by
    rw [Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hLane
  have hNeed := maskNeeds_mem l shflClass X (g,index) hShfl rfl hLane hBit
  rw [Step.warpLane_of_sameWarp hw] at hNeed
  have hAt : X.MaskAt shflClass (g,index) (2^32-1) rank mode :=
    ⟨(maskK_shflClass _ _ _ _).mpr ⟨rfl,hRank⟩,_,_,hShfl,rfl,rfl⟩
  have hExitK : X.MaskExitK shflClass (h,exit) (2^32-1) rank :=
    (maskExitK_shflClass _ _ _ _).mpr ⟨exitSite,hExit,hBeforeRank⟩
  have hDependency :
      Need.node (fun x => ∃ j, x = .thread (h,j) ∧ MaskWait l shflClass X (h,j) (g,index)) ∈
        Needs l X (g,index) := by
    simpa only [Needs,hShfl,KindNeeds] using hNeed
  have hWitness : Witness l X (.thread (h,exit)) (g,index) :=
    .of_need l hDependency ⟨_,hExit⟩
      ⟨exit,rfl,sameWarp_symm hw,_,_,_,hAt,.inr ⟨hBit,hExitK⟩⟩
  have hLast : DepStep l kernel X (.thread (h,exit),false) (.thread (g,index),true) :=
    .of_witness l hWitness
  exact hX.depStepAcyclic _ ((((Relation.TransGen.single hFirst).tail hSecond).tail
    hThird).tail hLast)

/-- A lane-zero MMA broadcast has an actual sending lane with the same shuffle ordinal. -/
theorem mmaLaneZeroShuffleSource {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index site rank : Nat} {sent recv : Value} {ok : Bool}
    (hWarp : warpIndex l g = 12)
    (hShfl : X.get (g,index) = some ⟨site,.shfl .idx sent 0 31 recv ok⟩)
    (hRank : X.ShflK (g,index) rank) (hSite : site < 2763) :
    ∃ j senderSite a b peerRecv valid, X.ShflK (g-laneOf l g,j) rank ∧
      X.get (g-laneOf l g,j) = some ⟨senderSite,.shfl .idx recv a b peerRecv valid⟩ := by
  have hg := event_thread_lt hX hShfl
  have hWarpPeer := (laneZero_sameWarp (by rw [hp.block]; decide) hg).1
  have hReply := hX.shfl g index rank site .idx sent 0 31 recv ok hShfl hRank
  rw [shflSource_idx (laneOf l g) (by decide : 0 < 32)] at hReply
  simp only [Nat.add_zero] at hReply
  exact hReply.2.resolve_right (mmaShufflePeerCannotExit hp hX hWarpPeer hWarp
    hShfl hRank hSite)

end
end PTX.Kernels.TmlFa4Fwd.Thread
