-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.InitialValueDescriptor
import Kernels.TmlFa4Fwd.Proof.Thread.MmaAllocatorExit
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
import Kernels.TmlFa4Fwd.Proof.TerminalSite
import Lemmas.Tmem.TmemPairRecord
import Lemmas.Tcgen05.TcCollectiveOrdinaryWaiting
import Lemmas.Order.WaitOrderObject
import Lemmas.Flow.ElectActor
import Lemmas.Step.WarpShfl

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.Assumption Prologue
open PTX.Kernels.TmlFa4Fwd.Mma (valueDescriptorEvent valueDescriptorSite)

noncomputable section

private theorem beforeDealloc {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g i free : Nat} {e : Event} {kind : Kind}
    (he : X.get (g,i) = some e) (hFree : X.get (g,free) = some ⟨2766,kind⟩)
    (hEarly : e.pc < 2766) : i < free := by
  have hCode : (kernel.code.drop 2766).all (fun i => staysPastEvent 2766 i.op) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hSegments : Assumptions.swExp2Sites.all (fun site =>
      match cuteExp2.matchAt kernel site with
      | some seg => decide (2766 ≤ seg.stop)
      | none => false) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  exact traceOrderOfPcFloor hX hCode hSegments he hFree hEarly
    (show 2766 ≤ 2766 by decide)

private theorem deallocationWitnessOfPeer {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g peer j ex : Nat}
    (hSame : SameWarp l g peer) (hExit : X.get (peer,ex) = some ⟨9205,.exit⟩)
    (hf : j < ex) (hFree : X.get (peer,j) = some ⟨2766,.tc (.resource .one
      none (.dealloc 0 512))⟩) :
    ∃ free group dst req,
      X.get (g,free) = some ⟨2766,.tc (.resource group dst req)⟩ ∧
      Witness l X (.thread (g,free)) (peer,j) := by
  have hLength : j+1 < (X.tr peer).length := by
    have h : ex < (X.tr peer).length := (List.getElem?_eq_some_iff.mp hExit).1
    omega
  obtain ⟨cta, r, hr, peerLane, hPeer⟩ := hX.tmemPairBlocking.performed hFree hLength
  have hR := (hX.tmemPair.1 cta).1 r hr
  have hValid := hR.2.2
  let lane : Fin 32 := ⟨laneOf l g, Nat.mod_lt _ (by decide)⟩
  have hSame' := Tmem.Pair.WarpRequest.event_sameWarp hValid lane peerLane
  rw [hPeer] at hSame'
  have hLane : laneOf l (r.own.event l lane).1 = laneOf l g := by
    have hLt := lane.isLt
    have hOff : r.own.warp * 32 + lane.val < l.block := by
      have h := hValid.2.1
      omega
    have hEq : r.own.cta * l.block + r.own.warp * 32 + lane.val =
      (r.own.warp * 32 + lane.val) + l.block * r.own.cta := by ring
    change (r.own.cta * l.block + r.own.warp * 32 + lane.val) % l.block % 32 = lane.val
    rw [hEq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hOff]
    simp [Nat.add_mod, Nat.mod_eq_of_lt hLt]
  have hThread : (r.own.event l lane).1 = g :=
    sameWarp_eq_of_lane_eq (Step.sameWarp_trans hSame' (sameWarp_symm hSame)) hLane
  have hGet := hValid.2.2.1 lane
  have hSource := hValid.2.2.1 peerLane
  rw [hPeer] at hSource
  have hPc : r.own.pc = 2766 := congrArg Event.pc (Option.some.inj (hSource.symm.trans hFree))
  let free := (r.own.event l lane).2
  have hId : r.own.event l lane = (g,free) := Prod.ext hThread rfl
  rw [hId, hPc] at hGet
  obtain ⟨rank,hRank⟩ := hValid.2.2.2
  have hK := hRank lane
  rw [hId] at hK
  have hRankPeer := hRank peerLane
  rw [hPeer] at hRankPeer
  have hFill : X.TcK (g,free) (((X.tr peer).take j).countP isTcColl) :=
    hRankPeer.2.symm ▸ hK
  have hMem : g ∈ warpLanes l peer := mem_warpLanes_of_sameWarp hSame
  refine ⟨free, r.group, r.own.dst, r.own.request, hGet, ?_⟩
  apply Witness.of_need
      (fills := fun ref => ∃ k, ref = .thread (g,k) ∧
        X.TcK (g,k) (((X.tr peer).take j).countP isTcColl))
  · simp only [Needs,hFree,KindNeeds,resourceNeeds,List.mem_append]
    exact .inl (.inl (List.mem_map.mpr ⟨g,hMem,rfl⟩))
  · exact present_of_len (List.getElem?_eq_some_iff.mp hGet).1
  · exact ⟨free,rfl,hFill⟩

private theorem valueBroadcastExitWitness {l : Launch} {X : Execution}
    {g peer i ex rank pc : Nat} {a recv : Value} {ok : Bool}
    (he : X.get (g,i) = some ⟨pc,.shfl .idx a 0 31 recv ok⟩) (hK : X.ShflK (g,i) rank)
    (hWarp : SameWarp l g peer) (hx : X.get (peer,ex) = some ⟨9205,.exit⟩)
    (hCount : ((X.tr peer).take ex).countP Execution.isShfl ≤ rank) :
    Witness l X (.thread (peer,ex)) (g,i) := by
  let mask := 2^32-1
  have hAt : X.MaskAt shflClass (g,i) mask rank .idx :=
    ⟨(maskK_shflClass _ _ _ _).mpr ⟨rfl,hK⟩, _, _, he, rfl, rfl⟩
  have hLane : laneOf l peer < 32 := Nat.mod_lt _ (by decide)
  have hBit : mask.testBit (laneOf l peer) = true := by
    rw [show mask = 2^32-1 by rfl, Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hLane
  have hExitK : X.MaskExitK shflClass (peer,ex) mask rank :=
    (maskExitK_shflClass _ _ _ _).mpr ⟨9205,hx,hCount⟩
  have hNeed := maskNeeds_mem l shflClass X (g,i) he rfl hLane hBit
  refine Witness.of_need l (by simpa only [Needs,he,KindNeeds] using hNeed)
    (present_of_len (List.getElem?_eq_some_iff.mp hx).1) ?_
  rw [Step.warpLane_of_sameWarp hWarp]
  exact ⟨ex,rfl,sameWarp_symm hWarp, mask,rank,.idx,hAt,.inr ⟨hBit,hExitK⟩⟩

/-- A peer cannot fill the initial V descriptor shuffle by exiting. Its actual
deallocation waits for the issuing lane, which reaches deallocation after the shuffle. -/
theorem InitialValueDescriptorSend.peerDidNotExit {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g peer i rank : Nat} {recv : Value} {ok : Bool} (hWarp : SameWarp l g peer)
    (hSend : InitialValueDescriptorSend l X (g,i) recv ok) (hK : X.ShflK (g,i) rank) :
    ¬ ShflExited X peer rank := by
  rintro ⟨ex,exitPc,hExit,hCount⟩
  obtain rfl := actualExitPc hX hExit
  obtain ⟨steady,he⟩ := hSend
  have hLo : 173 < (valueDescriptorSite steady).prepare+8 := by cases steady <;> decide
  have hHint : (valueDescriptorSite steady).prepare+8 ∉ registerHintSites := by
    cases steady <;> decide
  have hBody := roleBodyPcOfEvent hp hX he hLo hHint
  have hMma : warpIndex l g = 12 := by
    change roleBodyPc (warpIndex l g) ((valueDescriptorSite steady).prepare+8) at hBody
    cases steady <;> simp only [valueDescriptorSite, roleBodyPc] at hBody <;>
      split_ifs at hBody <;> omega
  have hMmaPeer : warpIndex l peer = 12 := hWarp.2.symm.trans hMma
  obtain ⟨j,hJ,hPeerFree⟩ := mmaDeallocBeforeExit hp hX hMmaPeer hExit
  obtain ⟨free,group,dst,req,hFree,hD⟩ :=
    deallocationWitnessOfPeer hX hWarp hExit hJ hPeerFree
  have hPcBound : (valueDescriptorSite steady).prepare + 8 < 2766 := by cases steady <;> decide
  have hIx : i < free := beforeDealloc hX he hFree hPcBound
  have hPrior : TraceBefore X (g,i) (g,free) :=
    ⟨rfl,hIx,(List.getElem?_eq_some_iff.mp hFree).1⟩
  have hPeerPrior : TraceBefore X (peer,j) (peer,ex) :=
    ⟨rfl,hJ,(List.getElem?_eq_some_iff.mp hExit).1⟩
  have h1 : DepStep l kernel X (.thread (peer,ex),false) (.thread (g,i),true) :=
    DepStep.of_witness l (valueBroadcastExitWitness he hK hWarp hExit hCount)
  have h2 : DepStep l kernel X (.thread (g,i),true) (.thread (g,free),false) :=
    DepStep.of_resumes l (Resumes.of_blocking he rfl hPrior)
  have h3 : DepStep l kernel X (.thread (g,free),false) (.thread (peer,j),true) :=
    DepStep.of_witness l hD
  have h4 : DepStep l kernel X (.thread (peer,j),true) (.thread (peer,ex),false) :=
    DepStep.of_resumes l (Resumes.of_blocking hPeerFree rfl hPeerPrior)
  exact hX.depStepAcyclic _ (.tail (.tail (.tail (.single h1) h2) h3) h4)

theorem InitialValueDescriptorSend.laneZeroDidNotExit {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g i rank : Nat} {recv : Value} {ok : Bool}
    (hSend : InitialValueDescriptorSend l X (g,i) recv ok) (hK : X.ShflK (g,i) rank) :
    ¬ ShflExited X (g-laneOf l g) rank := by
  have hg : g < l.threads := by
    obtain ⟨_, he⟩ := hSend
    exact event_thread_lt hX he
  obtain ⟨hw, _⟩ := laneZero_sameWarp (show 0 < l.block by rw [hp.block]; decide) hg
  exact peerDidNotExit hp hX hw hSend hK

/-- The received word has an actual same-instance lane-zero sender. Its decoded
descriptor station can be identified once those two paths are aligned. -/
theorem InitialValueDescriptorSend.actualLaneZeroWord {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g i rank : Nat} {recv : Value} {ok : Bool}
    (hSend : InitialValueDescriptorSend l X (g,i) recv ok) (hK : X.ShflK (g,i) rank) :
    ∃ j, X.ShflK (g-laneOf l g,j) rank ∧
      ∃ pc b c result valid,
        X.get (g-laneOf l g,j) = some ⟨pc,.shfl .idx recv b c result valid⟩ := by
  have hLive := hSend.laneZeroDidNotExit hp hX hK
  obtain ⟨steady, he⟩ := hSend
  have hSource := shflSource_idx (laneOf l g) (show 0 < 32 by decide)
  obtain ⟨_, hPeer⟩ := hX.shfl g i rank
    ((valueDescriptorSite steady).prepare + 8)
    .idx (b32 (PTX.Kernels.TmlFa4Fwd.Mma.valueDescriptorLow l 1)) 0 31 recv ok he hK
  rw [hSource, Nat.add_zero] at hPeer
  obtain ⟨j, pc, b, c, result, valid, hOrd, hWord⟩ := hPeer.resolve_right hLive
  exact ⟨j, hOrd, pc, b, c, result, valid, hWord⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread
