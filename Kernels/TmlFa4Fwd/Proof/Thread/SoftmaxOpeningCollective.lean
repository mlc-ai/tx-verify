-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.FirstScoreAcquire
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
import Kernels.TmlFa4Fwd.Proof.MmaResources
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Lemmas.Tcgen05.TcCollectiveOrdinaryWaiting
import Lemmas.Flow.NotTcData
import Lemmas.Step.Released

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption Prologue

set_option maxRecDepth 100000 in
private theorem noEarlyTensorData :
    (kernel.code.take 3428).all (fun ins => !tcDataOp ins.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem openingScoreFloor :
    (kernel.code.drop 3428).all (fun ins => Thread.staysPastEvent 3428 ins.op) = true := by
  kernel_rfl

set_option maxRecDepth 100000 in
private theorem openingScoreFloorSegments :
    Assumptions.swExp2Sites.all (fun pc => match cuteExp2.matchAt kernel pc with
      | some seg => decide (3428 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

private theorem noTensorDataBelowOpeningScore {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {e : Event}
    (he : X.get i = some e) (hPc : e.pc < 3428) (hData : isTcData e = true) : False := by
  rcases get_source hX he with ⟨_,hBad⟩ | ⟨_,ins,_,_,hc,hFire⟩
  · simp only [isTcData,hBad] at hData
    cases hData
  have hGet : (kernel.code.take 3428)[e.pc]? = some ins :=
    (List.getElem?_take_of_lt hPc).trans hc
  have hNot := List.all_eq_true.mp noEarlyTensorData ins (List.mem_of_getElem? hGet)
  have hYes := fires_tcData_op hFire hData
  simp only [hYes, Bool.not_true, Bool.false_eq_true] at hNot

private theorem noSoftmaxResource {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j pc : Nat} {grp : CtaGroup} {dst : Option Loc} {request : Tmem.Request}
    (he : X.get (g,j) = some ⟨pc,.tc (.resource grp dst request)⟩)
    (hWarp : warpIndex l g < 8) : False := by
  have hSites := (Mma.actualResourceRequest hX he).2
  have hLoc : pc = 1909 ∨ pc = 2763 ∨ pc = 2766 := by
    rcases hSites with ⟨h,_⟩ | ⟨h,_⟩ | ⟨h,_⟩ <;> aesop
  have hLo : 173 < pc := by rcases hLoc with h | h | h <;> omega
  have hHi : pc < 3103 := by rcases hLoc with h | h | h <;> omega
  have hHint : pc ∉ registerHintSites := by
    rcases hLoc with rfl | rfl | rfl <;> decide
  have hRole := roleBodyPcOfEvent hp hX he hLo hHint
  unfold roleBodyPc at hRole
  rcases hRole with h | h
  · have hExit : pc = 9205 := h
    omega
  · have h14 : ¬ 14 ≤ warpIndex l g := by omega
    have h13 : warpIndex l g ≠ 13 := by omega
    have h12 : warpIndex l g ≠ 12 := by omega
    simp only [ite_eq_right h14,ite_eq_right h13,ite_eq_right h12,ite_eq_left hWarp] at h
    omega

/-- Each opening score acquire immediately precedes the warp's first Tensor Memory collective
ordinal. Earlier metadata and scheduler events consume no Tensor Memory instance. -/
theorem openingScoreLoadOrdinal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g score : Nat} {stage : Fin 2} (hScore : Thread.Scores.FirstScoreAcquire l X (g,score) stage) :
    ((X.tr g).take (score+1)).countP isTcColl = 0 := by
  have hWarp := (hScore.role hp hX).1
  apply List.countP_eq_zero.mpr
  intro e hm
  obtain ⟨j,hLookup⟩ := List.mem_iff_getElem?.mp hm
  have hj : j < score+1 := by
    have hn := (List.getElem?_eq_some_iff.mp hLookup).1
    simp only [List.length_take] at hn
    omega
  have he : X.get (g,j) = some e := by
    change (X.tr g)[j]? = some e
    rwa [List.getElem?_take_of_lt hj] at hLookup
  have hPc : e.pc < 3428 := by
    by_contra! hAfter
    have hOrder := Thread.traceOrderOfPcFloor hX openingScoreFloor openingScoreFloorSegments
      hScore.decoded he (by change (3425 : Nat) < 3428; decide) hAfter
    omega
  by_contra hNot
  have hColl : isTcColl e = true := by simpa only [Bool.not_eq_false] using hNot
  obtain ⟨kind,hKind⟩ := TcCollective.kind_of_coll hColl
  obtain ⟨pc,actual⟩ := e
  change actual = .tc kind at hKind
  subst actual
  cases kind <;> simp only [isTcColl,Bool.false_eq_true] at hColl
  case resource grp dst request => exact noSoftmaxResource hp hX he hWarp
  all_goals exact noTensorDataBelowOpeningScore hX he hPc rfl

/-- A pending score load is released once all warp lanes have issued the same collective. -/
theorem openingScoreCollectiveReleased {l : Launch} {X : Execution}
    {g j pc addr ordinal : Nat} {vals : List Value}
    (he : X.get (g,j) = some ⟨pc,.tc (.ld addr vals .s32x32b)⟩)
    (hOrdinal : ((X.tr g).take j).countP isTcColl = ordinal)
    (hPeers : ∀ peer ∈ warpLanes l g, ∃ pos, X.TcK (peer,pos) ordinal)
    (hLast : j+1 = (X.tr g).length) :
    Step.Released l X g := by
  constructor
  intro site kind hGet _
  have hIndex : (X.tr g).length-1 = j := by omega
  rw [hIndex,he,Option.some.injEq] at hGet
  cases hGet
  rw [hIndex]
  intro need hNeed
  simp only [Needs,he,KindNeeds,tcNeeds] at hNeed
  obtain ⟨peer,hPeer,rfl⟩ := List.mem_map.mp hNeed
  obtain ⟨pos,hPos⟩ := hPeers peer hPeer
  obtain ⟨event,hEvent,_⟩ := hPos.1
  exact ⟨.thread (peer,pos),⟨event,hEvent⟩,pos,rfl,hOrdinal.symm ▸ hPos⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
