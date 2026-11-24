-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.InitialValueAcquire
import Kernels.TmlFa4Fwd.Proof.MmaFirstReadyParity
import Kernels.TmlFa4Fwd.Proof.Thread.OutputCommitOrder
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

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.Assumption
open PTX.Kernels.TmlFa4Fwd.Mma (readyHead readyEvent initialReadyPollOperands)

noncomputable section

private theorem keyFloorCode :
    (kernel.code.drop 2148).all (fun i => staysPastEvent 2148 i.op) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

private theorem keyFloorSegments : Assumptions.swExp2Sites.all (fun site =>
    match cuteExp2.matchAt kernel site with
    | some seg => decide (2148 ≤ seg.stop)
    | none => false) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

/-- The actual initial key acquire is the first successful cache poll on its issuing lane. -/
theorem initialKeyWaitOrdinal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j key : Nat} {commit : TcCommit.Spec} {loc : Loc} {parity : Nat} {acq : Bool}
    {scope : MbarScope} (hCommit : SecondOutputCommit X (g,j) commit)
    (hKey : X.get (g,key) = some ⟨2145,.wait loc parity true acq scope⟩) :
    (Thread.Mma.atPrefix l X g key).kvAcquires 0 = 0 := by
  obtain ⟨value,hV,_,hCount⟩ := initialValueAcquireBeforeSecondOutputCommit hp hX hCommit
  have hw := hCommit.issuerWarp hp hX
  obtain ⟨gate,hGate⟩ := hV.atGate hp hX hw
  have hLoc : Mma.Observation.readyObject l g 1 ≠
      Prologue.initObject l (g/l.block) (Loader.readySlot 0) := by
    intro h
    have hAddr := congrArg Loc.addr h
    simp only [Mma.Observation.readyObject,Loader.readySlot_address] at hAddr
    omega
  have hLater : 2148 ≤ readyHead gate := by
    fin_cases gate
    · exact (hLoc (initialReadyPollOperands hp hX hGate).1).elim
    · decide
    · decide
    · decide
  have hKeyFirst := traceOrderOfPcFloor hX keyFloorCode keyFloorSegments hKey hGate
    (show 2145 < 2148 by decide) hLater
  let e : Event := ⟨2145,.wait loc parity true acq scope⟩
  have hMark : readyEvent e = some (loc,parity) := by
    have hAny : (List.finRange 4).any (fun i => readyHead i == 2145) = true := by decide
    simp [e,readyEvent,hAny]
  have hTake : (X.tr g).take (key+1) = (X.tr g).take key ++ [e] := by
    change (X.tr g)[key]? = some e at hKey
    simp [List.take_add_one,hKey]
  have hMono := ((List.take_sublist_take_left (l := X.tr g)
    (show key+1 ≤ value by omega)).filterMap readyEvent).length_le
  rw [hTake,List.filterMap_append] at hMono
  simp only [List.filterMap_cons,hMark,List.filterMap_nil,List.length_append,
    List.length_cons,List.length_nil] at hMono
  have hUsed := Mma.readyUsesAtPrefix hp hX (event_thread_lt hX hKey) hw key
  change (((X.tr g).take value).filterMap readyEvent).length = 1 at hCount
  dsimp only at hUsed
  omega

end
end PTX.Kernels.TmlFa4Fwd.Thread
