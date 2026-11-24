-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OutputCommitOrder
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
import Lemmas.Flow.NotTcMma

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.Assumption

set_option maxRecDepth 100000 in
private theorem noMmaAfterFirstOutput :
    (kernel.code.drop 2642).all (fun i => !tcMmaOp i.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem firstOutputFloor :
    (kernel.code.drop 2642).all (fun i => staysPastEvent 2642 i.op) = true := by kernel_rfl

set_option maxRecDepth 100000 in
private theorem firstOutputSegmentFloor :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some seg => decide (2642 ≤ seg.stop)
      | none => false) = true := by kernel_rfl

variable {l : Launch} {m : Mem0} {X : Execution} (hX : Consistent l kernel Assumptions.all m X)
include hX

private theorem mmaBeforeOutputCommitAt {mma commit : EvId} {d site : Nat} {op : TcMma.OperandSpec}
    {accum : Bool} {mask : List Nat} {spec : TcCommit.Spec} (hMma : X.MmaIssue mma d op accum mask)
    (hCommit : X.get commit = some ⟨site,.tc (.commit spec)⟩) (hLane : mma.1 = commit.1)
    (hSite : 2642 ≤ site)
    (hFloor : (kernel.code.drop site).all (fun i => staysPastEvent site i.op) = true)
    (hSegments : Assumptions.swExp2Sites.all (fun start => match cuteExp2.matchAt kernel start with
      | some seg => decide (site ≤ seg.stop)
      | none => false) = true) : TraceBefore X mma commit := by
  obtain ⟨g,i⟩ := mma
  obtain ⟨h,j⟩ := commit
  change g = h at hLane
  subst h
  obtain ⟨issue,hGet⟩ := hMma
  have hC : X.get (g,j) = some ⟨site,.tc (.commit spec)⟩ := hCommit
  have hIssue : issue < 2642 := by
    by_contra! hOther
    rcases get_source hX hGet with ⟨_,hBad⟩ | ⟨t,ins,o,_,hCode,hFires⟩
    · cases hBad
    have hOp := fires_tcMma_op hFires rfl
    have hIn : ins ∈ kernel.code.drop 2642 := by
      apply List.mem_of_getElem? (i := issue-2642)
      rwa [List.getElem?_drop,Nat.add_sub_of_le hOther]
    have hAbsent := List.all_eq_true.mp noMmaAfterFirstOutput _ hIn
    simp [hOp] at hAbsent
  exact ⟨rfl,traceOrderOfPcFloor hX hFloor hSegments hGet hC (hIssue.trans_le hSite)
    (Nat.le_refl site),(List.getElem?_eq_some_iff.mp hC).1⟩

/-- Every real MMA on the final O0 issuer's lane precedes that commit. -/
theorem mmaBeforeFirstOutputCommit {mma commit : EvId} {d : Nat} {op : TcMma.OperandSpec}
    {accum : Bool} {mask : List Nat} {spec : TcCommit.Spec} (hMma : X.MmaIssue mma d op accum mask)
    (hCommit : FirstOutputCommit X commit spec) (hLane : mma.1 = commit.1) :
    TraceBefore X mma commit := by
  exact mmaBeforeOutputCommitAt hX hMma hCommit hLane (by decide)
    firstOutputFloor firstOutputSegmentFloor

/-- Every real MMA on the final O1 issuer's lane precedes that commit. -/
theorem mmaBeforeSecondOutputCommit {mma commit : EvId} {d : Nat} {op : TcMma.OperandSpec}
    {accum : Bool} {mask : List Nat} {spec : TcCommit.Spec} (hMma : X.MmaIssue mma d op accum mask)
    (hCommit : SecondOutputCommit X commit spec) (hLane : mma.1 = commit.1) :
    TraceBefore X mma commit := by
  apply mmaBeforeOutputCommitAt hX hMma hCommit.decoded hLane (by decide)
  · set_option maxRecDepth 100000 in decide +kernel
  · set_option maxRecDepth 100000 in decide +kernel

end PTX.Kernels.TmlFa4Fwd.Thread
