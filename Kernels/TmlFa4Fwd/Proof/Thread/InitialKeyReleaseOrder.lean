-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReleaseSource
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaInitialKeyReady
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

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX PTX.Assumption
open PTX.Kernels.TmlFa4Fwd.Mma (commitSite releaseCommitSite initialQkBlock qkPc)

set_option maxRecDepth 100000 in
private theorem keyReleaseFloor :
    (kernel.code.drop 2274).all (fun i => staysPastEvent 2274 i.op) = true := by
  kernel_rfl

set_option maxRecDepth 100000 in
private theorem keyReleaseFloorSegments :
    Assumptions.swExp2Sites.all (fun pc =>
      match cuteExp2.matchAt kernel pc with
      | some seg => decide (2274 ≤ seg.stop)
      | none => false) = true := by
  kernel_rfl

/-- Every actual initial QK fragment on the release issuer's lane precedes its
K/V releases, including releases on later visits to the same cache slot. -/
theorem InitialQueryFragment.beforeCacheRelease {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {stage : Fin 2} {mma : EvId} {i : Nat} {form : ReleaseForm} {spec : TcCommit.Spec}
    (hMma : InitialQueryFragment X stage mma)
    (hRelease : ReleaseIssue X mma.1 i form spec) :
    TraceBefore X mma (mma.1,i) := by
  obtain ⟨step,_,_,_,_,he⟩ := hMma
  have hBefore : qkPc (initialQkBlock stage) + step.val < 2274 := by
    have := step.isLt
    fin_cases stage <;> first | (change 2197 + step.val < 2274; omega) |
      (change 2259 + step.val < 2274; omega)
  have hAfter : 2274 ≤ (commitSite (releaseCommitSite (releaseIndex form))).pc := by
    cases form <;> decide
  exact ⟨rfl,traceOrderOfPcFloor hX keyReleaseFloor keyReleaseFloorSegments he hRelease
    hBefore hAfter,len_of_get hRelease⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Mma
