-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaOutputOrder
import Kernels.TmlFa4Fwd.Proof.Thread.MmaIssueElection
import Kernels.TmlFa4Fwd.Proof.Thread.OutputCommitOrder
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
import Kernels.TmlFa4Fwd.Proof.Thread.MmaReleaseOrdinal
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Lemmas.Flow.ElectActor

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof

/-- Every actual fragment in the final O1 commit's CTA belongs to that issuer's
trace and precedes the commit. -/
theorem mmaBeforeSameCtaSecondOutputCommit {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {mma final : EvId} {d : Nat} {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    {spec : TcCommit.Spec} (hMma : X.MmaIssue mma d op accum mask)
    (hFinal : SecondOutputCommit X final spec)
    (hCta : mma.1 / l.block = final.1 / l.block) :
    TraceBefore X mma final := by
  obtain ⟨hWarp, _, _, _, _, hElectMma, hLaneMma⟩ := mmaIssueElection hp hX hMma
  obtain ⟨_, _, _, hElectFinal, hLaneFinal⟩ :=
    PTX.Kernels.TmlFa4Fwd.Mma.secondOutputCommitLeader hp hX hFinal.decoded
  obtain ⟨_, hGet⟩ := hMma
  have hSame : SameWarp l mma.1 final.1 :=
    ⟨⟨event_thread_lt hX hGet, event_thread_lt hX hFinal.decoded, hCta⟩,
      hWarp.trans (hFinal.issuerWarp hp hX).symm⟩
  have hIssuer := selected_elect_thread_unique hX.elect hElectMma hElectFinal
    hSame hLaneMma hLaneFinal
  exact mmaBeforeSecondOutputCommit hX ⟨_, hGet⟩ hFinal hIssuer

end PTX.Kernels.TmlFa4Fwd.Thread
