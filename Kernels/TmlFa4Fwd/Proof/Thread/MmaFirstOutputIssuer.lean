-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaOutputOrder
import Kernels.TmlFa4Fwd.Proof.Thread.MmaIssueElection
import Kernels.TmlFa4Fwd.Proof.Thread.OutputCommitOrder
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Lemmas.Flow.ElectActor

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof

/-- Every actual MMA in the first output commit's CTA precedes that commit on its issuer's lane. -/
theorem mmaBeforeSameCtaFirstOutputCommit {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {mma final : EvId} {d : Nat} {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    {spec : TcCommit.Spec}
    (hMma : X.MmaIssue mma d op accum mask) (hFinal : FirstOutputCommit X final spec)
    (hSameCta : mma.1 / l.block = final.1 / l.block) :
    TraceBefore X mma final := by
  obtain ⟨hWarp, _, _, _, _, hElect, hLane⟩ := mmaIssueElection hp hX hMma
  obtain ⟨_, _, _, hElect', hLane'⟩ := Mma.firstOutputCommitLeader hp hX hFinal
  obtain ⟨_, he⟩ := hMma
  obtain ⟨_, hf⟩ := hFinal.issued
  have hFinalWarp := hFinal.issuerWarp hp hX
  have hWarpSame : SameWarp l mma.1 final.1 :=
    ⟨⟨event_thread_lt hX he, event_thread_lt hX hf, hSameCta⟩, hWarp.trans hFinalWarp.symm⟩
  have hIssuer := selected_elect_thread_unique hX.elect hElect hElect' hWarpSame hLane hLane'
  exact mmaBeforeFirstOutputCommit hX ⟨_, he⟩ hFinal hIssuer

end PTX.Kernels.TmlFa4Fwd.Thread
