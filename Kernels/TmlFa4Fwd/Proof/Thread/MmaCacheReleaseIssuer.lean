-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReleaseSource
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaIssueElection
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Lemmas.Flow.ElectActor

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX PTX.Proof PTX.TcMma PTX.Kernels.TmlFa4Fwd.Mma

/-- MMA fragments and K/V releases in one CTA use the same elected lane. -/
theorem sameCacheReleaseIssuer {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {d : Nat} {op : OperandSpec} {accum : Bool} {mask : List Nat}
    (hMma : X.MmaIssue i d op accum mask)
    {g index : Nat} {form : ReleaseForm} {spec : TcCommit.Spec}
    (hRelease : ReleaseIssue X g index form spec)
    (hCta : i.1 / l.block = g / l.block) : i.1 = g := by
  obtain ⟨hw,j,site,inst,leader,hElect,hLane⟩ := mmaIssueElection hp hX hMma
  have hSame : SameWarp l i.1 g :=
    ⟨⟨event_thread_lt hX hMma.choose_spec,event_thread_lt hX hRelease,hCta⟩,
      hw.trans (hRelease.issuerWarp hp hX).symm⟩
  obtain ⟨_,_,_,hReleased,hElected⟩ :=
    readyReleaseLeader hp hX (releaseIndex form) hRelease
  exact selected_elect_thread_unique hX.elect hElect hReleased hSame hLane hElected

end PTX.Kernels.TmlFa4Fwd.Thread.Mma
