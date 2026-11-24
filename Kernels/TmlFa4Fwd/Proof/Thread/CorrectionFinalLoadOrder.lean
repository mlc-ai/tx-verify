-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStagingAcquire
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionTmemAddress
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaOutputOrder
import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvPipeline
import Kernels.TmlFa4Fwd.Proof.Thread.InitialValuePhase
import Kernels.TmlFa4Fwd.Proof.Thread.QueryOutputCommit

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Correction
open PTX PTX.Proof PTX.TcMma PTX.AsyncCopy
open PTX.Kernels.TmlFa4Fwd.Correction (finalizeLoadPc)

/-- The recorded acquire before a final correction load observes completion of
the actual MMA operand snapshot in its CTA. -/
theorem mmaDoneBeforeFinalizationLoad {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) (chunk : Fin 16) {i load : EvId} {addr : Nat}
    {vals : List Value} {shape : TcShape}
    (he : X.get load = some ⟨finalizeLoadPc stage chunk,.tc (.ld addr vals shape)⟩)
    {d : Nat} {op : OperandSpec} {acc : Bool} {mask : List Nat}
    (hMma : X.MmaIssue i d op acc mask) (hOwner : i.1/l.block = load.1/l.block)
    {index : Nat} {loc : Loc} (hLoc : op.byteLoc .b index = some loc) :
    DoneBefore l X i load := by
  fin_cases stage
  · obtain ⟨wait,hWait,hPo⟩ := firstAcquireBeforeFinalizationLoad hp hX 0 he
    obtain ⟨output,s,scope,hCommit,hCta,hReads⟩ := firstOutputAcquireReads hp hX hWait
    obtain ⟨q,_,_,_,_,_,_,hQlane,_,hQk,_⟩ :=
      firstOutputCommitHasQueryFragmentOfPrefix hp hX hCommit
    have hPeerCta : i.1/l.block = q.1/l.block := by
      rw [hQlane,hCta.2.2,hPo.1]
      exact hOwner
    have hLane := (mmaIssueSameThread hp hX hMma hQk hPeerCta).trans hQlane
    have hOrder := mmaBeforeFirstOutputCommit hX hMma hCommit hLane
    obtain ⟨hObserve,hScope,_⟩ := hReads (isB := true) hMma hLane hOrder.2.1 hLoc
    exact .inl ⟨wait,scope,hObserve,hScope,.single (.inl hPo)⟩
  · obtain ⟨wait,hWait,hPo⟩ := secondAcquireBeforeFinalizationLoad hp hX he
    obtain ⟨output,s,scope,hCommit,hCta,hReads⟩ := secondOutputAcquireReads hp hX hWait
    obtain ⟨_,hInitial⟩ := initialValueIssuesBeforeSecondOutputCommitExact hp hX hCommit
    obtain ⟨q,_,_,_,_,_,hPv,_,hPvOrder⟩ := hInitial 1 0
    have hPeerCta : i.1/l.block = q.1/l.block := by
      rw [hPvOrder.1,hCta.2.2,hPo.1]
      exact hOwner
    have hLane := (mmaIssueSameThread hp hX hMma hPv hPeerCta).trans hPvOrder.1
    have hOrder := mmaBeforeSecondOutputCommit hX hMma hCommit hLane
    obtain ⟨hObserve,hScope,_⟩ := hReads (isB := true) hMma hLane hOrder.2.1 hLoc
    exact .inl ⟨wait,scope,hObserve,hScope,.single (.inl hPo)⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Correction
