-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaOutputOrder
import Kernels.TmlFa4Fwd.Proof.Thread.MmaFirstOutputIssuer
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionOutputReuseFence
import Lemmas.Order.OrderWaits

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Output
open PTX PTX.AsyncCopy

/-- A completed MMA's shared operand read precedes a generic access when a
covering proxy fence lies between its successful acquire and the access. -/
theorem operandReadBeforeProxyReuse {l : Launch} {X : Execution}
    {mma wait fence writer : EvId} {isB : Bool} {scope : MbarScope} {index : Nat}
    {loc : Loc} {value : Option Byte}
    (hRead : X.MmaRead mma isB index loc value)
    (hObserved : AsyncObserved X mma .mmaDone wait true scope)
    (hScope : ScopesMeet l .cluster mma.1 scope wait.1)
    (hFence : X.IsProxyFence fence (.async (some (.shared .cta))) none)
    (hFenceThread : fence.1 < l.threads) (hSpace : loc.space = .shared)
    (hOwner : loc.cta = fence.1/l.block) (hBefore : po X wait fence) (hAfter : po X fence writer) :
    modelCausality l X loc (.async mma (.mmaRead isB index)) (.thread writer) := by
  have hCover : ({loc,size := 1} : Acc).Covers loc := ⟨rfl,rfl,le_rfl,Nat.lt_succ_self _⟩
  have hReach : SameCluster l fence.1 writer.1 := by
    rw [← hAfter.1]
    exact ⟨hFenceThread,hFenceThread,rfl⟩
  exact ⟨⟨{loc,size := 1},false,⟨rfl,rfl,hRead.1⟩,hCover⟩,
    wait,.inr ⟨scope,hObserved,hScope⟩,
    .inl ⟨fence,some (.shared .cta),none,hFence,hFenceThread,⟨hSpace,hOwner⟩,hReach,
      .single (.inl hBefore),.single (.inl hAfter)⟩⟩

/-- Every shared MMA operand of the same CTA was observed
before the same correction lane's first output proxy publication. That fence
orders the actual operand effect before a later second-stage staging write. -/
theorem mmaOperandBeforeSecondStagingOfSameCta {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {mma writer : EvId} {d index : Nat} {op : TcMma.OperandSpec} {isB accum : Bool}
    {mask : List Nat} {a : Acc} {data : List Byte} {loc : Loc}
    (hStore : Thread.StageStagingWrite X writer 1 a data)
    (hCta : mma.1/l.block = writer.1/l.block)
    (hMma : X.MmaIssue mma d op accum mask)
    (hLoc : op.byteLoc (if isB then .b else .a) index = some loc)
    (hSpace : loc.space = .shared) (hAt : loc.cta = writer.1/l.block) :
    ∃ value, X.MmaRead mma isB index loc value ∧
      modelCausality l X loc (.async mma (.mmaRead isB index)) (.thread writer) := by
  obtain ⟨wait,fence,hWait,hFence,hBefore,hAfter⟩ := hStore.firstAcquireFenceBeforeSecond hp hX
  obtain ⟨first,s0,scope,hFirst,hFirstCta,hReads⟩ := Thread.firstOutputAcquireReads hp hX hWait
  have hWaitLane : wait.1 = writer.1 := hBefore.1.trans hAfter.1
  have hSame : mma.1/l.block = first.1/l.block :=
    hCta.trans ((congrArg (· / l.block) hWaitLane).symm.trans hFirstCta.2.2.symm)
  have hOrder := Thread.mmaBeforeSameCtaFirstOutputCommit hp hX hMma hFirst hSame
  obtain ⟨hObserved,hScope,value,hRead⟩ := hReads hMma hOrder.1 hOrder.2.1 hLoc
  obtain ⟨_,hF⟩ := hFence
  have hBeforeFence : po X wait fence := po_of_not_access hBefore.1 hBefore.2.1 hBefore.2.2
    (by rw [hF]; rfl)
  have hAfterFence : po X fence writer := po_of_source_not_access hAfter.1 hAfter.2.1 hAfter.2.2
    (by rw [hF]; rfl)
  have hLocCta : loc.cta = fence.1/l.block := by rwa [hAfter.1]
  exact ⟨value,hRead,operandReadBeforeProxyReuse hRead hObserved hScope ⟨_,hF⟩
    (PTX.Proof.event_thread_lt hX hF) hSpace hLocCta hBeforeFence hAfterFence⟩

/-- Every shared MMA operand on the final output issuer's lane was observed
before the same correction lane's first output proxy publication. That fence
orders the actual operand effect before a later second-stage staging write. -/
theorem mmaOperandBeforeSecondStaging {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {mma output writer : EvId} {d index : Nat} {op : TcMma.OperandSpec} {isB accum : Bool}
    {mask : List Nat} {spec : TcCommit.Spec} {a : Acc} {data : List Byte} {loc : Loc}
    (hStore : Thread.StageStagingWrite X writer 1 a data)
    (_hSecond : Thread.SecondOutputCommit X output spec)
    (hCta : SameCta l output.1 writer.1) (hLane : mma.1 = output.1)
    (hMma : X.MmaIssue mma d op accum mask)
    (hLoc : op.byteLoc (if isB then .b else .a) index = some loc)
    (hSpace : loc.space = .shared) (hAt : loc.cta = writer.1/l.block) :
    ∃ value, X.MmaRead mma isB index loc value ∧
      modelCausality l X loc (.async mma (.mmaRead isB index)) (.thread writer) := by
  exact mmaOperandBeforeSecondStagingOfSameCta hp hX hStore
    ((congrArg (· / l.block) hLane).trans hCta.2.2) hMma hLoc hSpace hAt

end PTX.Kernels.TmlFa4Fwd.Protocol.Output
