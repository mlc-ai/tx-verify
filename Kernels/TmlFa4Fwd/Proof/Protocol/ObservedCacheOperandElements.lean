-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.CompetingCacheWrites
public import Kernels.TmlFa4Fwd.Proof.Protocol.CacheOperandFinite
import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderPhaseAlignment
import Kernels.TmlFa4Fwd.Proof.Thread.MmaCacheReleaseIssuer
import Kernels.TmlFa4Fwd.Proof.Thread.MmaIssueElection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.Proof PTX.AsyncCopy PTX.TcMma Thread
open PTX.Kernels.TmlFa4Fwd.Mma
open PTX.Kernels.TmlFa4Fwd.Loader (kvUseStage)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- A recorded recurring K operand element comes from a single finite BF16 word
of its selected cache publication. -/
theorem recurringKeyOperandElementInPrefix (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X) (stage : Fin 2)
    {g index d : Nat} {step : Fin 8} {op : OperandSpec} {accum : Bool} {mask : List Nat}
    (hKey : QkInstruction X (g,index) (recurringKeyBlock stage) step d op accum mask) {row k : Nat}
    (hr : row < 128) (hk : k < 16) {ops : MmaOperands}
    (hOps : X.async.mmaOperands (g,index) = some ops) :
    ∃ value, Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b row k = .ok value := by
  obtain ⟨wait,use,⟨done⟩,hEarlier,hUse,hBytes⟩ :=
    recurringKeyFragmentReadyBytesExact hp hX stage hKey
  have hMma : X.MmaIssue (g,index) d op accum mask := ⟨_,hKey.decoded⟩
  apply done.actualCacheOperandElement hp hX hFrame (recurringKeyBlock stage) step .key
    hr hk hMma hEarlier (fun b => hBytes (qkByteIndex row k b)) hOps
  intro issue group j spec word hPub hPhase hMember hWord b
  dsimp only
  intro hLoc other a data hWrite hCover
  have hCopy := ((group.member j spec).mp hMember).2.2
  have hShape := actualCopyShape hX hCopy
  have hSource : spec.dst.Covers (spec.dst.loc.at (2 * word + b.val)) := by
    have hb := b.isLt
    simp only [Acc.Covers, Loc.InRange, Loc.at, hShape.widthEq, true_and]
    exact ⟨by omega,by omega⟩
  rw [hEarlier.1] at hPub
  exact recurringKeyOperandWriterOrder hp hX stage hKey hUse hPub hPhase hMember hLoc hSource
    hWrite hCover

/-- The PV fragment's most recent successful V acquire identifies the selected
publication and every byte address of the recorded operand. -/
theorem valueOperandReadyInPrefix (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index d : Nat} {block : Fin 4} {step : Fin 8} {op : OperandSpec} {accum : Bool}
    {mask : List Nat} (hValue : PvInstruction X (g,index) block step d op accum mask) :
    ∃ use wait, Thread.Mma.LatestValueReadyUse l X g index use ∧
      Nonempty (Completed l X (g,wait) (kvUseStage use) (use/3)) ∧
      TraceBefore X (g,wait) (g,index) ∧
      ∀ byte, op.byteLoc .b byte = (cacheOperand l g block step use .value).byteLoc .b byte := by
  obtain ⟨use,_,wait,hDescriptor,hB,hShape,hPoll,_,_,hRank,hEarlier,hOnly⟩ :=
    Thread.Mma.actualValueReadyOfFragment hp hX hValue
  have hUse : Thread.Mma.LatestValueReadyUse l X g index use :=
    ⟨wait,hPoll,hRank,hDescriptor.2.2,hEarlier,hOnly⟩
  have hMma : X.MmaIssue (g,index) d op accum mask := ⟨_,hValue.decoded⟩
  have hWarp : Prologue.warpIndex l g = 12 := (mmaIssueElection hp hX hMma).1
  have hg := event_thread_lt hX hValue.decoded
  have hOrdinal := (hPoll.exactOccurrence hp hX hWarp).2.1
  have hCount := Thread.Mma.readyUsesAtPrefix hp hX hg hWarp wait
  dsimp only at hOrdinal hCount
  change (((X.tr g).take wait).filterMap readyEvent).length = use at hRank
  rw [← hCount,hRank] at hOrdinal
  obtain ⟨done⟩ := completedForObservedIssuer hp hX hWarp
    (Thread.Mma.sameCacheReleaseIssuer hp hX hMma) hPoll
    (actualEmptyGuardLower hp hX g (kvUseStage use))
  change (Thread.Mma.atPrefix l X g wait).kvAcquires (kvUseStage use) = use/3 at hOrdinal
  change Completed l X (g,wait) (kvUseStage use)
    ((Thread.Mma.atPrefix l X g wait).kvAcquires (kvUseStage use)) at done
  rw [hOrdinal] at done
  obtain ⟨hDesc,hLow,hHigh⟩ := hShape
  refine ⟨use,wait,hUse,⟨done⟩,hEarlier,fun j => ?_⟩
  simp only [OperandSpec.byteLoc,cacheOperand,pvOperands,hB,hDesc,hLow,hHigh,
    reduceCtorEq,false_and,↓reduceIte]
  rfl

/-- A recorded PV operand element comes from a single finite BF16 word of the V
publication acquired for the fragment, including the first and final packets. -/
theorem valueOperandElementInPrefix (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g index d : Nat} {block : Fin 4} {step : Fin 8}
    {op : OperandSpec} {accum : Bool} {mask : List Nat}
    (hValue : PvInstruction X (g,index) block step d op accum mask) {row k : Nat} (hr : row < 128)
    (hk : k < 16) {ops : MmaOperands} (hOps : X.async.mmaOperands (g,index) = some ops) :
    ∃ value, Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b row k = .ok value := by
  obtain ⟨use,wait,hUse,⟨done⟩,hEarlier,hBytes⟩ := valueOperandReadyInPrefix hp hX hValue
  have hMma : X.MmaIssue (g,index) d op accum mask := ⟨_,hValue.decoded⟩
  apply done.actualCacheOperandElement hp hX hFrame block step .value hr hk hMma hEarlier
    (fun b => hBytes (qkByteIndex row k b)) hOps
  intro issue group j spec word hPub hPhase hMember hWord b
  dsimp only
  intro hLoc other a data hWrite hCover
  have hCopy := ((group.member j spec).mp hMember).2.2
  have hShape := actualCopyShape hX hCopy
  have hSource : spec.dst.Covers (spec.dst.loc.at (2 * word + b.val)) := by
    have hb := b.isLt
    simp only [Acc.Covers, Loc.InRange, Loc.at, hShape.widthEq, true_and]
    exact ⟨by omega,by omega⟩
  rw [hEarlier.1] at hPub
  exact valueOperandWriterOrder hp hX hValue hUse hPub hPhase hMember hLoc hSource hWrite hCover

end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
