-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.InitialCacheOperandOrder
public import Kernels.TmlFa4Fwd.Proof.Protocol.ObservedPrimingKey
public import Kernels.TmlFa4Fwd.Proof.Protocol.ObservedPrimingValue
import Kernels.TmlFa4Fwd.Proof.Protocol.CacheOperandWriterOrder
import Kernels.TmlFa4Fwd.Proof.Thread.MmaInitialKeyPrefixReady
import Kernels.TmlFa4Fwd.Proof.Thread.MmaIssueElection
import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderPhaseAlignment
import Kernels.TmlFa4Fwd.Proof.Thread.MmaCacheReleaseIssuer

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.Proof PTX.AsyncCopy PTX.TcMma Thread
open PTX.Kernels.TmlFa4Fwd.Mma

/-- An actual opening QK fragment reads the first tile's selected K byte or
zero fill. The writer remains identifiable in an unfinished execution. -/
theorem initialKeyOperandByteInPrefix {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {batch : Nat} {stage : Fin 2} {g index d : Nat}
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1) * p.heads)
    (hInit : Thread.Mma.InitialQueryFragment X stage (g,index))
    (step : Fin 8) {row k byte : Nat} (hr : row < 128) (hk : k < 16) (hByte : byte < 2)
    {accum : Bool} {mask : List Nat}
    (hMma : X.MmaIssue (g,index) d (qkOperands l g (initialQkBlock stage) step 0) accum mask) :
    let coords := Epilogue.assignedCoordinates p batch (g/l.block)
    let key := 128 * (trips p batch coords.1 - 1) + row
    ∃ loc, (qkOperands l g (initialQkBlock stage) step 0).byteLoc .b
      (qkByteIndex row k byte) = some loc ∧
      OperandByteSource l X (g,index) true (qkByteIndex row k byte) loc
        (if key < p.kLength batch then
          (Value.float .bf16 (qkKey p batch coords.2 key (16 * step.val + k))).byteAt byte
        else zeroByte) := by
  obtain ⟨wait,hPoll,hEarlier,hOrdinal⟩ := hInit.keyReadyInPrefix hp hX
  have hWarp : Prologue.warpIndex l g = 12 := (mmaIssueElection hp hX hMma).1
  obtain ⟨done⟩ := completedForObservedIssuer hp hX hWarp
    (Thread.Mma.sameCacheReleaseIssuer hp hX hMma) hPoll (actualEmptyGuardLower hp hX g 0)
  rw [hOrdinal] at done
  obtain ⟨loc,pub,group,j,copy,hPub,hPhase,hMember,_,hCover,_,hLoc,hValue⟩ :=
    done.initialKeyOperandWithPublication hp hX hFrame (initialQkBlock stage) step hb hLo hHi
      hr hk hByte hMma hEarlier
  refine ⟨loc,hLoc,hValue ?_⟩
  intro other a bs hWrite hOther
  apply cacheOperandOrderOfCopyOrder hp hX hMma hLoc _ hWrite hOther
  intro r spec hCopy hOverlap
  exact (initialKeyCopyCompetitors hp hX hInit hMma hPub hPhase hMember hLoc hCover
    r spec hCopy hOverlap).elim .inl (.inr ∘ .inr)

/-- An actual PV fragment using ready use one reads the first tile's selected V
byte or zero fill, including when the execution is an unfinished prefix. -/
theorem initialValueOperandByteInPrefix {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {batch : Nat} {g index d : Nat}
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1) * p.heads)
    (steady : Bool) (stage : Fin 2) (step : Fin 8) {row k byte : Nat}
    (hr : row < 128) (hk : k < 16) (hByte : byte < 2)
    {op : OperandSpec} {accum : Bool} {mask : List Nat}
    (hPv : PvInstruction X (g,index) (firstPvBlock steady stage) step d op accum mask)
    (hLatest : Thread.Mma.LatestValueReadyUse l X g index 1) :
    let coords := Epilogue.assignedCoordinates p batch (g/l.block)
    let key := 128 * (trips p batch coords.1 - 1) + pvKeyRow step k
    ∃ loc, op.byteLoc .b (qkByteIndex row k byte) = some loc ∧
      OperandByteSource l X (g,index) true (qkByteIndex row k byte) loc
        (if key < p.kLength batch then
          (Value.float .bf16 (pvValue p batch coords.2 key row)).byteAt byte
        else zeroByte) := by
  obtain ⟨use,_,wait,hDescriptor,hB,_,hPoll,_,_,hRank,hEarlier,hOnly⟩ :=
    Thread.Mma.actualValueReadyOfFragment hp hX hPv
  have hUse : Thread.Mma.LatestValueReadyUse l X g index use :=
    ⟨wait,hPoll,hRank,hDescriptor.2.2,hEarlier,hOnly⟩
  have hOne := hUse.unique hLatest
  have hRankOne := hRank.trans hOne
  rw [hOne] at hB hPoll
  have hMma : X.MmaIssue (g,index) d op accum mask := ⟨_,hPv.decoded⟩
  have hWarp : Prologue.warpIndex l g = 12 := (mmaIssueElection hp hX hMma).1
  have hLane := event_thread_lt hX hPv.decoded
  have hOrdinal := (hPoll.exactOccurrence hp hX hWarp).2.1
  have hCount := Thread.Mma.readyUsesAtPrefix hp hX hLane hWarp wait
  dsimp only at hOrdinal hCount
  change (((X.tr g).take wait).filterMap readyEvent).length = 1 at hRankOne
  rw [← hCount,hRankOne] at hOrdinal
  have hReady : Thread.Mma.ReadyPoll l X g wait 1 0 true .cta := hPoll
  obtain ⟨done⟩ := completedForObservedIssuer hp hX hWarp
    (Thread.Mma.sameCacheReleaseIssuer hp hX hMma) hReady (actualEmptyGuardLower hp hX g 1)
  change (Thread.Mma.atPrefix l X g wait).kvAcquires 1 = 0 at hOrdinal
  rw [hOrdinal] at done
  have hFragment : InitialValueFragment X (g,index) steady stage step d op accum mask :=
    hPv.decoded
  obtain ⟨loc,pub,group,j,copy,hPub,hPhase,hMember,_,hCover,_,hLoc,hValue⟩ :=
    done.initialValueOperandWithPublication hp hX hFrame stage step hb hLo hHi
      hr hk hByte hFragment hB hMma hEarlier
  refine ⟨loc,hLoc,hValue ?_⟩
  intro other a bs hWrite hOther
  apply cacheOperandOrderOfCopyOrder hp hX hMma hLoc _ hWrite hOther
  intro r spec hCopy hOverlap
  exact (initialValueCopyCompetitors hp hX hPv hLatest hPub hPhase hMember hLoc hCover
    r spec hCopy hOverlap).elim .inl (.inr ∘ .inr)

end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
