-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Safety.QueryFiniteOperands
public import Kernels.TmlFa4Fwd.Proof.Protocol.ObservedCacheOperandElements
import Kernels.TmlFa4Fwd.Proof.Protocol.CacheOperandWriterOrder
import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderPhaseAlignment
import Kernels.TmlFa4Fwd.Proof.Thread.MmaInitialKeyPrefixReady
import Kernels.TmlFa4Fwd.Proof.Thread.MmaCacheReleaseIssuer
import Kernels.TmlFa4Fwd.Proof.Thread.MmaProbabilityOperand

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX PTX.AsyncCopy PTX.Proof PTX.TcMma
open Mma Thread Protocol.LoaderReady
open Loader (CachePlane kvUseStage)

/-- A completed writer supplies the shared byte, with every competing write ordered
before the source or after the operand read. -/
def SharedOperandSource (l : Launch) (X : Execution) (i : EvId) (isB : Bool)
    (index : Nat) (loc : Loc) : Prop :=
  ∃ src : MmaSources.ByteSource X, src.loc = loc ∧
    ∀ w a bytes, X.MemWrites w a bytes → a.Covers loc →
      w = src.ref ∨ modelCausality l X loc w src.ref ∨
        modelCausality l X loc (.async i (.mmaRead isB index)) w

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

private theorem cacheOperandSourceOfReady (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {wait mma : EvId} {use phase d : Nat}
    {accum : Bool} {mask : List Nat} {op : OperandSpec}
    (hDone : Completed l X wait (kvUseStage use) phase) (block : Fin 4) (step : Fin 8)
    (plane : CachePlane) (hMma : X.MmaIssue mma d op accum mask) (hEarlier : TraceBefore X wait mma)
    (hBytes : ∀ j, op.byteLoc .b j = (cacheOperand l mma.1 block step use plane).byteLoc .b j)
    {index : Nat} {loc : Loc} (hAt : op.byteLoc .b index = some loc)
    (hOrder : ∀ pub (group : Thread.Loader.PublishedCopyGroup l X pub) n spec,
      X.AsyncArrive pub (Thread.Loader.readyObject l mma.1 (kvUseStage use)) true →
      generation l X pub (kvUseStage use) = phase → (n,spec) ∈ group.copies →
      spec.dst.Covers loc →
      ∀ other a data, X.MemWrites other a data → a.Covers loc →
        other = .async (pub.1,n) (.write .copy) ∨
        modelCausality l X loc other (.async (pub.1,n) (.write .copy)) ∨
        modelCausality l X loc (.async mma (.mmaRead true index)) other) :
    SharedOperandSource l X mma true index loc := by
  obtain ⟨row, k, byte, hr, hk, rfl⟩ := cacheOperandFlatByteCoordinates
    ((hBytes index).symm.trans hAt)
  obtain ⟨pub, group, n, spec, data, word, hPub, hPhase, hMember, hWord, hData, hUse⟩ :=
    hDone.actualCacheOperandWord hp hX block step plane hr hk hMma hEarlier
      (fun b => hBytes (qkByteIndex row k b.val))
  obtain rfl := Option.some.inj (hAt.symm.trans (hUse byte).1)
  have hCopy := ((group.member n spec).mp hMember).2.2
  have hShape := actualCopyShape hX hCopy
  have hSource : spec.dst.Covers (spec.dst.loc.at (2 * word + byte.val)) := by
    have := byte.isLt
    simp only [Acc.Covers, Loc.InRange, Loc.at, hShape.widthEq, true_and]
    omega
  have hWrite :=
    (Execution.memWrites_write_copy_of_whole hCopy hShape.whole).mpr ⟨rfl, hData⟩
  rw [hEarlier.1] at hPub
  exact ⟨⟨_, _, _, _, hWrite, hSource⟩, rfl, hOrder pub group n spec hPub hPhase hMember hSource⟩

private theorem initialKeySource (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j d : Nat} {stage : Fin 2} {step : Fin 8} {op : OperandSpec} {accum : Bool} {mask : List Nat}
    (hKey : QkInstruction X (g,j) (initialQkBlock stage) step d op accum mask) {index : Nat}
    {loc : Loc} (hAt : op.byteLoc .b index = some loc) :
    SharedOperandSource l X (g,j) true index loc := by
  have hIssue : X.MmaIssue (g,j) d op accum mask := ⟨_, hKey.decoded⟩
  have hInitial : Thread.Mma.InitialQueryFragment X stage (g,j) :=
    ⟨step, d, op, accum, mask, hKey.decoded⟩
  obtain ⟨wait, hPoll, hEarlier, hOrdinal⟩ := hInitial.keyReadyInPrefix hp hX
  have hWarp := (Thread.mmaIssueElection hp hX hIssue).1
  obtain ⟨done⟩ := completedForObservedIssuer hp hX hWarp
    (Thread.Mma.sameCacheReleaseIssuer hp hX hIssue) hPoll (actualEmptyGuardLower hp hX g 0)
  rw [hOrdinal] at done
  have hB := hKey.initialKeyOperand hp hX stage
  have hQ := hKey.queryOperand hp hX
  have hBytes (n : Nat) :
      op.byteLoc .b n = (cacheOperand l g (initialQkBlock stage) step 0 .key).byteLoc .b n := by
    simp only [OperandSpec.byteLoc, cacheOperand, qkOperands, hQ.descriptor, hQ.ctaLow,
      hQ.ctaHigh, hB, reduceCtorEq, false_and, ↓reduceIte]
    rfl
  apply cacheOperandSourceOfReady hp hX (use := 0) done (initialQkBlock stage) step .key
    hIssue hEarlier hBytes hAt
  intro pub group n spec hPub hPhase hMember hSource other a data hWrite hCover
  apply Protocol.cacheOperandOrderOfCopyOrder hp hX hIssue hAt _ hWrite hCover
  intro rival copy hCopy hOverlap
  exact (initialKeyCopyCompetitors hp hX hInitial hIssue hPub hPhase hMember hAt hSource
    rival copy hCopy hOverlap).elim .inl (.inr ∘ .inr)

private theorem recurringKeySource (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j d : Nat} {stage : Fin 2} {step : Fin 8} {op : OperandSpec} {accum : Bool} {mask : List Nat}
    (hKey : QkInstruction X (g,j) (recurringKeyBlock stage) step d op accum mask) {index : Nat}
    {loc : Loc} (hAt : op.byteLoc .b index = some loc) :
    SharedOperandSource l X (g,j) true index loc := by
  obtain ⟨wait, use, ⟨done⟩, hEarlier, hUse, hBytes⟩ :=
    recurringKeyFragmentReadyBytesExact hp hX stage hKey
  have hIssue : X.MmaIssue (g,j) d op accum mask := ⟨_, hKey.decoded⟩
  apply cacheOperandSourceOfReady hp hX done (recurringKeyBlock stage) step .key
    hIssue hEarlier hBytes hAt
  intro pub group n spec hPub hPhase hMember hSource other a data hWrite hCover
  exact recurringKeyOperandWriterOrder hp hX stage hKey hUse hPub hPhase hMember hAt
    hSource hWrite hCover

private theorem valueOperandSource (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j d : Nat} {block : Fin 4} {step : Fin 8} {op : OperandSpec} {accum : Bool} {mask : List Nat}
    (hValue : PvInstruction X (g,j) block step d op accum mask) {index : Nat} {loc : Loc}
    (hAt : op.byteLoc .b index = some loc) :
    SharedOperandSource l X (g,j) true index loc := by
  obtain ⟨use, wait, hUse, ⟨done⟩, hEarlier, hBytes⟩ := valueOperandReadyInPrefix hp hX hValue
  have hIssue : X.MmaIssue (g,j) d op accum mask := ⟨_, hValue.decoded⟩
  apply cacheOperandSourceOfReady hp hX done block step .value hIssue hEarlier hBytes hAt
  intro pub group n spec hPub hPhase hMember hSource other a data hWrite hCover
  exact valueOperandWriterOrder hp hX hValue hUse hPub hPhase hMember hAt
    hSource hWrite hCover

/-- Every shared byte of an issued MMA is backed when the MMA has yet to read its operands.
K and V come from the completed ready generation, and the query arrives before its first use. -/
theorem pendingSharedOperandSources (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {i : EvId} (hPending : X.async.mmaOperands i = none) {isB : Bool}
    {index : Nat} {loc : Loc} (hAt : X.MmaFootprint i isB index loc) :
    SharedOperandSource l X i isB index loc := by
  rcases hAt with ⟨d, op, accum, mask, hMma, hByte⟩ | ⟨copy, _, _, hCopy, _⟩
  · obtain ⟨g, j⟩ := i
    rcases Thread.actualMmaInstruction hX hMma with ⟨block, step, hKey⟩ | ⟨block, step, hValue⟩
    · cases isB
      · exact pendingQkQuerySource hp hX hFrame hKey hPending hByte
      · have hBlocks : ∀ b : Fin 4, b = initialQkBlock 0 ∨ b = initialQkBlock 1 ∨
            b = recurringKeyBlock 0 ∨ b = recurringKeyBlock 1 := by decide
        rcases hBlocks block with rfl | rfl | rfl | rfl
        · exact initialKeySource hp hX hKey hByte
        · exact initialKeySource hp hX hKey hByte
        · exact recurringKeySource hp hX hKey hByte
        · exact recurringKeySource hp hX hKey hByte
    · obtain rfl := hValue.sharedOperandB hX hByte
      exact valueOperandSource hp hX hValue hByte
  · exact (Thread.noTensorCopyOperandIssue hX hCopy).elim

end PTX.Kernels.TmlFa4Fwd.Safety
