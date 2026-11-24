-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.RecurringValueOrder
public import Kernels.TmlFa4Fwd.Proof.Protocol.RecurringKeyReadyWords
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPendingDestination
import Kernels.TmlFa4Fwd.Proof.LoaderCopyFootprint

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.Proof PTX.AsyncCopy PTX.TcMma Thread
open PTX.Kernels.TmlFa4Fwd.Mma
open PTX.Kernels.TmlFa4Fwd.Loader (kvUseStage kvCopyVectorsApart)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

private theorem pendingSlotOfCacheOperandByte (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g producer index use : Nat} {e : Event}
    (he : X.get (producer,index) = some e) (hVector : Thread.Loader.recurringVectorEvent e)
    {spec : Spec} (hKind : e.kind = .copy spec) (block : Fin 4) (step : Fin 8)
    (plane : Loader.CachePlane) {row k : Nat} (hr : row < 128) (hk : k < 16) (b : Fin 2) {loc : Loc}
    (hLoc : (cacheOperand l g block step use plane).byteLoc .b (qkByteIndex row k b) = some loc)
    (hCover : spec.dst.Covers loc) :
    kvUseStage (Thread.Loader.recurringUseBefore X (producer,index)) = kvUseStage use := by
  let next := Thread.Loader.recurringUseBefore X (producer,index)
  obtain ⟨pair, upper, hDst⟩ := Thread.Loader.pendingRecurringVectorDestination hp hX he hVector
    hKind
  obtain ⟨lane, otherPair, otherUpper, word, hWord, hByte⟩ :=
    cacheOperandWordVector hp g block step use plane hr hk
  rw [hByte b] at hLoc
  obtain rfl := Option.some.inj hLoc
  rw [hDst] at hCover
  obtain ⟨_, _, hLo, hHi⟩ := hCover
  change kvCopyAddress l.sharedBase (kvUseStage next) (producer%l.block) pair upper ≤
    kvCopyAddress l.sharedBase (kvUseStage use) lane otherPair otherUpper + (2*word+b.val) at hLo
  change kvCopyAddress l.sharedBase (kvUseStage use) lane otherPair otherUpper + (2*word+b.val) <
    kvCopyAddress l.sharedBase (kvUseStage next) (producer%l.block) pair upper + 16 at hHi
  apply Fin.ext
  by_contra hDifferent
  change (kvUseStage next).val ≠ (kvUseStage use).val at hDifferent
  have hApart := kvCopyVectorsApart (a := producer%l.block) (b := lane) (u := upper)
    (v := otherUpper) hp.shared.1 pair.isLt otherPair.isLt (Or.inl hDifferent)
  have hBit := b.isLt
  rcases hApart with h | h <;> omega

/-- A recurring K operand byte is read before any covering later cache copy.
The copy may belong to a packet that has not committed. -/
theorem recurringKeyBeforeLaterCoveringCopy (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2) {g index : Nat} {step : Fin 8}
    {d : Nat} {op : OperandSpec} {accum : Bool} {mask : List Nat}
    (hKey : QkInstruction X (g,index) (recurringKeyBlock stage) step d op accum mask)
    {producer copyIndex : Nat} {event : Event} (he : X.get (producer,copyIndex) = some event)
    (hVector : Thread.Loader.recurringVectorEvent event) {use row k : Nat} {loc : Loc} {copy : Spec}
    (hKind : event.kind = .copy copy)
    (hUse : use = (Thread.Mma.atPrefix l X g index).kvAcquires 0 +
      (Thread.Mma.atPrefix l X g index).kvAcquires 1 +
      (Thread.Mma.atPrefix l X g index).kvAcquires 2 - 1) (hr : row < 128) (hk : k < 16) (b : Fin 2)
    (hOperand : op.byteLoc .b (qkByteIndex row k b) = some loc) (hCover : copy.dst.Covers loc)
    (hLater : use < Thread.Loader.recurringUseBefore X (producer,copyIndex)) :
    X.AsyncPresent (g,index) (.mmaRead true (qkByteIndex row k b)) ∧
      modelCausality l X loc (.async (g,index) (.mmaRead true (qkByteIndex row k b)))
        (.async (producer,copyIndex) (.write .copy)) := by
  obtain ⟨_, actual, _, _, hActual, hBytes⟩ := recurringKeyFragmentReadyBytesExact hp hX stage hKey
  obtain rfl : use = actual := hUse.trans hActual.symm
  have hSlot := pendingSlotOfCacheOperandByte hp hX he hVector hKind
    (recurringKeyBlock stage) step .key hr hk b ((hBytes _).symm.trans hOperand) hCover
  exact recurringKeyBeforePendingCopy hp hX stage hKey he hVector hKind hActual hOperand hCover
    hSlot hLater

/-- A V operand byte is read before any covering later cache copy, including
an issued vector whose publication is still open. -/
theorem valueBeforeLaterCoveringCopy (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {block : Fin 4} {step : Fin 8} {d : Nat} {op : OperandSpec} {accum : Bool}
    {mask : List Nat} (hValue : PvInstruction X (g,index) block step d op accum mask)
    {producer copyIndex : Nat} {event : Event} (he : X.get (producer,copyIndex) = some event)
    (hVector : Thread.Loader.recurringVectorEvent event) {use row k : Nat} {loc : Loc} {copy : Spec}
    (hKind : event.kind = .copy copy) (hUse : Thread.Mma.LatestValueReadyUse l X g index use)
    (hr : row < 128) (hk : k < 16) (b : Fin 2)
    (hOperand : op.byteLoc .b (qkByteIndex row k b) = some loc) (hCover : copy.dst.Covers loc)
    (hLater : use < Thread.Loader.recurringUseBefore X (producer,copyIndex)) :
    X.AsyncPresent (g,index) (.mmaRead true (qkByteIndex row k b)) ∧
      modelCausality l X loc (.async (g,index) (.mmaRead true (qkByteIndex row k b)))
        (.async (producer,copyIndex) (.write .copy)) := by
  obtain ⟨actual, hActual, hB, hShape⟩ := Thread.Mma.valueFragmentUse hp hX hValue
  obtain rfl := hUse.unique hActual
  obtain ⟨hDesc, hLow, hHigh⟩ := hShape
  have hByte : (cacheOperand l g block step use .value).byteLoc .b (qkByteIndex row k b) =
      some loc := by
    rw [← hOperand]
    simp only [OperandSpec.byteLoc, cacheOperand, pvOperands, hB, hDesc, hLow, hHigh,
      reduceCtorEq, false_and, ↓reduceIte]
    rfl
  have hSlot := pendingSlotOfCacheOperandByte hp hX he hVector hKind block step .value
    hr hk b hByte hCover
  exact valueBeforePendingCacheCopy hp hX hValue he hVector hKind hActual hOperand hCover
    hSlot hLater

/-- A present K/V operand address identifies an in-range BF16 row, contraction
element, and byte. This also applies to byte indices supplied by a footprint. -/
theorem cacheOperandFlatByteCoordinates {l : Launch} {g use index : Nat} {block : Fin 4}
    {step : Fin 8} {plane : Loader.CachePlane} {loc : Loc}
    (hLoc : (cacheOperand l g block step use plane).byteLoc .b index = some loc) :
    ∃ (row k : Nat) (b : Fin 2), row < 128 ∧ k < 16 ∧ index = qkByteIndex row k b := by
  let op := cacheOperand l g block step use plane
  have hKind : op.descriptor.kind.k * op.descriptor.kind.width = 32 := by cases plane <;> rfl
  have hExtent : Operand.extent .b op.descriptor = 128 := by cases plane <;> rfl
  change op.byteLoc .b index = some loc at hLoc
  have hRow : index / 32 < 128 := by
    unfold OperandSpec.byteLoc at hLoc
    simp only [hKind, reduceCtorEq, false_and, ↓reduceIte, hExtent] at hLoc
    split at hLoc
    · contradiction
    · rename_i hValid
      push Not at hValid
      exact hValid.2
  refine ⟨index / 32, (index % 32) / 2, ⟨index % 2, Nat.mod_lt _ (by decide)⟩,
    hRow, by omega, ?_⟩
  change index = 32 * (index / 32) + 2 * ((index % 32) / 2) + index % 2
  omega

/-- A later covering vector follows a V operand read at any flat byte index. -/
theorem valueReadBeforeFutureCoveringVector (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g index : Nat} {block : Fin 4} {step : Fin 8}
    {d : Nat} {op : OperandSpec} {accum : Bool} {mask : List Nat}
    (hValue : PvInstruction X (g,index) block step d op accum mask) {use byte : Nat}
    (hUse : Thread.Mma.LatestValueReadyUse l X g index use) {loc : Loc}
    (hByte : op.byteLoc .b byte = some loc) {other : EvId} {copy : Spec} {event : Event}
    (he : X.get other = some event) (hVector : Thread.Loader.recurringVectorEvent event)
    (hKind : event.kind = .copy copy) (hCover : copy.dst.Covers loc)
    (hLater : use < Thread.Loader.recurringUseBefore X other) :
    modelCausality l X loc (.async (g,index) (.mmaRead true byte))
      (.async other (.write .copy)) := by
  obtain ⟨actual,hActual,hB,hShape⟩ := Thread.Mma.valueFragmentUse hp hX hValue
  obtain rfl := hUse.unique hActual
  obtain ⟨hDesc,hLow,hHigh⟩ := hShape
  have hLoc : (cacheOperand l g block step use .value).byteLoc .b byte = some loc := by
    rw [← hByte]
    simp only [OperandSpec.byteLoc, cacheOperand, pvOperands, hB, hDesc, hLow, hHigh,
      reduceCtorEq, false_and, ↓reduceIte]
    rfl
  obtain ⟨row,k,b,hr,hk,rfl⟩ := cacheOperandFlatByteCoordinates hLoc
  obtain ⟨producer,copyIndex⟩ := other
  exact (valueBeforeLaterCoveringCopy hp hX hValue he hVector hKind hActual hr hk b
    hByte hCover hLater).2

end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
