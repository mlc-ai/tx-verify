-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasWordValues
public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasLayout
public import Kernels.TmlFa4Fwd.Proof.InputCopies
import Lemmas.Order.ReadLast
import Lemmas.Async.AsyncMBarrier
import Lemmas.Order.OrderBaseCausality
import Lemmas.Step.CtaBar

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- A backed row contains the stored bias, while an out-of-box row receives BF16 zero. -/
def biasBoxValue (p : Params) (row head col : Nat) : Option ℝ :=
  if row < p.totalQ + 128 then p.bias row head col else some 0

/-- The copy reference for one byte of a Bias word read by the consuming lane. -/
def biasWordWriter (p : Params) (l : Launch) (g : Nat) (i : Fin 16) (word byte : Fin 4)
    (tensor : EvId) : AsyncCopy.Ref :=
  let slot := biasVectorSlot p l g i word byte
  .async tensor (.write (.load slot.1.val slot.2.1.val slot.2.2.val))

/-- Other writes to the same byte lie before the selected TMA write or after the read. -/
def BiasWordOrder (p : Params) (l : Launch) (X : Execution) (stage : Fin 2)
    (repeated : Bool) (i : Fin 16) (word : Fin 4) (g j : Nat) (tensor : EvId) : Prop :=
  ∀ (byte : Fin 4) w a bytes, X.MemWrites w a bytes →
    let loc := (biasReadAcc l g (biasVectorBase l g stage repeated i) repeated i word.val).loc.at
      byte.val
    let writer := biasWordWriter p l g i word byte tensor
    a.Covers loc → w = writer ∨ modelCausality l X loc w writer ∨
      modelCausality l X loc (.thread (g, j)) w

/-- After selecting the ordered TMA writer, the bytes in the actual shared read rebuild to
the two original BF16 elements, including a mask and descriptor padding. -/
theorem biasReadWordOfBox {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (writes : ∀ w a bytes loc, X.MemWrites w a bytes → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (stage : Fin 2) (repeated : Bool) (i : Fin 16) (word : Fin 4)
    {g j col row head : Nat} (hc : col + 64 ≤ 1280) (hh : head < p.heads)
    {tensor : EvId} {o : TensorCopy.Observation} (hObserve : X.tensor tensor = some o)
    {barrier : Loc} {clusterAddress : Bool}
    (hSpec : o.spec = biasInputSpec p col row head
      ⟨.shared, g / l.block, biasBoxStart l stage (i.val / 8)⟩ barrier clusterAddress)
    {bs : List (Option Byte)}
    (hRead : X.get (g, j) = some ⟨biasReadPc repeated i,
      .rd (biasReadAcc l g (biasVectorBase l g stage repeated i) repeated i word.val) bs⟩)
    {wait : Nat} (hEarlier : wait < j)
    (hCta : tensor.1 / l.block = g / l.block)
    (hObserved : AsyncCopy.AsyncObserved X tensor (.notify .load) (g, wait) true .cta)
    (hOrder : BiasWordOrder p l X stage repeated i word g j tensor) :
    let absRow := row + (g % l.block) % 128
    let lowCol := col + (8 * (i.val % 8) + 2 * word.val)
    rebuild 3 bs =
      .ok (biasLoadWord (biasBoxValue p absRow head lowCol)
        (biasBoxValue p absRow head (lowCol + 1))) := by
  obtain ⟨observed, address, hObservedSpec, hIssue, hNotify, hWait⟩ := hObserved.tensor
  have hSame := Option.some.inj (hObserve.symm.trans hObservedSpec)
  subst observed
  obtain ⟨pc, parity, hPoll⟩ := hWait.1
  obtain ⟨_, hTensorEvent⟩ := hIssue
  have hCtaScope : SameCta l tensor.1 g := ⟨Step.CtaBar.thread_lt_of_get hX hTensorEvent,
    Step.CtaBar.thread_lt_of_get hX hRead, hCta⟩
  have hAfter : baseCausality l X (g, wait) (g, j) := by
    have hLen := (List.getElem?_eq_some_iff.mp hRead).1
    refine .single (.inl ⟨rfl, hEarlier, hLen, ?_⟩)
    intro hAccess
    have hLast := hAccess.2 (j - wait) le_rfl
    rw [Nat.add_sub_of_le hEarlier.le, hRead, hPoll] at hLast
    cases hLast
  rcases o with ⟨spec, effects⟩
  dsimp only at hSpec
  subst spec
  let readAcc := biasReadAcc l g (biasVectorBase l g stage repeated i) repeated i word.val
  let readId := AsyncCopy.Ref.thread (g, j)
  have hReads : X.MemReads readId readAcc bs := .inl ⟨_, hRead⟩
  have hLength : bs.length = 4 := (hX.rf readId readAcc bs hReads).1
  have hCopy (byte : Fin 4) :
      bs[byte.val]? = some (some ((biasValue
        (biasBoxValue p (row + (g % l.block) % 128) head
          (col + (8 * (i.val % 8) + 2 * word.val + byte.val / 2)))).byteAt (byte.val % 2))) := by
    let slot := biasVectorSlot p l g i word byte
    have hSlot : col + slot.1.val < 1280 := by
      have hByte := byte.isLt
      have hWord := word.isLt
      change col + (8 * (i.val % 8) + 2 * word.val + byte.val / 2) < 1280
      omega
    have hWritten := biasInputSlotWritten hp hX writes hObserve hNotify rfl slot hSlot hh
    have hLoc : readAcc.loc.at byte.val =
        (biasInputSpec p col row head
          ⟨.shared, g / l.block, biasBoxStart l stage (i.val / 8)⟩ barrier clusterAddress).sharedLoc
          slot :=
      biasVectorMatchesBox p l g stage repeated i word byte (inputCoordinate col row head)
    let copySpec := biasInputSpec p col row head
      ⟨.shared, g / l.block, biasBoxStart l stage (i.val / 8)⟩ barrier clusterAddress
    let target : Acc := {loc := copySpec.sharedLoc slot, size := 1}
    have hCov : target.Covers (readAcc.loc.at byte.val) := by
      rw [hLoc]
      simpa only [Loc.at, Nat.add_zero] using
        (Acc.covers_at (a := target) (k := 0) (by change 0 < 1; decide))
    have hBefore : modelCausality l X (readAcc.loc.at byte.val)
        (biasWordWriter p l g i word byte tensor) readId := by
      refine ⟨⟨target, true, hWritten.intent, hCov⟩, (g, wait), .inr ⟨.cta, ?_, ?_⟩, .inl hAfter⟩
      · simpa only [AsyncCopy.AsyncObserved, AsyncCopy.Notifies, AsyncCopy.Part.target]
          using hObserved
      · exact ScopesMeet.of_sameCta hCtaScope
    have hReadByte := read_byte_of_last_write hX hReads
      (show byte.val < readAcc.size from byte.isLt) hWritten hCov hBefore (hOrder byte)
    rw [hLoc] at hReadByte
    by_cases hRow : row + (g % l.block) % 128 < p.totalQ + 128 <;>
      simpa [wbyte, biasBoxValue, slot, biasVectorSlot, hRow, biasValue] using hReadByte
  let absRow := row + (g % l.block) % 128
  let lowCol := col + (8 * (i.val % 8) + 2 * word.val)
  let lo := biasBoxValue p absRow head lowCol
  let hi := biasBoxValue p absRow head (lowCol + 1)
  have bytes (x : Option ℝ) :
      (biasValue x).toBytes = [(biasValue x).byteAt 0, (biasValue x).byteAt 1] := by
    cases x <;> rfl
  have hBytes : bs = ((biasValue lo).toBytes ++ (biasValue hi).toBytes).map some := by
    rw [bytes lo, bytes hi]
    apply List.ext_getElem?
    intro k
    by_cases hk : k < 4
    · interval_cases k
      · exact hCopy 0
      · exact hCopy 1
      · exact hCopy 2
      · exact hCopy 3
    · rw [List.getElem?_eq_none (by omega : bs.length ≤ k)]
      exact (List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hk)).symm
  rw [hBytes]
  exact rebuildBiasLoadWord lo hi

end
end PTX.Kernels.TmlFa4Fwd.Softmax
