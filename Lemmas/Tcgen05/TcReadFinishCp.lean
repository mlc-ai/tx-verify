-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.MmaFinish
public import Core.Tc.TcMmaRead

public section

/-! # Tensor Memory read preservation when a copy captures and finishes -/

namespace PTX.TcMma
open AsyncCopy

variable {L : Launch} {A : List Assumption} {X : Execution} {i : EvId} {values : MmaOperands}
variable {ra rb : Nat → Option Ref}

local notation "Y" => X.finishMma i values ra rb

private theorem no_mma_of_cp {j : EvId} {c : TcCopy.Spec} {dst : Nat} {s : OperandSpec}
    {acc : Bool} {mask : List Nat} (hc : X.CpIssue j c) (hm : X.MmaIssue j dst s acc mask) :
    False := by
  have h := congrArg Event.kind (Option.some.inj (hc.choose_spec.symm.trans hm.choose_spec))
  cases h

private theorem old_result {c : TcCopy.Spec} (hi : X.CpIssue i c) {e : EvId} {cell : Cell}
    {v : Value} (h : Result L A Y e cell v) : Result L A X e cell v := by
  have old {j dst sp accum mask ops} (hj : X.MmaIssue j dst sp accum mask)
      (hop : (Y).async.mmaOperands j = some ops) : X.async.mmaOperands j = some ops := by
    have hne : j ≠ i := by
      rintro rfl
      exact no_mma_of_cp hi hj
    simpa only [Execution.finishMma, ite_eq_right hne] using hop
  induction h with
  | overwrite issue position ops arithmetic =>
    exact .overwrite issue position (old issue ops) arithmetic
  | accumulate issue position ops _ source arithmetic ih =>
    exact .accumulate issue position (old issue ops) ih source arithmetic
  | accumulateStored issue position ops stored source arithmetic =>
    exact .accumulateStored issue position (old issue ops) stored source arithmetic

private theorem old_copy_value {j : EvId} {cell : Cell} {v : Value} (hNe : j ≠ i)
    (h : CpValue Y j cell v) : CpValue X j cell v := by
  obtain ⟨sp, k, cta, operands, row, col, lane, hIssue, hCta, hOps, hRow, hCol, hLane, hCell,
    hValue⟩ := h
  exact ⟨sp, k, cta, operands, row, col, lane, hIssue, hCta,
    by simpa only [Execution.finishMma, ite_eq_right hNe] using hOps,
    hRow, hCol, hLane, hCell, hValue⟩

private theorem old_wrote {c : TcCopy.Spec} (hi : X.CpIssue i c)
    (hShift : ∀ e sp, ¬ X.ShiftIssue e sp) {e : EvId} {cell : Cell} {v : Value}
    (hNe : e ≠ i) (hw : Wrote L A Y e cell v) : Wrote L A X e cell v := by
  rcases hw with h | h | h | ⟨_, _, ⟨⟨s, hs, _⟩, _⟩, _⟩
  · exact .inl (old_result hi h)
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl (old_copy_value hNe h)))
  · exact (hShift e s hs).elim

/-- Finishing a copy preserves the values of existing readers if no reader can source that
copy and the trace has no Tensor Memory shifts. -/
theorem ReadOk.finishCp (hRead : ReadOk L A X) {c : TcCopy.Spec} (hi : X.CpIssue i c)
    (hShift : ∀ e sp, ¬ X.ShiftIssue e sp)
    (hNoLoad : ∀ e addr vals shape, X.TLd e addr vals shape →
      ∀ cell, ¬ ReadSource L X .ld i e cell)
    (hNoA : ∀ e dst sp accum mask, X.MmaIssue e dst sp accum mask →
      ∀ cell, ¬ ReadSource L X .a i e cell) : ReadOk L A Y := by
  constructor
  · intro e addr vals shape j source cell v hLoad hCell hSource hVal
    have hNe : source ≠ i := by
      rintro rfl
      exact hNoLoad e addr vals shape hLoad cell hSource
    exact hRead.1 e addr vals shape j source cell v hLoad hCell hSource
      (old_wrote hi hShift hNe hVal)
  · intro e j cell pos source v ops ha hSource hVal hOp hPos
    obtain ⟨dst, sp, accum, mask, hm, hCell⟩ := ha
    have hNeSource : source ≠ i := by
      rintro rfl
      exact hNoA e dst sp accum mask hm cell hSource
    have hNeMma : e ≠ i := by
      rintro rfl
      exact no_mma_of_cp hi hm
    have hOldOp : X.async.mmaOperands e = some ops := by
      simpa only [Execution.finishMma, ite_eq_right hNeMma] using hOp
    exact hRead.2 e j cell pos source v ops ⟨dst, sp, accum, mask, hm, hCell⟩ hSource
      (old_wrote hi hShift hNeSource hVal) hOldOp hPos

end PTX.TcMma
