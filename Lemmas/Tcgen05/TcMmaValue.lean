-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Tc.TcMmaValue

@[expose] public section

namespace PTX.TcMma
noncomputable section

/-- Every derived value belongs to an actual unmasked write footprint. -/
theorem Result.footprint {L : Launch} {A : List Assumption} {X : Execution}
    {i : EvId} {cell : Cell} {v : Value} (h : Result L A X i cell v) :
    X.MmaCell i cell := by
  cases h with
  | overwrite issue position _ _ => exact ⟨_, _, _, _, _, _, issue, position⟩
  | accumulate issue position _ _ _ _ => exact ⟨_, _, _, _, _, _, issue, position⟩
  | accumulateStored issue position _ _ _ _ => exact ⟨_, _, _, _, _, _, issue, position⟩

/-- An actual initial write of the cell: an overwriting MMA or a store. -/
def Initializer (L : Launch) (X : Execution) (first : EvId) (cell : Cell) : Prop :=
  (∃ d s mask, X.MmaIssue first d s false mask ∧ X.MmaCell first cell) ∨
    ∃ v, StoreValue L X first cell v

/-- Finite accumulation derivations start at an actual initializing write; a cycle of
accumulation-only issues cannot conjure an initial accumulator. -/
theorem Result.has_initializer {L : Launch} {A : List Assumption} {X : Execution}
    {i : EvId} {cell : Cell} {v : Value} (h : Result L A X i cell v) :
    ∃ first, Initializer L X first cell := by
  induction h with
  | overwrite issue position _ _ =>
      exact ⟨_, .inl ⟨_, _, _, issue, _, _, _, _, _, _, issue, position⟩⟩
  | accumulate _ _ _ _ _ _ ih => exact ih
  | accumulateStored _ _ _ previous _ _ => exact ⟨_, .inr ⟨_, previous⟩⟩

/-- Without a numerical profile only exact integer MMAs have results. -/
theorem result_no_profile {L : Launch} {X : Execution} {i : EvId} {cell : Cell} {v : Value}
    (h : Result L [] X i cell v) :
    ∃ d s accum mask sa sb sat, X.MmaIssue i d s accum mask ∧
      s.descriptor.kind = .i8 sa sb sat := by
  have key : ∀ {d : Descriptor} {accum a b old row col},
      eval [] d accum a b old row col = .ok v → ∃ sa sb sat, d.kind = .i8 sa sb sat := by
    intro d accum a b old row col he
    unfold eval at he
    split at he
    · exact ⟨_, _, _, by assumption⟩
    all_goals cases he
  cases h with
  | overwrite issue _ _ ha =>
    exact ⟨_, _, _, _, _, _, _, issue, (key ha).choose_spec.choose_spec.choose_spec⟩
  | accumulate issue _ _ _ _ ha =>
    exact ⟨_, _, _, _, _, _, _, issue, (key ha).choose_spec.choose_spec.choose_spec⟩
  | accumulateStored issue _ _ _ _ ha =>
    exact ⟨_, _, _, _, _, _, _, issue, (key ha).choose_spec.choose_spec.choose_spec⟩

/-- A competing writer that is neither before the source nor after the consumer
prevents selection of that source for an accumulator read (it fails the stability conjunct of
`ReadSource .acc`). -/
theorem not_readSource_acc_of_interference {L : Launch} {X : Execution}
    {source consumer other : EvId} {cell : Cell}
    (hw : TmemWrite L X other cell) (hs : other ≠ source) (hc : other ≠ consumer)
    (hb : ¬ WriteBefore L X other source) (ha : ¬ Before L X consumer other) :
    ¬ ReadSource L X .acc source consumer cell := by
  rw [readSource_acc]
  rintro ⟨-, -, -, hstable, -⟩
  rcases hstable other hw with h | h | h | h
  · exact hs h
  · exact hc h
  · exact hb h
  · exact ha h

end
end PTX.TcMma
