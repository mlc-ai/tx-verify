-- SPDX-License-Identifier: Apache-2.0
-- iface: RescaleStep producer=W1 status=proved domain=consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Spec
public import Lemmas.Flow.Mul2NVal
public import Lemmas.Tcgen05.TmemWriters

@[expose] public section

/-! # A rescale store's words are the loaded words times the factor

The statement the Tensor Memory chain of the MMA lane needs from warpgroup 0 (`RescaleStep`): a
word a store of the warpgroup wrote to a cell is a number (a clean four-byte word that reads as
an `f32`) whenever every register of an earlier load of the same lane read such a word. The loaded
chunk is the accumulator's earlier MMA result (`Protocol/Values/MmaResults.lean`); the factor is
warpgroup 0's (`W0Valid`, `Iface/W0Value.lean`), a number on a valid trace. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

noncomputable section

/-- **A rescale store's word is a number when the words its lane loaded before are**: for every
word a store of the lane wrote to a cell there is a load of the same lane before the store such
that, if each register of the load read a number, the word is a number. -/
def RescaleStepAt (L : Launch) (X : Execution) (st : EvId) : Prop :=
  ∀ (cell : TcMma.Cell) (old : Value), TcMma.StoreValue L X st cell old →
    ∃ (e : EvId) (a : Nat) (vals : List Value) (sh : TcShape), X.TLd e a vals sh ∧
      e.1 = st.1 ∧ e.2 < st.2 ∧
      ((∀ v ∈ vals, ∃ r : ℝ, OkF v r) → ∃ r : ℝ, OkF old r)

/-- The rescale-step fact at every event. -/
def RescaleStep (L : Launch) (X : Execution) : Prop := ∀ st, RescaleStepAt L X st

/-- A four-byte float word is a number. -/
theorem okF_float (r : ℝ) : OkF (.float .f32 r) r :=
  ⟨⟨rfl, fun _ _ _ h => (by cases h), fun _ _ h => (by cases h)⟩, rfl⟩

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
