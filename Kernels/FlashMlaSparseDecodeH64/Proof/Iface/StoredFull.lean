-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.GatherVocab

@[expose] public section

/-! # The stored coordinate word, with its converse

`StoredWord` says the word an index lane stores for a position is `-1` or the row of the selected
slot. `StoredWordFull` adds the converse: a selected slot's word is its row (not the zero fill
`-1`), which the value link of the scores needs. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

noncomputable section

/-- **A stored coordinate word, exactly**: `StoredWord`, and the word of a selected slot is its
physical row. -/
def StoredWordFull (P : Params) (e q : Nat) (extra : Bool) (pos : Nat) (z : BitVec 64) : Prop :=
  StoredWord P e q extra pos z ∧
    (slotValid P e q extra pos → wordInt (.bits 32 z) = (slotRow P e q extra pos : Int))

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
