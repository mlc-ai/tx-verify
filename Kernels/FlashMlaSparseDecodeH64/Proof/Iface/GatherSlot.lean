-- SPDX-License-Identifier: Apache-2.0
-- iface: GatherSlot producer=N status=proved domain=consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.GatherRows
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Reads
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Launch

@[expose] public section

/-! # The slot a gather row names

`GatherRowsGood` says a row word of a gather is `-1` or the row of SOME selected slot. `GatherSlot`
says which: the gather `q` of block `r` (the TMA lane's `64 r + ...` coordinate reads before it)
takes row `i` from the slot at position `4 q + i` of block `r` (`w0BlockSlot`) of the cache the
block has (`w0BlockExtra`), or is the zero fill `-1` (exactly when the slot is not selected). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

noncomputable section

/-- **A row word of a block's slot**: `-1`, or the physical row of the slot, which is selected;
and the word of a selected slot is its row. -/
def SlotRowWord (P : Params) (e q : Nat) (extra : Bool) (pos : Nat) (y : Int) : Prop :=
  (y = -1 ∨ (slotValid P e q extra pos ∧ y = (slotRow P e q extra pos : Int))) ∧
    (slotValid P e q extra pos → y = (slotRow P e q extra pos : Int))

/-- **The slot of every gather row**: gather `q` of block `r` has column origin `0`, the map of the
block's cache, and four row words, row `i` of which is `-1` or the row of the selected slot at
position `4 q + i` of the block. -/
def GatherSlot (P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k pc a : Nat} {s : TensorCopy.Spec}, X.get (g, k) = some ⟨pc, .tensorIssue a s⟩ →
    MbarRow.TmaAt L g pc → ∃ q < 16, ∃ r, pc = gatherPc q ∧
      ((X.tr g).take k).countP tmaRd = 64 * r + (if q = 15 then 64 else 4 * q + 8) ∧
      s.origin 0 = 0 ∧
      (⟨s.outer, s.descriptor⟩ : Σ n, TensorDescriptor.Descriptor n) =
        gatherMap P (w0BlockExtra P (ctaidY L g) r) ∧
      ∃ ys : Fin 4 → Int, s.rows = some ys ∧ ∀ i : Fin 4,
        SlotRowWord P (ctaidY L g) (ctaidX L g) (w0BlockExtra P (ctaidY L g) r)
          (w0BlockSlot P (ctaidY L g) r (4 * q + i.val)) (ys i)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
