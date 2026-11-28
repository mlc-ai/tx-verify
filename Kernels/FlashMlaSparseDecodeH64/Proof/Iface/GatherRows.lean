-- SPDX-License-Identifier: Apache-2.0
-- iface: GatherRowsGood producer=A status=proved domain=consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Spec
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Tma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.GatherVocab

@[expose] public section

/-! # The coordinate words of a gather

The TMA lane's gather4 loads take five coordinate words from registers it filled from the
coordinate ring (`Protocol/Shared/TmaCoord.lean`): the column origin and the four row words
(`TensorCopy.Spec.origin 0`, `TensorCopy.Spec.rows`). Which token a row word names is the
value link of the index lane's stores (the position's index word, the page arithmetic) to the
ring and to these registers, which no data machine of the tree proves yet.

`GatherRowsGood` is the exact statement of that link as the dequantizer's valid data needs it:
every gather has the column origin `0` and, for each of its four rows, either the word `-1`
(the zero fill) or the physical row of a selected slot of the cache the gather's map is. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX

noncomputable section

/-- **A good row word** of a gather `s`: `-1`, or the physical row of a selected slot of the
cache that is `s`'s map. -/
def GoodRow (P : Params) (s : TensorCopy.Spec) (y : Int) : Prop :=
  y = -1 ∨ ∃ e < P.b, ∃ q < P.s_q, ∃ extra j, slotValid P e q extra j ∧
    (⟨s.outer, s.descriptor⟩ : Σ n, TensorDescriptor.Descriptor n) = gatherMap P extra ∧
    y = (slotRow P e q extra j : Int)

/-- **The coordinate words of the gathers** (the leaf `noUb.dequant` is narrowed to): every
gather of a TMA lane has origin column `0` and four good row words. -/
def GatherRowsGood (P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k pc a : Nat} {s : TensorCopy.Spec}, X.get (g, k) = some ⟨pc, .tensorIssue a s⟩ →
    MbarRow.TmaAt L g pc → s.origin 0 = 0 ∧
      ∃ ys : Fin 4 → Int, s.rows = some ys ∧ ∀ i, GoodRow P s (ys i)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
