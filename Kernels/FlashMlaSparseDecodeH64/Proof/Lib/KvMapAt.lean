-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.TensorIn

@[expose] public section

/-! # The cache map a gather names

`KvMapAt P x y`: the map `y` is the main cache's when the gather's parameter slot is `+ 768`
and the extra cache's (which is on) when it is `+ 896`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX TensorDescriptor

/-- **The cache map of parameter slot `x`**. -/
def KvMapAt (P : Params) (x : Nat) (y : Σ n, Descriptor n) : Prop :=
  (x = 768 ∧ y = ⟨1, mapKv P.kvBase P.numBlocks P.blockStride P.kvClass⟩) ∨
    (x = 896 ∧ P.extra_topk ≠ 0 ∧
      y = ⟨1, mapExtraKv P.extraKvBase P.extraNumBlocks P.extraBlockStride P.extraKvClass⟩)

theorem KvMapAt.kvMap {P : Params} {x : Nat} {y : Σ n, Descriptor n} (h : KvMapAt P x y) :
    KvMap P y := by
  rcases h with ⟨-, h⟩ | ⟨-, h1, h2⟩
  · exact .inl h
  · exact .inr ⟨h1, h2⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
