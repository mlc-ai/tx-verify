-- SPDX-License-Identifier: Apache-2.0
-- iface: QueryTile producer=W status=proved domain=consistent
module

public import Kernels.InklingRelDecode.Proof.Iface.Regions

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Iface
open PTX

/-- A query-store word: two bf16 numbers, or the 32-bit zero of two masked loads. -/
def QueryWord (bs : List Byte) : Prop :=
  (∃ x y : ℝ, ∀ z < 2, bs[z]? = some ((Value.float .bf16 x).byteAt z) ∧
    bs[2 + z]? = some ((Value.float .bf16 y).byteAt z)) ∨
  ∀ q < 4, bs[q]? = some (Value.bits 32 (BitVec.ofNat 64 0), q)

/-- **The query tile as the Prologue stores it**: every query store (pcs `526 + 6 i`) writes a
`QueryWord`, no location is stored twice, and every byte of the query tile of an MMA's CTA is
covered by a query store. -/
structure QueryTile (L : Launch) (X : Execution) : Prop where
  word : ∀ {g k a bs} {i : Fin 8}, X.get (g, k) = some ⟨526 + 6 * i.val, .wr a bs⟩ → QueryWord bs
  once : ∀ {g k g' k' a a' bs bs'} {i i' : Fin 8},
    X.get (g, k) = some ⟨526 + 6 * i.val, .wr a bs⟩ →
    X.get (g', k') = some ⟨526 + 6 * i'.val, .wr a' bs'⟩ → a.loc = a'.loc → g = g' ∧ k = k'
  covered : ∀ {h f pc dst s acc mask l}, X.get (h, f) = some ⟨pc, .tc (.mma dst s acc mask)⟩ →
    InQ L l → l.cta = h / L.block →
    ∃ g k a bs, ∃ i : Fin 8, X.get (g, k) = some ⟨526 + 6 * i.val, .wr a bs⟩ ∧ a.Covers l

end PTX.Kernels.InklingRelDecode.Proof.Iface
