-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Index.Cnt

@[expose] public section

/-! # The index warp's stores per block

A block of either loop stores the lane's coordinate pair (two stores, `stA`/`stB`) and, on lanes
`0 mod 4`, the validity byte (`bA`/`bB`). `StEq`: the class `st` of the counts is `(2 + sgB) i`
for the `i` finished blocks, plus the stores `stDone` of the state's own block; `sgB` is `1` on
the lanes that store the byte. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

/-- The validity byte's stores of the lane in a block: one on lanes `0 mod 4`. -/
def sgB (L : Launch) (g : Nat) : Nat := if ixSkipB L g then 0 else 1

/-- The stores of the state's own block made before the state. -/
def stDone (L : Launch) (g : Nat) : IxSite → Nat → Nat
  | .stA, el | .stB, el => el
  | .bA, _ | .bB, _ => 2
  | .arrA, _ | .arrB, _ => 2 + sgB L g
  | _, _ => 0

/-- **The stores of the state**: `i` finished blocks and the state's own, with the element
below the site's and the byte sites only on the lanes that store the byte. -/
def StEq (L : Launch) (g : Nat) (d : D) (n : Cnt → Nat) (i : Nat) : Prop :=
  n .st = (2 + sgB L g) * i + stDone L g d.site d.el ∧ d.el < d.site.elems ∧
    ((d.site = .bA ∨ d.site = .bB) → ixSkipB L g = false)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Index
