-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow

@[expose] public section

/-! # The named barriers' participant warps

`barIn id w`: warp `w` of a CTA takes part in named barrier `id`: warpgroup 0's warps 0–3 in
`wg0_sync` (barrier 9), the warp pairs `{0, 2}` and `{1, 3}` in barriers 10 and 11, every warp
of the CTA (warps 0–11) in the startup's barrier 0 and in `everyone_sync` (barrier 12).
`barWarps id` is the set of them. The groups are proved from the barrier rows in
`Protocol/Bar/Group.lean`; the progress at a `bar.sync` takes them as a hypothesis. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof

/-- **Warp `w` takes part in named barrier `id`.** -/
def barIn (id w : Nat) : Bool :=
  if id = 9 then decide (w < 4)
  else if id = 10 ∨ id = 11 then decide (w < 4 ∧ w % 2 = id - 10)
  else decide (w < 12)

/-- The participant warps of named barrier `id`. -/
def barWarps (id : Nat) : Finset Nat := (Finset.range 12).filter fun w => barIn id w = true

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
