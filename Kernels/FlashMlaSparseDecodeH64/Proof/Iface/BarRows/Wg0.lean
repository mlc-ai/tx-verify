-- SPDX-License-Identifier: Apache-2.0
-- iface: BarRow.Wg0 producer=W1 status=row-proved domain=consistent ahead=1
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.BarRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Wg0

@[expose] public section

/-! # Warpgroup 0: named-barrier row

Warpgroup 0's code (pcs 103–1841, warps 0–3) has ten barrier sites (`wg0Sites`, checked on the
code by `wg0_sites`), all with register ids and counts:

* `wg0_sync` (barrier 9, 128 threads; `bar.sync`, aligned) at the eight pcs of `wg0NineSites`;
* the warp-pair barrier at pc 475 (`bar.sync`, aligned): barrier `10 + warp % 2` (10 for warps 0
  and 2, 11 for warps 1 and 3), 64 threads; the id is computed (`or.b32` of `10` and the warp
  index's parity, pcs 241–242), the only one that is not a moved constant;
* `everyone_sync` (barrier 12, 384 threads; `barrier.sync`, unaligned) at pc 1835: its count
  register holds the CTA's size, so its event carries no count (`barTmpl`).

The values are the producer's to prove (the moves and the computed id are in
`Data/Barriers.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

noncomputable section

namespace BarRow

/-- The `wg0_sync` sites. -/
def wg0NineSites : List Nat := [256, 569, 1154, 1156, 1342, 1502, 1659, 1817]

/-- Warpgroup 0's barrier sites. -/
def wg0Sites : List (Nat × Shape) :=
  (475, .sync true) :: (1835, .sync false) :: wg0NineSites.map fun pc => (pc, .sync true)

/-- **Static check**: the barrier sites of pcs 103–1841 are `wg0Sites`. -/
theorem wg0_sites : regionOk kernel.code 103 1842 wg0Sites = true := by
  decide +kernel

/-- **The barrier uses of warpgroup 0**, event `e` of lane `g`. -/
def Wg0Use (L : Launch) (g : Nat) (e : Event) : Prop :=
  (e.pc ∈ wg0NineSites ∧ Sync e 9 128) ∨ (e.pc = 475 ∧ Sync e (10 + warp L g % 2) 64) ∨
    Everyone e 1835

end BarRow

/-- **Row `BarRow.Wg0`**: a barrier event of a lane of warpgroup 0 is one of `Wg0Use`. -/
def BarRow.Wg0 (_P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {e : Event}, g < L.threads → X.get (g, k) = some e → Wg0At L g e.pc →
    Execution.isBar e = true → BarRow.Wg0Use L g e

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
