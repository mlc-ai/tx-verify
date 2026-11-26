-- SPDX-License-Identifier: Apache-2.0
-- iface: BarRow.Wg1 producer=A status=row-proved domain=consistent ahead=1
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.BarRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Wg1

@[expose] public section

/-! # Warpgroup 1's idle code: named-barrier row

Warpgroup 1's idle code (pcs 2587–2605: warp 6 and the lanes of warps 4, 5 that lost their
election) has one barrier site, `everyone_sync` at pc 2604 (`barrier.sync`, unaligned; checked on
the code by `wg1_sites`); its head (pcs 1842–1849) has none (`wg1Head_sites`). The row: a barrier
event of a lane of the role is that site's, of barrier 12 with 384 threads. Id and count are
registers (moved constants); the producer proves their values. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

noncomputable section

namespace BarRow

/-- **Static check**: the barrier sites of pcs 2587–2605 are `everyone_sync` at 2604. -/
theorem wg1_sites : regionOk kernel.code 2587 2606 [(2604, .sync false)] = true := by
  decide +kernel

end BarRow

/-- **Row `BarRow.Wg1`**: a barrier event of a lane of the role is `everyone_sync` at 2604. -/
def BarRow.Wg1 (_P : Params) (L : Launch) (X : Execution) : Prop :=
  BarRow.EveryoneRow L X (Wg1At L) 2604

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
