-- SPDX-License-Identifier: Apache-2.0
-- iface: BarRow.Mma producer=B status=row-proved domain=consistent ahead=1
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.BarRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Mma

@[expose] public section

/-! # The MMA lane: named-barrier row

The code of the MMA lane (pcs 1850–2161) has one barrier site, `everyone_sync` at pc 2160
(`barrier.sync`, unaligned; checked on the code by `mma_sites`), which every lane of the
role reaches at its end. The row: a barrier event of a lane of the role is that site's, of
barrier 12 with 384 threads. Id and count are registers (moved constants); the producer proves
their values. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

noncomputable section

namespace BarRow

/-- **Static check**: the barrier sites of pcs 1850–2161 are `everyone_sync` at 2160. -/
theorem mma_sites : regionOk kernel.code 1850 2162 [(2160, .sync false)] = true := by
  decide +kernel

end BarRow

/-- **Row `BarRow.Mma`**: a barrier event of a lane of the role is `everyone_sync` at 2160. -/
def BarRow.Mma (_P : Params) (L : Launch) (X : Execution) : Prop :=
  BarRow.EveryoneRow L X (MmaAt L) 2160

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
