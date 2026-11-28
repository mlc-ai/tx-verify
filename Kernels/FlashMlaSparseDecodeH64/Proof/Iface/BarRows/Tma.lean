-- SPDX-License-Identifier: Apache-2.0
-- iface: BarRow.Tma producer=A status=row-proved domain=consistent ahead=1
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.BarRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Tma

@[expose] public section

/-! # The TMA lane: named-barrier row

The code of the TMA lane (pcs 2162–2331) has one barrier site, `everyone_sync` at pc 2330
(`barrier.sync`, unaligned; checked on the code by `tma_sites`), which every lane of the
role reaches at its end. The row: a barrier event of a lane of the role is that site's, of
barrier 12 with 384 threads. Id and count are registers (moved constants); the producer proves
their values.

**Proved** by lane A: `barRow_tma` (`Tma/Export/Bar.lean`, from `tma_bar`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

noncomputable section

namespace BarRow

/-- **Static check**: the barrier sites of pcs 2162–2331 are `everyone_sync` at 2330. -/
theorem tma_sites : regionOk kernel.code 2162 2332 [(2330, .sync false)] = true := by
  decide +kernel

end BarRow

/-- **Row `BarRow.Tma`**: a barrier event of a lane of the role is `everyone_sync` at 2330. -/
def BarRow.Tma (_P : Params) (L : Launch) (X : Execution) : Prop :=
  BarRow.EveryoneRow L X (TmaAt L) 2330

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
