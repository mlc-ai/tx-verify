-- SPDX-License-Identifier: Apache-2.0
-- iface: BarRow.Dequant producer=D status=row-proved domain=consistent ahead=1
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.BarRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Dequant

@[expose] public section

/-! # The dequant lanes: named-barrier row

The code of the dequant lanes (pcs 2606–3610) has one barrier site, `everyone_sync` at pc 3610
(`barrier.sync`, unaligned; checked on the code by `dequant_sites`), which every lane of the
role reaches at its end. The row: a barrier event of a lane of the role is that site's, of
barrier 12 of the whole CTA (384 threads, recorded without a count). Id and count are registers
(moved constants); the producer proves their values (`barRow_dequant`,
`Dequant/Export/Bar.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

noncomputable section

namespace BarRow

/-- **Static check**: the barrier sites of pcs 2606–3610 are `everyone_sync` at 3610. -/
theorem dequant_sites : regionOk kernel.code 2606 3611 [(3610, .sync false)] = true := by
  decide +kernel

end BarRow

/-- **Row `BarRow.Dequant`**: a barrier event of a lane of the role is `everyone_sync` at 3610. -/
def BarRow.Dequant (_P : Params) (L : Launch) (X : Execution) : Prop :=
  BarRow.EveryoneRow L X (DequantAt L) 3610

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
