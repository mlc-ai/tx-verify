-- SPDX-License-Identifier: Apache-2.0
-- iface: BarRow.Index producer=A status=row-proved domain=consistent ahead=1
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.BarRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Index

@[expose] public section

/-! # The index lanes: named-barrier row

The code of the index lanes (pcs 2332–2586) has one barrier site, `everyone_sync` at pc 2585
(`barrier.sync`, unaligned; checked on the code by `index_sites`), which every lane of the
role reaches at its end. The row: a barrier event of a lane of the role is that site's, of
barrier 12 with 384 threads. Id and count are registers (moved constants); the producer proves
their values. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

noncomputable section

namespace BarRow

/-- **Static check**: the barrier sites of pcs 2332–2586 are `everyone_sync` at 2585. -/
theorem index_sites : regionOk kernel.code 2332 2587 [(2585, .sync false)] = true := by
  decide +kernel

end BarRow

/-- **Row `BarRow.Index`**: a barrier event of a lane of the role is `everyone_sync` at 2585. -/
def BarRow.Index (_P : Params) (L : Launch) (X : Execution) : Prop :=
  BarRow.EveryoneRow L X (IndexAt L) 2585

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
