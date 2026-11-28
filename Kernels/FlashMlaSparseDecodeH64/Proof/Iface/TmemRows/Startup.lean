-- SPDX-License-Identifier: Apache-2.0
-- iface: TmemRow.Startup producer=A status=row-proved domain=consistent ahead=1
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.TmemRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Startup

@[expose] public section

/-! # The startup: Tensor Memory row

The startup (pcs 0–102) has two `tcgen05` sites (checked on the code by `startup_sites`): warp 0's
`tcgen05.alloc` of 512 columns at pc 91, whose address goes to a shared word, and its
`tcgen05.relinquish_alloc_permit` at pc 96, both of CTA group 1. The row: a `tcgen05` event of the
startup is warp 0's, and records `.resource .one (some dst) (.alloc 512)` or
`.resource .one none .relinquish`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

noncomputable section

namespace TmemRow

/-- **Static check**: the `tcgen05` sites of pcs 0–102 are the allocation at 91 and the
relinquishment at 96. -/
theorem startup_sites : regionOk kernel.code 0 103 [(91, .alloc), (96, .relinq)] = true := by
  decide +kernel

end TmemRow

/-- **Row `TmemRow.Startup`**: a `tcgen05` event of the startup is warp 0's allocation of 512
columns or its relinquishment. -/
def TmemRow.Startup (_P : Params) (L : Launch) (X : Execution) : Prop :=
  TmemRow.TcRow L X (fun _ pc => StartupAt pc) fun g e => warp L g = 0 ∧
    ((∃ dst, e.kind = .tc (.resource .one (some dst) (.alloc 512))) ∨
      e.kind = .tc (.resource .one none .relinquish))

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
