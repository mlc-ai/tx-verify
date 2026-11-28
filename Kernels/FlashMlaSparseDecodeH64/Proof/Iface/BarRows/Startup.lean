-- SPDX-License-Identifier: Apache-2.0
-- iface: BarRow.Startup producer=A status=row-proved domain=consistent ahead=1
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.BarRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Startup

@[expose] public section

/-! # The startup: named-barrier row

Every thread runs the startup (pcs 0–102); its one barrier site is the `bar.sync 0` at pc 97
(`__syncthreads`, aligned, immediate id, no count; checked on the code by `startup_sites`). The
row: a barrier event of the startup is that site's, of barrier 0 without a thread count. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

noncomputable section

namespace BarRow

/-- **Static check**: the barrier sites of pcs 0–102 are the `bar.sync 0` at 97. -/
theorem startup_sites : regionOk kernel.code 0 103 [(97, .cta)] = true := by
  decide +kernel

end BarRow

/-- **Row `BarRow.Startup`**: a barrier event of the startup is the `bar.sync 0` at 97. -/
def BarRow.Startup (_P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {e : Event}, g < L.threads → X.get (g, k) = some e → StartupAt e.pc →
    Execution.isBar e = true → e.pc = 97 ∧ BarRow.Cta e

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
