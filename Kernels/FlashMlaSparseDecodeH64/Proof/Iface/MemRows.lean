-- SPDX-License-Identifier: Apache-2.0
-- iface: MemRow.Place producer=C status=row-proved domain=consistent ahead=1
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Startup
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Wg0
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Wg1
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Mma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Tma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Index
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Dequant

@[expose] public section

/-! # The memory rows

The per-role rows (`MemRows/<Role>.lean`) and the dispatch's **`MemRow.Place`**: a memory event
of a launched lane is at a pc of one role's range whose lane condition the lane meets (as
`TmemRow.Place`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX MbarRow

noncomputable section

/-- **Row `MemRow.Place`**: a memory event of a launched lane is at a pc of a role's code, and
the lane is of that role. -/
def MemRow.Place (_P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {e : Event}, g < L.threads → X.get (g, k) = some e → MemRow.MemEvent e →
    StartupAt e.pc ∨ Wg0At L g e.pc ∨ Wg1At L g e.pc ∨ MmaAt L g e.pc ∨ TmaAt L g e.pc ∨
      IndexAt L g e.pc ∨ DequantAt L g e.pc

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
