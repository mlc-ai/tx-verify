-- SPDX-License-Identifier: Apache-2.0
-- iface: TmemRow.Place producer=A status=row-proved domain=consistent ahead=1
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.TmemRows.Startup
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.TmemRows.Wg0
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.TmemRows.Mma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.TmemRows.Quiet

@[expose] public section

/-! # The Tensor Memory rows

The per-role rows (`TmemRows/<Role>.lean`, `TmemRows/Quiet.lean`) and the dispatch's
**`TmemRow.Place`**: a `tcgen05` event of a launched lane is at a pc of one role's range whose
lane condition the lane meets (as `MbarRow.Place`, `BarRow.Place`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow MbarRow

noncomputable section

/-- **Row `TmemRow.Place`**: a `tcgen05` event of a launched lane is at a pc of a role's code,
and the lane is of that role. -/
def TmemRow.Place (_P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {e : Event} {c : TcKind}, g < L.threads → X.get (g, k) = some e →
    e.kind = .tc c →
    StartupAt e.pc ∨ Wg0At L g e.pc ∨ Wg1At L g e.pc ∨ MmaAt L g e.pc ∨ TmaAt L g e.pc ∨
      IndexAt L g e.pc ∨ DequantAt L g e.pc

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
