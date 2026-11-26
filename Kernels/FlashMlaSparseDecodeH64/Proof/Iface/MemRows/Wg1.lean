-- SPDX-License-Identifier: Apache-2.0
-- iface: MemRow.Wg1 producer=C status=row-proved domain=consistent ahead=1
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Wg1

@[expose] public section

/-! # Warpgroup 1's head and idle code: memory classification row

The head (pcs 1842–1849) makes no memory access; the idle code (pcs 2587–2605) makes the two
length reads, non-coherent global reads of the launch's parameters (`Wg1/Shape.lean`, `IEv`):
`MemRow.Wg1`, proved by `memRow_wg1` (`Wg1/Export/Mem.lean`). The reads' addresses are not stated
(the shape table leaves them unconstrained). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX MbarRow

noncomputable section

/-- **Row `MemRow.Wg1`**: a memory event of the head or the idle code is a non-coherent read. -/
def MemRow.Wg1 (_P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {e : Event}, g < L.threads → X.get (g, k) = some e → Wg1At L g e.pc →
    MemRow.MemEvent e → ∃ a bs, e.kind = .nc a bs

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
