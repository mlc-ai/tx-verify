-- SPDX-License-Identifier: Apache-2.0
-- iface: MemRow.Startup producer=C status=row-proved domain=consistent ahead=1
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Base
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Startup

@[expose] public section

/-! # The startup: memory classification row

The startup's code (pcs 0–102) has two memory instructions (`Startup/Shape.lean`, from Core's
templates): `tcgen05.alloc`'s second step, lane 0's store of the allocated column to the four
bytes of the shared word `Region.tmemWord` (pc 91), and the read-back of that word (pc 92); both
only in warp 0 (`MemRow.Startup`, proved by `memRow_startup`, `Startup/Export/Mem.lean`).

Both name the same word: the read-back's address is the shared variable's byte `222752`
(`ld.shared [sym + 222752]`, no register). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX MbarRow

noncomputable section

/-- **Row `MemRow.Startup`**: a memory event of the startup is warp 0's store of four bytes at
`Region.tmemWord`, or warp 0's read of the same four bytes at pc 92. -/
def MemRow.Startup (_P : Params) (L : Launch) (X : Execution) : Prop :=
  ∀ {g k : Nat} {e : Event}, g < L.threads → X.get (g, k) = some e → StartupAt e.pc →
    MemRow.MemEvent e → warp L g = 0 ∧
    ((∃ (a : Acc) (bs : List Byte), e.kind = .wr a bs ∧
        MemRow.WsAcc L (g / L.block) Region.tmemWord.lo 4 a) ∨
      (e.pc = 92 ∧ ∃ a bs, e.kind = .rd a bs ∧
        MemRow.WsAcc L (g / L.block) Region.tmemWord.lo 4 a))

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
