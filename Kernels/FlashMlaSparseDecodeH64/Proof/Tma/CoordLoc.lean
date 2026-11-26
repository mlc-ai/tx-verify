-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Objs
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.Regions

@[expose] public section

/-! # The coordinate words' places

The word of coordinate quadruple `q` of the TMA lane's slot `b < 4` is the workspace byte
`221728 + 256 b + 16 q` (`crd_loc`): the slot word is `W b`, so the quadruples' base is the
workspace byte `256 b` above the table. Shared by the memory row (`Tma/Export/Mem.lean`) and the
reads' uses (`Tma/Export/Use.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

variable {P : Params} {L : Launch} {m : Mem0}

/-- The word of coordinate quadruple `q` of slot `b` is the workspace byte
`221728 + 256 b + 16 q`. -/
theorem crd_loc (hp : Pre P L m) {g : Nat} {d : D} {b : Nat} (hb : b < 4)
    (hs : d.slot = W b) (q : Fin 16) :
    smLoc L g (crdB L d) (coordOff q) =
      wsLoc L (g / L.block) (221728 + 256 * b + 16 * q.val) := by
  have h3 := sharedBase_lt hp
  have hq := q.isLt
  simp only [crdB, ringB, hs]
  rw [slotB_W hp hb, show (248 : Int) = ((248 : Nat) : Int) from rfl,
    i32_W (n := 248) (by decide), mad32_W (by omega) (by decide) (by omega)]
  simp only [smLoc, wsLoc, coordOff, W, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add,
    BitVec.toNat_ofInt, Loc.mk.injEq, true_and]
  omega

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Tma
