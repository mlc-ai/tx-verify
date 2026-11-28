-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Mma.Ev
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base

@[expose] public section

/-! # The MMA warp's mbarrier words as the named objects

The shared words of the role's mbarrier registers (`Ev.lean`) are the mbarriers of the families of
`Iface/Objects.lean` in the thread's CTA (`MbarRow.loc`): the query's two, and per stage `b` of the
block loop (the phase word `W b`) the stage's `dequantReady`, `qkDone`, `soReady` and `svDone`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- A word `c` bytes above the shared base names the object at that offset. -/
theorem smLoc_sbw (hp : Pre P L m) {c : Nat} (hc : c ≤ 222944) :
    smLoc L g (addi (sbw L) c) 0 = ⟨.shared, g / L.block, L.sharedBase + c⟩ := by
  have h3 := sharedBase_lt hp
  simp only [smLoc, addi, r32, i32, sbw, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add,
    BitVec.toNat_ofInt, Loc.mk.injEq, true_and]
  omega

/-- A stage's word `c` bytes above the stage's base names the object at offset `c + 8 b`. -/
theorem smLoc_bb (hp : Pre P L m) (b : Fin 2) {c : Nat} (hc : c ≤ 222936) :
    smLoc L g (addi (bb L (W b.val)) c) 0 =
      ⟨.shared, g / L.block, L.sharedBase + (c + 8 * b.val)⟩ := by
  have h3 := sharedBase_lt hp
  fin_cases b <;>
  simp only [smLoc, addi, add32, shl, r32, i32, sbw, bb, W, truncBits, BitVec.toNat_ofNat,
    BitVec.toNat_add, BitVec.toNat_ofInt, BitVec.toNat_shiftLeft, Loc.mk.injEq, true_and] <;>
  simp <;> omega

theorem qTma_loc (hp : Pre P L m) : smLoc L g (qTmaW L) 0 = MbarRow.loc L g .qTma :=
  smLoc_sbw hp (by decide)

theorem qUt_loc (hp : Pre P L m) : smLoc L g (qUtccpW L) 0 = MbarRow.loc L g .qUtccp :=
  smLoc_sbw hp (by decide)

theorem ready_loc (hp : Pre P L m) (b : Fin 2) :
    smLoc L g (readyW L (W b.val)) 0 = MbarRow.loc L g (.dequantReady b) :=
  smLoc_bb hp b (by decide)

theorem qk_loc (hp : Pre P L m) (b : Fin 2) :
    smLoc L g (qkW L (W b.val)) 0 = MbarRow.loc L g (.qkDone b) :=
  smLoc_bb hp b (by decide)

theorem so_loc (hp : Pre P L m) (b : Fin 2) :
    smLoc L g (soW L (W b.val)) 0 = MbarRow.loc L g (.soReady b) :=
  smLoc_bb hp b (by decide)

theorem sv_loc (hp : Pre P L m) (b : Fin 2) :
    smLoc L g (svW L (W b.val)) 0 = MbarRow.loc L g (.svDone b) :=
  smLoc_bb hp b (by decide)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Mma
