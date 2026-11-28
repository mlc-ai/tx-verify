-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Ev
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Base

@[expose] public section

/-! # Warpgroup 2's mbarrier words as the named objects

The shared words of the role's mbarrier registers (`Ev.lean`) are the mbarriers of the families of
`Iface/Objects.lean` in the thread's CTA (`MbarRow.loc`): `qUtccp`, and per slot `b` (the slot bit
`sb`, `slotF b`) the slot's `rawReady`, `svDone`, `dequantReady` and `rawFree`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 Control

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The ring slot of the slot bit. -/
def slotF (b : Bool) : Fin 2 := if b then 1 else 0

/-- A slot's word `c` bytes above the slot's barrier base names the object at `c + 8 b`. -/
theorem smLoc_slot (hp : Pre P L m) (b : Bool) {c : Nat} (hc : c ≤ 222936) :
    smLoc L g (addi (r2330W L b) c) 0 =
      ⟨.shared, g / L.block, L.sharedBase + (c + 8 * (slotF b).val)⟩ := by
  have h3 := sharedBase_lt hp
  have hs : shl (slW b) 3 = BitVec.ofNat 64 (if b then 8 else 0) := by cases b <;> decide
  simp only [r2330W, hs]
  cases b <;>
  simp only [smLoc, addi, add32, r32, i32, sbw, slotF, truncBits, BitVec.toNat_ofNat,
    BitVec.toNat_add, BitVec.toNat_ofInt, Loc.mk.injEq, true_and, Bool.false_eq_true,
    ↓reduceIte] <;> simp <;> omega

theorem q_loc (hp : Pre P L m) : smLoc L g (qW L) 0 = MbarRow.loc L g .qUtccp := by
  have h3 := sharedBase_lt hp
  simp only [smLoc, qW, addi, r32, i32, sbw, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add,
    BitVec.toNat_ofInt, MbarRow.loc, mbarLoc, MbarFam.off, Loc.mk.injEq, true_and]
  omega

theorem raw_loc (hp : Pre P L m) (b : Bool) :
    smLoc L g (rawW L b) 0 = MbarRow.loc L g (.rawReady (slotF b)) :=
  smLoc_slot hp b (by decide)

theorem sv_loc (hp : Pre P L m) (b : Bool) :
    smLoc L g (svW L b) 0 = MbarRow.loc L g (.svDone (slotF b)) :=
  smLoc_slot hp b (by decide)

theorem ready_loc (hp : Pre P L m) (b : Bool) :
    smLoc L g (readyW L b) 0 = MbarRow.loc L g (.dequantReady (slotF b)) :=
  smLoc_slot hp b (by decide)

theorem free_loc (hp : Pre P L m) (b : Bool) :
    smLoc L g (freeW L b) 0 = MbarRow.loc L g (.rawFree (slotF b)) :=
  smLoc_slot hp b (by decide)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Dequant
