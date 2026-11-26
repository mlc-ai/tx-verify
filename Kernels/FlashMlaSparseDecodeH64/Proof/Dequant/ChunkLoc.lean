-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Dequant
public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Objs
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DequantWords

@[expose] public section

/-! # Warpgroup 2's lane constants and the chunk store's location

The lane registers `%r58`, `%r59`, `%r60` as numbers (`lane_tab`, evaluated for the 384 thread
indices) and the chunk store's location (`store_loc`: `dequant b`'s chunk `dqChunk i r s`, `i` the
lane's index in its warpgroup), shared by `Dequant/Export/Mem.lean` and the chunk walk. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 MemRow Dequant

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

namespace Dequant

/-- `%r58`, `%r59`, `%r60` of the thread index word `x`. -/
def f58 (x : BitVec 64) : BitVec 64 :=
  or32 (or32 (andi (shl (shru (andi x 127) 3) 7) 896) (andi (shl x 4) 1024))
    (shl (xor32 (andi (shru (andi x 127) 3) 7) (andi x 7)) 4)
def f59 (x : BitVec 64) : BitVec 64 := shl (andi x 7) 3
def f60 (x : BitVec 64) : BitVec 64 := mul32 (shru (andi x 127) 3) (i32 576)

theorem lane_tab : ∀ t < 384, (f58 (BitVec.ofNat 64 t)).toNat = dqCol (t % 128) ∧
    (f59 (BitVec.ofNat 64 t)).toNat = t % 8 * 8 ∧
    (f60 (BitVec.ofNat 64 t)).toNat = t % 128 / 8 * 576 := by
  decide +kernel

theorem tid_lt (g : Nat) : g % 384 < 384 := Nat.mod_lt _ (by decide)

/-- `%r58` as a number. -/
theorem r58_eq (hp : Pre P L m) (g : Nat) :
    Control.r58W L g = BitVec.ofNat 64 (dqCol (g % 128)) := by
  obtain ⟨h, -, -⟩ := lane_tab (g % 384) (tid_lt g)
  have hc := (dqCol_table (g % 128) (Nat.mod_lt _ (by decide))).2.1
  apply BitVec.eq_of_toNat_eq
  rw [show Control.r58W L g = f58 (tw L g) from rfl, tw, tidOf_eq hp, h,
    Nat.mod_mod_of_dvd _ (by decide : 128 ∣ 384), BitVec.toNat_ofNat]
  omega

/-- **The chunk store's location**: chunk `(r, s)` of the lane in `dequant b`. -/
theorem store_loc (hp : Pre P L m) (g : Nat) (b : Bool) (r : Fin 4) (s : Fin 8) :
    smLoc L g (chunkW L g b r s) 0 =
      wsLoc L (g / L.block) ((Region.dequant (slotF b)).lo + dqChunk (g % 128) r s) := by
  have h3 := sharedBase_lt hp
  have hc := (dqCol_table (g % 128) (Nat.mod_lt _ (by decide))).2.1
  have hr := r.isLt
  have hs := s.isLt
  have hsel : Arith32.sel (Control.s0 b) (sbw L) (addi (sbw L) 65536) =
      bif b then addi (sbw L) 65536 else sbw L := by cases b <;> rfl
  unfold chunkW Control.r2014W
  rw [r58_eq hp, hsel]
  cases b <;> simp only [Bool.cond_true, Bool.cond_false] <;> split_ifs <;>
    simp only [smLoc, wsLoc, add32, addi, r32, i32, sbw, slotF,
      truncBits, Region.lo, dqChunk, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt,
      Loc.mk.injEq, true_and, ↓reduceIte, Bool.false_eq_true] <;> simp <;> omega

end Dequant

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
