-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Dequant
public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Control.Machine
public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.ChunkLoc
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Ev

@[expose] public section

/-! # The locations of warpgroup 2's shared reads

`scale_loc`, `rawRd_loc`: the location of a scale element and of a raw word as the workspace's
byte (`wsLoc`), from the lane's offsets (`r59`, `r60`) and the slot's raw buffer. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 MemRow Dequant

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

namespace Dequant

theorem r60_eq (hp : Pre P L m) (g : Nat) :
    Control.r60W L g = BitVec.ofNat 64 (g % 128 / 8 * 576) := by
  obtain ⟨-, -, h⟩ := lane_tab (g % 384) (tid_lt g)
  apply BitVec.eq_of_toNat_eq
  rw [show Control.r60W L g = f60 (tw L g) from rfl, tw, tidOf_eq hp, h,
    Nat.mod_mod_of_dvd _ (by decide : 128 ∣ 384), BitVec.toNat_ofNat]
  omega

theorem r59_eq (hp : Pre P L m) (g : Nat) :
    Control.r59W L g = BitVec.ofNat 64 (g % 8 * 8) := by
  obtain ⟨-, h, -⟩ := lane_tab (g % 384) (tid_lt g)
  apply BitVec.eq_of_toNat_eq
  rw [show Control.r59W L g = f59 (tw L g) from rfl, tw, tidOf_eq hp, h,
    Nat.mod_mod_of_dvd _ (by decide : 8 ∣ 384), BitVec.toNat_ofNat]
  omega

theorem raw_sel (b : Bool) :
    Arith32.sel (Control.s0 b) (addi (sbw L) 131072) (addi (sbw L) 167936) =
      bif b then addi (sbw L) 167936 else addi (sbw L) 131072 := by cases b <;> rfl

/-- A word `c` above the raw buffer at `base` plus `off` is the workspace's byte
`base + c + off`. -/
theorem raw_addr' (hp : Pre P L m) (g : Nat) {base c off : Nat} (hb : base ≤ 167936)
    (hc : c + off < 36864) :
    smLoc L g (add32 (addi (sbw L) (Int.ofNat base)) (BitVec.ofNat 64 c)) (Int.ofNat off) =
      wsLoc L (g / L.block) (base + c + off) := by
  have h3 := sharedBase_lt hp
  simp only [smLoc, wsLoc, add32, addi, r32, i32, sbw, truncBits, BitVec.toNat_ofNat,
    BitVec.toNat_add, BitVec.toNat_ofInt, Loc.mk.injEq, true_and]
  simp
  omega

/-- A word `c` above a raw buffer's base plus `off` is that buffer's byte `c + off`. -/
theorem raw_addr (hp : Pre P L m) (g : Nat) (b : Bool) {c off : Nat}
    (hc : c + off < 36864) :
    smLoc L g (add32 (bif b then addi (sbw L) 167936 else addi (sbw L) 131072)
      (BitVec.ofNat 64 c)) (Int.ofNat off) =
      wsLoc L (g / L.block) ((Region.raw (slotF b)).lo + c + off) := by
  cases b
  · exact raw_addr' hp g (base := 131072) (by decide) hc
  · exact raw_addr' hp g (base := 167936) (by decide) hc

/-- **The scale read's location**: element `j` of row `r`'s scale vector in `raw b`. -/
theorem scale_loc (hp : Pre P L m) (g : Nat) (b : Bool) (r : Fin 4) (j : Nat) :
    (smLoc L g (Control.r2338W L g b) (scaleOff r)).at (4 * j) =
      wsLoc L (g / L.block)
        ((Region.raw (slotF b)).lo + g % 128 / 8 * 576 + (512 + 9216 * r.val) + 4 * j) := by
  have hr := r.isLt
  have hi : g % 128 / 8 * 576 ≤ 15 * 576 := Nat.mul_le_mul_right _ (by omega)
  have hw : Control.r2338W L g b =
      add32 (bif b then addi (sbw L) 167936 else addi (sbw L) 131072)
        (BitVec.ofNat 64 (g % 128 / 8 * 576)) := by
    rw [← raw_sel, ← r60_eq hp]
  have ho : scaleOff r = Int.ofNat (512 + 9216 * r.val) := by
    simp only [scaleOff, Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [hw, ho, raw_addr hp g b (by omega)]
  simp only [wsLoc, Loc.at, Loc.mk.injEq, true_and]
  omega

/-- Two words `c`, `c'` above the raw buffer at `base` plus `off`. -/
theorem raw_addr2' (hp : Pre P L m) (g : Nat) {base c c' off : Nat} (hb : base ≤ 167936)
    (hc : c + c' + off < 36864) :
    smLoc L g (add32 (add32 (addi (sbw L) (Int.ofNat base)) (BitVec.ofNat 64 c))
      (BitVec.ofNat 64 c')) (Int.ofNat off) = wsLoc L (g / L.block) (base + (c + c') + off) := by
  have h3 := sharedBase_lt hp
  simp only [smLoc, wsLoc, add32, addi, r32, i32, sbw, truncBits, BitVec.toNat_ofNat,
    BitVec.toNat_add, BitVec.toNat_ofInt, Loc.mk.injEq, true_and]
  simp
  omega

theorem raw_addr2 (hp : Pre P L m) (g : Nat) (b : Bool) {c c' off : Nat}
    (hc : c + c' + off < 36864) :
    smLoc L g (add32 (add32 (bif b then addi (sbw L) 167936 else addi (sbw L) 131072)
      (BitVec.ofNat 64 c)) (BitVec.ofNat 64 c')) (Int.ofNat off) =
      wsLoc L (g / L.block) ((Region.raw (slotF b)).lo + (c + c') + off) := by
  cases b
  · exact raw_addr2' hp g (base := 131072) (by decide) hc
  · exact raw_addr2' hp g (base := 167936) (by decide) hc

/-- **The raw read's location**: word `s` of row `r` of the lane in `raw b`. -/
theorem rawRd_loc (hp : Pre P L m) (g : Nat) (b : Bool) (r : Fin 4) (s : Fin 8) :
    (smLoc L g (rawRowW L g b) (rawOff r s)).at (8 * 0) =
      wsLoc L (g / L.block) ((Region.raw (slotF b)).lo + (g % 128 / 8 * 576 + g % 8 * 8) +
        (9216 * r.val + 64 * s.val)) := by
  have hr := r.isLt
  have hs := s.isLt
  have hi : g % 128 / 8 * 576 ≤ 15 * 576 := Nat.mul_le_mul_right _ (by omega)
  have h8 : g % 8 * 8 ≤ 56 := by omega
  have ho : rawOff r s = Int.ofNat (9216 * r.val + 64 * s.val) := by
    simp only [rawOff, Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  have hw : rawRowW L g b = add32 (add32
      (bif b then addi (sbw L) 167936 else addi (sbw L) 131072)
      (BitVec.ofNat 64 (g % 128 / 8 * 576))) (BitVec.ofNat 64 (g % 8 * 8)) := by
    rw [← raw_sel, ← r60_eq hp, ← r59_eq hp]
  rw [hw, ho, raw_addr2 hp g b (by omega)]
  simp only [wsLoc, Loc.at, Loc.mk.injEq, true_and]
  omega

end Dequant

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
