-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ClassBt
public import Kernels.InklingRelDecode.Proof.Thread.EvDProLoad

@[expose] public section

/-!
# The addresses of the prologue's block-table loads

The six loads of the block-table words (`lbSite k`, block `k / 2`, slab `k % 2`) read the address
registers `%rd123 … %rd128`: `%rd7 = block_table + 4 * (stride_bt * req)` plus four times the
word index `2 (split + (k / 2) * num_splits)`, which the code computes with shifts and a 32-bit
sum, and plus 4 for the second slab. Where the block's index `split + (k / 2) * num_splits` is
below `2 ^ 24` and `stride_bt * req + 2 * (index + 1)` is below `2 ^ 31` (no 32-bit wrap-around),
the address is the one of the specification's block table:
`block_table + 4 * (stride_bt * req + 2 * (split + (k / 2) * num_splits) + k % 2)`
(`lb_addr`).
-/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.InklingRelDecode.Proof.EvD

noncomputable section
set_option maxRecDepth 100000

theorem wMadWideS32_ofNat (a b c : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    wMadWideS32 (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) (BitVec.ofNat 64 c) =
      BitVec.ofNat 64 (a * b + c) := by
  unfold wMadWideS32 intBits intOf
  have ea : a % 2 ^ 32 = a := Nat.mod_eq_of_lt (by omega)
  have eb : b % 2 ^ 32 = b := Nat.mod_eq_of_lt (by omega)
  simp only [truncBits_ofNat _ _ (by omega : 32 ≤ 64), truncBits_ofNat 64 _ (by omega : 64 ≤ 64),
    ite_true, tos32, ea, eb, show 2 * 32 = 64 by rfl]
  have h1 : a < 2 ^ 31 := ha
  simp only [h1, hb, ↓reduceIte]
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, toSigned, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  rw [show ((a : Int) * (b : Int)) = ((a * b : Nat) : Int) by push_cast; rfl]
  generalize a * b = p
  have hp : (c % 2 ^ 64 % 2 ^ 64) = c % 2 ^ 64 := by omega
  rw [hp]
  split_ifs <;> omega

theorem ofInt_four : BitVec.ofInt 64 4 = BitVec.ofNat 64 4 := nfI 4
theorem ofInt_six : BitVec.ofInt 64 6 = BitVec.ofNat 64 6 := nfI 6
theorem ofInt_seven : BitVec.ofInt 64 7 = BitVec.ofNat 64 7 := nfI 7
theorem ofInt_eight : BitVec.ofInt 64 8 = BitVec.ofNat 64 8 := nfI 8

/-- `%rd7 = block_table + 4 * (stride_bt * req)`. -/
theorem rd7_eq (L : Launch) (g : Nat) (dt : Dat) (h : dt.pro.w67 * cta L g .z < 2 ^ 31)
    (hz32 : cta L g .z < 2 ^ 32) :
    v_rd7 L g dt = BitVec.ofNat 64 (dt.pro.w67 * cta L g .z * 4 + dt.pro.btB) := by
  have hz : cta L g .z % 2 ^ 32 = cta L g .z := Nat.mod_eq_of_lt hz32
  have h2 : dt.pro.w67 * (cta L g .z % 2 ^ 32) % 2 ^ 32 = dt.pro.w67 * cta L g .z := by
    rw [hz]; exact Nat.mod_eq_of_lt (by omega)
  simp only [v_rd7, v_r230, v_r67, v_r19, wCta_eq, wMulLo32_ofNat, ofInt_four, h2, v_rd72]
  rw [wMadWideS32_ofNat _ _ _ h (by norm_num)]

/-- `%r1451 = split << 7`. -/
theorem r1451_form (L : Launch) (g : Nat) (dt : Dat) (hx : cta L g .x < 2 ^ 24) :
    v_r1451 L g dt = BitVec.ofNat 64 (cta L g .x * 128) := by
  have h1 : cta L g .x % 2 ^ 32 = cta L g .x := Nat.mod_eq_of_lt (by omega)
  simp only [v_r1451, v_r17, wCta_eq, ofInt_seven, wShl32_ofNat _ 7 (by norm_num), h1]
  congr 1
  omega

/-- `%rd123 = %rd7 + 4 * (2 * split)`: the address of word 0. -/
theorem rd123_eq (L : Launch) (g : Nat) (dt : Dat) (h : dt.pro.w67 * cta L g .z < 2 ^ 31)
    (hz32 : cta L g .z < 2 ^ 32) (hx : cta L g .x < 2 ^ 24) :
    v_rd123 L g dt = BitVec.ofNat 64 (dt.pro.w67 * cta L g .z * 4 + dt.pro.btB +
      4 * (2 * cta L g .x)) := by
  have e1 := r1451_form L g dt hx
  have e2 : v_r231 L g dt = BitVec.ofNat 64 (2 * cta L g .x) := by
    rw [v_r231, e1, ofInt_six, wShrS32_ofNat _ 6 (by omega) (by norm_num)]
    congr 1
    omega
  rw [v_rd123, e2, rd7_eq L g dt h hz32, ofInt_four, wMadWideS32_ofNat _ _ _ (by omega)
    (by norm_num)]
  congr 1
  omega

theorem rd124_eq (L : Launch) (g : Nat) (dt : Dat) (h : dt.pro.w67 * cta L g .z < 2 ^ 31)
    (hz32 : cta L g .z < 2 ^ 32) (hx : cta L g .x < 2 ^ 24) :
    v_rd124 L g dt = BitVec.ofNat 64 ((dt.pro.w67 * cta L g .z * 4 + dt.pro.btB +
      4 * (2 * cta L g .x) + 4) % 2 ^ 64) := by
  rw [v_rd124, rd123_eq L g dt h hz32 hx, ofInt_four, wAdd64_ofNat]

/-- `%rd125`: the address of word 2 (block 1, slab 0). -/
theorem rd125_eq (L : Launch) (g : Nat) (dt : Dat) (h : dt.pro.w67 * cta L g .z < 2 ^ 31)
    (hz32 : cta L g .z < 2 ^ 32) (hx : cta L g .x + dt.pro.w71 < 2 ^ 24) :
    v_rd125 L g dt = BitVec.ofNat 64 (dt.pro.w67 * cta L g .z * 4 + dt.pro.btB +
      4 * (2 * (cta L g .x + dt.pro.w71))) := by
  have h1 : cta L g .x % 2 ^ 32 = cta L g .x := Nat.mod_eq_of_lt (by omega)
  have e1 : v_r250 L g dt = BitVec.ofNat 64 (dt.pro.w71 + cta L g .x) := by
    simp only [v_r250, v_r71, v_r17, wCta_eq, wAdd32_ofNat, h1]
    congr 1
    omega
  have e2 : v_r251 L g dt = BitVec.ofNat 64 ((dt.pro.w71 + cta L g .x) * 128) := by
    rw [v_r251, e1, ofInt_seven, wShl32_ofNat _ 7 (by norm_num)]
    congr 1
    omega
  have e3 : v_r252 L g dt = BitVec.ofNat 64 (2 * (dt.pro.w71 + cta L g .x)) := by
    rw [v_r252, e2, ofInt_six, wShrS32_ofNat _ 6 (by omega) (by norm_num)]
    congr 1
    omega
  rw [v_rd125, e3, rd7_eq L g dt h hz32, ofInt_four, wMadWideS32_ofNat _ _ _ (by omega)
    (by norm_num)]
  congr 1
  omega

theorem rd126_eq (L : Launch) (g : Nat) (dt : Dat) (h : dt.pro.w67 * cta L g .z < 2 ^ 31)
    (hz32 : cta L g .z < 2 ^ 32) (hx : cta L g .x + dt.pro.w71 < 2 ^ 24) :
    v_rd126 L g dt = BitVec.ofNat 64 ((dt.pro.w67 * cta L g .z * 4 + dt.pro.btB +
      4 * (2 * (cta L g .x + dt.pro.w71)) + 4) % 2 ^ 64) := by
  rw [v_rd126, rd125_eq L g dt h hz32 hx, ofInt_four, wAdd64_ofNat]

/-- `%rd127`: the address of word 4 (block 2, slab 0). -/
theorem rd127_eq (L : Launch) (g : Nat) (dt : Dat) (h : dt.pro.w67 * cta L g .z < 2 ^ 31)
    (hz32 : cta L g .z < 2 ^ 32) (hx : cta L g .x + 2 * dt.pro.w71 < 2 ^ 24) :
    v_rd127 L g dt = BitVec.ofNat 64 (dt.pro.w67 * cta L g .z * 4 + dt.pro.btB +
      4 * (2 * (cta L g .x + 2 * dt.pro.w71))) := by
  have e0 := r1451_form L g dt (by omega)
  have e1 : v_r272 L g dt = BitVec.ofNat 64 (dt.pro.w71 * 256) := by
    rw [v_r272, v_r71, ofInt_eight, wShl32_ofNat _ 8 (by norm_num)]
    congr 1
    omega
  have e2 : v_r273 L g dt = BitVec.ofNat 64 (dt.pro.w71 * 256 + cta L g .x * 128) := by
    rw [v_r273, e1, e0, wAdd32_ofNat]
    congr 1
    omega
  have e3 : v_r274 L g dt = BitVec.ofNat 64 (2 * (cta L g .x + 2 * dt.pro.w71)) := by
    rw [v_r274, e2, ofInt_six, wShrS32_ofNat _ 6 (by omega) (by norm_num)]
    congr 1
    omega
  rw [v_rd127, e3, rd7_eq L g dt h hz32, ofInt_four, wMadWideS32_ofNat _ _ _ (by omega)
    (by norm_num)]
  congr 1
  omega

theorem rd128_eq (L : Launch) (g : Nat) (dt : Dat) (h : dt.pro.w67 * cta L g .z < 2 ^ 31)
    (hz32 : cta L g .z < 2 ^ 32) (hx : cta L g .x + 2 * dt.pro.w71 < 2 ^ 24) :
    v_rd128 L g dt = BitVec.ofNat 64 ((dt.pro.w67 * cta L g .z * 4 + dt.pro.btB +
      4 * (2 * (cta L g .x + 2 * dt.pro.w71)) + 4) % 2 ^ 64) := by
  rw [v_rd128, rd127_eq L g dt h hz32 hx, ofInt_four, wAdd64_ofNat]

/-- **The address of block-table word `k`** (block `k / 2`, slab `k % 2`): where the index fits,
it is `block_table + 4 (stride_bt * req + 2 (split + (k / 2) * num_splits) + k % 2)` modulo
`2 ^ 64`. -/
theorem lb_addr (L : Launch) (g : Nat) (dt : Dat) {k : Nat} (hk : k < 6)
    (hz32 : cta L g .z < 2 ^ 32)
    (hidx : dt.pro.w67 * cta L g .z + 2 * (cta L g .x + k / 2 * dt.pro.w71) + k % 2 < 2 ^ 31)
    (hx : cta L g .x + k / 2 * dt.pro.w71 < 2 ^ 24) :
    loadAddr L g dt (lbSite k) = (dt.pro.btB + 4 * (dt.pro.w67 * cta L g .z +
      2 * (cta L g .x + k / 2 * dt.pro.w71) + k % 2)) % 2 ^ 64 := by
  have hS : dt.pro.w67 * cta L g .z < 2 ^ 31 := by omega
  interval_cases k
  · have h : valueOf L g dt (gloadBase (lbSite 0).pc) = .bits 64 (v_rd123 L g dt) := rfl
    rw [loadAddr, h, rd123_eq L g dt hS hz32 (by omega)]
    simp only [BitVec.toNat_ofNat]
    congr 1
    omega
  · have h : valueOf L g dt (gloadBase (lbSite 1).pc) = .bits 64 (v_rd124 L g dt) := rfl
    rw [loadAddr, h, rd124_eq L g dt hS hz32 (by omega)]
    simp only [BitVec.toNat_ofNat, Nat.mod_mod]
    congr 1
    omega
  · have h : valueOf L g dt (gloadBase (lbSite 2).pc) = .bits 64 (v_rd125 L g dt) := rfl
    rw [loadAddr, h, rd125_eq L g dt hS hz32 (by omega)]
    simp only [BitVec.toNat_ofNat]
    congr 1
    omega
  · have h : valueOf L g dt (gloadBase (lbSite 3).pc) = .bits 64 (v_rd126 L g dt) := rfl
    rw [loadAddr, h, rd126_eq L g dt hS hz32 (by omega)]
    simp only [BitVec.toNat_ofNat, Nat.mod_mod]
    congr 1
    omega
  · have h : valueOf L g dt (gloadBase (lbSite 4).pc) = .bits 64 (v_rd127 L g dt) := rfl
    rw [loadAddr, h, rd127_eq L g dt hS hz32 (by omega)]
    simp only [BitVec.toNat_ofNat]
    congr 1
    omega
  · have h : valueOf L g dt (gloadBase (lbSite 5).pc) = .bits 64 (v_rd128 L g dt) := rfl
    rw [loadAddr, h, rd128_eq L g dt hS hz32 (by omega)]
    simp only [BitVec.toNat_ofNat, Nat.mod_mod]
    congr 1
    omega

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
