-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.Fits
public import Kernels.TmlFa4Fwd.Proof.Mma.Fits
import Std.Tactic.BVDecide.Normalize.BitVec

@[expose] public section

/-! # The loader and the MMA warp agree on the tile's K/V blocks

The loader's block word of the picked tile (`r28Ref`, its setup's `%r28`) is the MMA warp's
(`Mma.blocks` of `Mma.refV`, `tile_agree`): the two compute the same minimum of the same
ceilings. The row term differs only in how the code forms the floor quotient (`row_agree`:
`nt + ~fdiv a b` against `nt - sdiv a b + adj`), and the sums only in their order
(`sum_agree`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section

/-! ### 32-bit words modulo `2 ^ 32` -/

theorem tr_toNat (z : BitVec 64) : (truncBits 32 z).toNat = z.toNat % 2 ^ 32 := by
  simp only [truncBits, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num))

theorem add32_toNat' (x y : BitVec 64) :
    (add32 x y).toNat = (x.toNat % 2 ^ 32 + y.toNat % 2 ^ 32) % 2 ^ 32 := by
  simp only [add32, r32, tr_toNat, BitVec.toNat_add]
  rw [Nat.mod_mod_of_dvd _ (by norm_num : 2 ^ 32 ∣ 2 ^ 64)]

theorem sub32_toNat' (x y : BitVec 64) :
    (sub32 x y).toNat = (x.toNat % 2 ^ 32 + 2 ^ 32 - y.toNat % 2 ^ 32) % 2 ^ 32 := by
  simp only [sub32, r32, tr_toNat, BitVec.toNat_sub]
  have h1 := Nat.mod_lt x.toNat (show 0 < 2 ^ 32 by norm_num)
  have h2 := Nat.mod_lt y.toNat (show 0 < 2 ^ 32 by norm_num)
  rw [Nat.mod_mod_of_dvd _ (by norm_num : 2 ^ 32 ∣ 2 ^ 64)]
  generalize x.toNat % 2 ^ 32 = a at *
  generalize y.toNat % 2 ^ 32 = b at *
  omega

theorem not32_toNat' (x : BitVec 64) : (not32 x).toNat = 2 ^ 32 - 1 - x.toNat % 2 ^ 32 := by
  simp only [not32, r32, tr_toNat, BitVec.toNat_not]
  have h1 := Nat.mod_lt x.toNat (show 0 < 2 ^ 32 by norm_num)
  generalize x.toNat % 2 ^ 32 = a at *
  omega

theorem i32m1_toNat : (i32 (-1)).toNat = 2 ^ 32 - 1 := by
  simp only [i32, tr_toNat, BitVec.toNat_ofInt]; norm_num
theorem i32z_toNat : (i32 0).toNat = 0 := by
  simp only [i32, tr_toNat, BitVec.toNat_ofInt]; norm_num
theorem i32_256_toNat : (i32 256).toNat = 256 := by
  simp only [i32, tr_toNat, BitVec.toNat_ofInt]; norm_num
theorem toSigned_i32m1 : toSigned 32 (i32 (-1)) = -1 := by
  simp only [toSigned, i32m1_toNat]; norm_num
theorem toSigned_i32z : toSigned 32 (i32 0) = 0 := by
  simp only [toSigned, i32z_toNat]; norm_num

theorem addi256_toNat (x : BitVec 64) :
    (addi x 256).toNat = (x.toNat % 2 ^ 32 + 256) % 2 ^ 32 := by
  show (truncBits 32 (r32 x + i32 256)).toNat = _
  rw [tr_toNat, BitVec.toNat_add, r32, tr_toNat, i32_256_toNat,
    Nat.mod_mod_of_dvd _ (by norm_num : 2 ^ 32 ∣ 2 ^ 64)]

theorem add32_not_add (x y z : BitVec 64) :
    add32 x (not32 (add32 y z)) = add32 (sub32 x y) (not32 z) := by
  apply BitVec.eq_of_toNat_eq
  rw [add32_toNat', add32_toNat', not32_toNat', not32_toNat', add32_toNat', sub32_toNat']
  have h1 := Nat.mod_lt x.toNat (show 0 < 2 ^ 32 by norm_num)
  have h2 := Nat.mod_lt y.toNat (show 0 < 2 ^ 32 by norm_num)
  have h3 := Nat.mod_lt z.toNat (show 0 < 2 ^ 32 by norm_num)
  simp only [Nat.mod_mod]
  generalize x.toNat % 2 ^ 32 = a at *
  generalize y.toNat % 2 ^ 32 = b at *
  generalize z.toNat % 2 ^ 32 = c at *
  omega

theorem not32_m1 : not32 (i32 (-1)) = i32 0 := by
  apply BitVec.eq_of_toNat_eq; rw [not32_toNat', i32m1_toNat, i32z_toNat]; norm_num
theorem not32_z : not32 (i32 0) = i32 (-1) := by
  apply BitVec.eq_of_toNat_eq; rw [not32_toNat', i32m1_toNat, i32z_toNat]; norm_num

/-- **The two forms of the row term agree.** -/
theorem row_agree (nt a b : BitVec 64) :
    add32 nt (not32 (fdiv a b)) =
      add32 (sub32 nt (sdiv a b))
        (sel (scmp .eq .b a (mul32 b (sdiv a b)) || scmpi .gt .s (xor32 b a) (-1))
          (i32 (-1)) (i32 0)) := by
  have hne : scmp .ne .b a (mul32 b (sdiv a b)) = !scmp .eq .b a (mul32 b (sdiv a b)) := by
    simp [scmp, compare]
  have hlt : scmpi .lt .s (xor32 b a) 0 = !scmpi .gt .s (xor32 b a) (-1) := by
    simp only [scmpi, compare]
    rw [toSigned_i32z, toSigned_i32m1]
    by_cases h : toSigned 32 (r32 (xor32 b a)) < 0 <;> simp [h] <;> omega
  simp only [fdiv, hne, hlt, add32_not_add]
  cases scmp .eq .b a (mul32 b (sdiv a b)) <;> cases scmpi .gt .s (xor32 b a) (-1) <;>
    simp [sel, not32_m1, not32_z]

/-- The loader's sum and the MMA warp's sum agree. -/
theorem sum_agree (r u d : BitVec 64) :
    addi (add32 (add32 r u) d) 256 = add32 (add32 u (addi r 256)) d := by
  apply BitVec.eq_of_toNat_eq
  rw [addi256_toNat, add32_toNat', add32_toNat', add32_toNat', add32_toNat', addi256_toNat]
  have h1 := Nat.mod_lt r.toNat (show 0 < 2 ^ 32 by norm_num)
  have h2 := Nat.mod_lt u.toNat (show 0 < 2 ^ 32 by norm_num)
  have h3 := Nat.mod_lt d.toNat (show 0 < 2 ^ 32 by norm_num)
  simp only [Nat.mod_mod]
  generalize r.toNat % 2 ^ 32 = a at *
  generalize u.toNat % 2 ^ 32 = b at *
  generalize d.toNat % 2 ^ 32 = c at *
  omega

/-! ### The agreement -/

variable {p : Params} {L : Launch} {g : Nat}

/-- **The loader's block word of the picked tile is the MMA warp's**, on lanes of one CTA. -/
theorem tile_agree {y : Nat} (hc : y / L.block = g / L.block) (R : Nat) (bal : BitVec 64) :
    Loader.r28Ref p L y R bal = Mma.blocks p L g (Mma.refV p L g R bal) := by
  simp only [Loader.r28Ref, Loader.setup, Mma.blocks, Loader.refVL, Mma.refV, Loader.coords,
    Mma.coords, Mma.ceil128, Loader.cdivS, Loader.cdivP, Epilogue.ctaW, hc]
  rw [row_agree, sum_agree]

end
end PTX.Kernels.TmlFa4Fwd.Proof
