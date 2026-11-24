-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Machine
import Kernels.TmlFa4Fwd.Proof.Protocol.KV.TileAgree
import Std.Tactic.BVDecide.Normalize.BitVec

@[expose] public section

/-! # Signed values of 32-bit words

The signed value `S x` of a word's low half, under the additions, minima and shifts of the tile
arithmetic, when they do not overflow. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Softmax (max32)

noncomputable section

/-! ### Signed 32-bit words -/

/-- A word's signed value. -/
def S (x : BitVec 64) : Int := toSigned 32 (r32 x)

theorem S_def (x : BitVec 64) :
    S x = if x.toNat % 2 ^ 32 < 2 ^ 31 then ((x.toNat % 2 ^ 32 : Nat) : Int)
      else ((x.toNat % 2 ^ 32 : Nat) : Int) - 2 ^ 32 := by
  simp only [S, toSigned, r32, tr_toNat, Nat.mod_mod]

theorem S_range (x : BitVec 64) : -2 ^ 31 ≤ S x ∧ S x < 2 ^ 31 := by
  rw [S_def]
  have := Nat.mod_lt x.toNat (show 0 < 2 ^ 32 by norm_num)
  split <;> omega

/-- Signed values modulo `2 ^ 32`. -/
theorem S_mod (x : BitVec 64) : ∃ k : Int, S x = x.toNat + 2 ^ 32 * k := by
  rw [S_def]
  split
  · exact ⟨-(x.toNat / 2 ^ 32 : Nat), by omega⟩
  · exact ⟨-(x.toNat / 2 ^ 32 : Nat) - 1, by omega⟩

theorem S_eq {x : BitVec 64} {v : Int} (h0 : -2 ^ 31 ≤ v) (h1 : v < 2 ^ 31)
    (h : ∃ k : Int, (x.toNat : Int) = v + 2 ^ 32 * k) : S x = v := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨k', hk'⟩ := S_mod x
  have := S_range x
  omega

theorem S_add {x y : BitVec 64} (h0 : -2 ^ 31 ≤ S x + S y) (h1 : S x + S y < 2 ^ 31) :
    S (add32 x y) = S x + S y := by
  obtain ⟨a, ha⟩ := S_mod x
  obtain ⟨b, hb⟩ := S_mod y
  refine S_eq h0 h1 ?_
  rw [add32_toNat', ha, hb]
  refine ⟨-((x.toNat % 2 ^ 32 + y.toNat % 2 ^ 32) / 2 ^ 32 : Nat) -
    (x.toNat / 2 ^ 32 : Nat) - (y.toNat / 2 ^ 32 : Nat) - a - b, ?_⟩
  omega

theorem S_sub {x y : BitVec 64} (h0 : -2 ^ 31 ≤ S x - S y) (h1 : S x - S y < 2 ^ 31) :
    S (sub32 x y) = S x - S y := by
  obtain ⟨a, ha⟩ := S_mod x
  obtain ⟨b, hb⟩ := S_mod y
  refine S_eq h0 h1 ?_
  rw [sub32_toNat', ha, hb]
  refine ⟨1 - ((x.toNat % 2 ^ 32 + 2 ^ 32 - y.toNat % 2 ^ 32) / 2 ^ 32 : Nat) -
    (x.toNat / 2 ^ 32 : Nat) + (y.toNat / 2 ^ 32 : Nat) - a + b, ?_⟩
  have := Nat.mod_lt y.toNat (show 0 < 2 ^ 32 by norm_num)
  omega

theorem S_addi {x : BitVec 64} {n : Int} (hn : S (i32 n) = n)
    (h0 : -2 ^ 31 ≤ S x + n) (h1 : S x + n < 2 ^ 31) : S (addi x n) = S x + n := by
  have he : addi x n = add32 x (i32 n) := by
    apply BitVec.eq_of_toNat_eq
    rw [add32_toNat']
    simp only [r32, tr_toNat, BitVec.toNat_add, i32]
    rw [Nat.mod_mod_of_dvd _ (by norm_num : 2 ^ 32 ∣ 2 ^ 64)]
    omega
  rw [he, S_add (by rw [hn]; exact h0) (by rw [hn]; exact h1), hn]

theorem S_min (x y : BitVec 64) : S (min32 x y) = min (S x) (S y) := by
  have hr : ∀ z : BitVec 64, S (r32 z) = S z := fun z => by
    rw [S_def, S_def, r32, tr_toNat, Nat.mod_mod]
  simp only [min32, compare, decide_eq_true_eq]
  change S (if S x < S y then r32 x else r32 y) = _
  split
  · rw [hr]; omega
  · rw [hr]; omega

theorem S_max (x y : BitVec 64) : S (max32 x y) = max (S x) (S y) := by
  have hr : ∀ z : BitVec 64, S (r32 z) = S z := fun z => by
    rw [S_def, S_def, r32, tr_toNat, Nat.mod_mod]
  simp only [max32, scmp, sel, compare, decide_eq_true_eq]
  change S (if S x > S y then r32 x else r32 y) = _
  split
  · rw [hr]; omega
  · rw [hr]; omega

theorem S_shrs7 (x : BitVec 64) : S (shrs x 7) = S x / 2 ^ 7 := by
  have h7 : (i32 7).toNat = 7 := by decide
  have hr := S_range x
  have he : shrs x 7 = truncBits 32 (BitVec.ofInt 64 (S x / 2 ^ 7)) := by
    simp only [shrs, h7]
    rfl
  rw [he]
  refine S_eq (by omega) (by omega) ?_
  rw [tr_toNat, BitVec.toNat_ofInt]
  generalize S x / 2 ^ 7 = v
  refine ⟨-(((v % ((2 ^ 64 : Nat) : Int)).toNat / 2 ^ 32 : Nat) : Int) -
    2 ^ 32 * (v / ((2 ^ 64 : Nat) : Int)), ?_⟩
  omega

/-- A block count is small. -/
theorem S_ceil (x : BitVec 64) :
    -2 ^ 25 ≤ S (Mma.ceil128 x) ∧ S (Mma.ceil128 x) ≤ 2 ^ 25 := by
  unfold Mma.ceil128
  dsimp only
  generalize add32 x (shru (shrs x 31) 25) = s
  have h1 := S_shrs7 s
  have h2 := S_range s
  have hs : ∀ c : Bool, 0 ≤ S (sel c (i32 1) (i32 0)) ∧ S (sel c (i32 1) (i32 0)) ≤ 1 := by decide
  obtain ⟨h3, h4⟩ := hs (scmpi .gt .s x (-1) && scmp .ne .b x (andi s (-128)))
  rw [S_add (by omega) (by omega)]
  omega

end
end PTX.Kernels.TmlFa4Fwd.Proof
