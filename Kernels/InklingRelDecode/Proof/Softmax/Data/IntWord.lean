-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Data.W1Max


@[expose] public section

/-! # 32-bit integer words and the predicate select

`w32 z` is the 32-bit word of the integer `z`. The adds and subtracts of the first window's mask
run (pcs 1467 to 1755) act on such words as on integers, a compare with an immediate reads the
word's signed value, and `selp` with the `-inf` immediate gives the word or `-inf`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption

set_option maxRecDepth 100000
noncomputable section

/-- The 32-bit word of an integer. -/
def w32 (z : ℤ) : Value := .bits 32 (truncBits 32 (BitVec.ofInt 64 z))

theorem toNat_w (z : ℤ) : (truncBits 32 (BitVec.ofInt 64 z)).toNat = (z % 2 ^ 32).toNat := by
  unfold truncBits
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  have : (2:ℕ) ^ 64 = 2^32 * 2^32 := by norm_num
  have h2 : (0:ℤ) ≤ z % 2 ^ 64 := Int.emod_nonneg _ (by norm_num)
  have h3 : (z % 2 ^ 64) % 2 ^ 32 = z % 2 ^ 32 := Int.emod_emod_of_dvd _ (by norm_num)
  have h4 : 0 ≤ z % 2 ^ 32 := Int.emod_nonneg _ (by norm_num)
  have h5 : z % 2 ^ 32 < 2 ^ 32 := Int.emod_lt_of_pos _ (by norm_num)
  have h6 : z % 2 ^ 64 < 2 ^ 64 := Int.emod_lt_of_pos _ (by norm_num)
  omega

theorem toSigned_w {z : ℤ} (h1 : -2 ^ 31 ≤ z) (h2 : z < 2 ^ 31) :
    toSigned 32 (truncBits 32 (BitVec.ofInt 64 z)) = z := by
  unfold toSigned
  have : (truncBits 32 (BitVec.ofInt 64 z)).toNat % 2 ^ 32 = (z % 2 ^ 32).toNat := by
    rw [toNat_w]
    have h4 : 0 ≤ z % 2 ^ 32 := Int.emod_nonneg _ (by norm_num)
    have h5 : z % 2 ^ 32 < 2 ^ 32 := Int.emod_lt_of_pos _ (by norm_num)
    omega
  rw [this]
  have h4 : 0 ≤ z % 2 ^ 32 := Int.emod_nonneg _ (by norm_num)
  have h5 : z % 2 ^ 32 < 2 ^ 32 := Int.emod_lt_of_pos _ (by norm_num)
  dsimp only
  split_ifs with h <;> omega

theorem trunc_add (x y : ℤ) : truncBits 32 (truncBits 32 (BitVec.ofInt 64 x) +
    truncBits 32 (BitVec.ofInt 64 y)) = truncBits 32 (BitVec.ofInt 64 (x + y)) := by
  apply BitVec.eq_of_toNat_eq
  have hx := toNat_w x
  have hy := toNat_w y
  have hxy := toNat_w (x + y)
  generalize truncBits 32 (BitVec.ofInt 64 x) = A at *
  generalize truncBits 32 (BitVec.ofInt 64 y) = B at *
  rw [hxy]
  unfold truncBits
  rw [BitVec.toNat_ofNat, BitVec.toNat_add, hx, hy]
  have h4 : 0 ≤ x % 2 ^ 32 := Int.emod_nonneg _ (by norm_num)
  have h5 : 0 ≤ y % 2 ^ 32 := Int.emod_nonneg _ (by norm_num)
  have h6 : x % 2 ^ 32 < 2 ^ 32 := Int.emod_lt_of_pos _ (by norm_num)
  have h7 : y % 2 ^ 32 < 2 ^ 32 := Int.emod_lt_of_pos _ (by norm_num)
  have h8 : (x + y) % 2 ^ 32 = ((x % 2 ^ 32) + (y % 2 ^ 32)) % 2 ^ 32 := by
    rw [Int.add_emod]
  omega

theorem trunc_idem (z : ℤ) :
    truncBits 32 (truncBits 32 (BitVec.ofInt 64 z)) = truncBits 32 (BitVec.ofInt 64 z) := by
  apply BitVec.eq_of_toNat_eq
  have h := toNat_w z
  generalize truncBits 32 (BitVec.ofInt 64 z) = A at *
  rw [h]
  unfold truncBits
  rw [BitVec.toNat_ofNat, h]
  have h4 : 0 ≤ z % 2 ^ 32 := Int.emod_nonneg _ (by norm_num)
  have h5 : z % 2 ^ 32 < 2 ^ 32 := Int.emod_lt_of_pos _ (by norm_num)
  omega

theorem trunc_sub (x y : ℤ) : truncBits 32 (truncBits 32 (BitVec.ofInt 64 x) -
    truncBits 32 (BitVec.ofInt 64 y)) = truncBits 32 (BitVec.ofInt 64 (x - y)) := by
  apply BitVec.eq_of_toNat_eq
  have hx := toNat_w x
  have hy := toNat_w y
  have hxy := toNat_w (x - y)
  generalize truncBits 32 (BitVec.ofInt 64 x) = A at *
  generalize truncBits 32 (BitVec.ofInt 64 y) = B at *
  rw [hxy]
  unfold truncBits
  rw [BitVec.toNat_ofNat, BitVec.toNat_sub, hx, hy]
  have h4 : 0 ≤ x % 2 ^ 32 := Int.emod_nonneg _ (by norm_num)
  have h5 : 0 ≤ y % 2 ^ 32 := Int.emod_nonneg _ (by norm_num)
  have h6 : x % 2 ^ 32 < 2 ^ 32 := Int.emod_lt_of_pos _ (by norm_num)
  have h7 : y % 2 ^ 32 < 2 ^ 32 := Int.emod_lt_of_pos _ (by norm_num)
  have h8 : (x - y) % 2 ^ 32 = ((x % 2 ^ 32) - (y % 2 ^ 32)) % 2 ^ 32 := by
    rw [Int.sub_emod]
  omega

theorem add_w {d a b : Nat} (hab : b ≠ a) (x y : ℤ) (v : Value) :
    okVal v (coreF (.int ⟨.add, .int .s 32, false, [some d], [.reg a, .reg b]⟩) [a, b]
      [w32 x, w32 y]) = w32 (x + y) := by
  have h1 : lk [a, b] [w32 x, w32 y] a = w32 x := by simp [lk]
  have h2 : lk [a, b] [w32 x, w32 y] b = w32 y := by
    simp only [lk, List.zip_cons_cons, List.zip_nil_right, List.lookup, beq_false_of_ne hab,
      beq_self_eq_true, Option.getD_some]
  have e : coreF (.int ⟨.add, .int .s 32, false, [some d], [.reg a, .reg b]⟩) [a, b]
      [w32 x, w32 y] = .ok (w32 (x + y)) := by
    simp only [coreF, coreW, addW, oVal, oBits, h1, h2, pure, Except.pure, bind, Except.bind,
      DType.width]
    simp only [w32, trunc_idem, trunc_add]
  rw [okVal_ok e]

theorem sub_w {d a b : Nat} (hab : b ≠ a) (x y : ℤ) (v : Value) :
    okVal v (coreF (.int ⟨.sub, .int .s 32, false, [some d], [.reg a, .reg b]⟩) [a, b]
      [w32 x, w32 y]) = w32 (x - y) := by
  have h1 : lk [a, b] [w32 x, w32 y] a = w32 x := by simp [lk]
  have h2 : lk [a, b] [w32 x, w32 y] b = w32 y := by
    simp only [lk, List.zip_cons_cons, List.zip_nil_right, List.lookup, beq_false_of_ne hab,
      beq_self_eq_true, Option.getD_some]
  have e : coreF (.int ⟨.sub, .int .s 32, false, [some d], [.reg a, .reg b]⟩) [a, b]
      [w32 x, w32 y] = .ok (w32 (x - y)) := by
    simp only [coreF, coreW, subW, oVal, oBits, h1, h2, pure, Except.pure, bind, Except.bind,
      DType.width]
    simp only [w32, trunc_idem, trunc_sub]
  rw [okVal_ok e]

/-- The signed value of the 32-bit word of an integer. -/
def sg (z : ℤ) : ℤ := toSigned 32 (truncBits 32 (BitVec.ofInt 64 z))

theorem sg_eq {z : ℤ} (h1 : -2 ^ 31 ≤ z) (h2 : z < 2 ^ 31) : sg z = z := toSigned_w h1 h2

theorem setp_gt_w {d a : Nat} {z : ℤ} (v : Value) :
    okVal v (coreF (.int ⟨.setp .gt none, .int .s 32, false, [some d], [.reg a, .imm (-1)]⟩) [a]
      [w32 z]) = .pred (decide (0 ≤ sg z)) := by
  have h : lk [a] [w32 z] a = w32 z := by simp [lk]
  have hk : (DType.int IType.s 32).kind?.getD IType.b = IType.s := rfl
  have hm : toSigned 32 (truncBits 32 (BitVec.ofInt 64 (-1))) = -1 :=
    toSigned_w (by norm_num) (by norm_num)
  have e : coreF (.int ⟨.setp .gt none, .int .s 32, false, [some d], [.reg a, .imm (-1)]⟩) [a]
      [w32 z] = .ok (.pred (decide (0 ≤ sg z))) := by
    simp only [coreF, coreW, oBits, h, pure, Except.pure, bind, Except.bind, DType.width]
    simp only [w32, trunc_idem, compare, sg, hk, hm]
    exact congrArg (fun b => Except.ok (Value.pred b)) (decide_eq_decide.mpr (by omega))
  rw [okVal_ok e]

theorem setp_lt_w {d a : Nat} {z : ℤ} (v : Value) :
    okVal v (coreF (.int ⟨.setp .lt none, .int .s 32, false, [some d], [.reg a, .imm 0]⟩) [a]
      [w32 z]) = .pred (decide (sg z < 0)) := by
  have h : lk [a] [w32 z] a = w32 z := by simp [lk]
  have hk : (DType.int IType.s 32).kind?.getD IType.b = IType.s := rfl
  have hm : toSigned 32 (truncBits 32 (BitVec.ofInt 64 0)) = 0 :=
    toSigned_w (by norm_num) (by norm_num)
  have e : coreF (.int ⟨.setp .lt none, .int .s 32, false, [some d], [.reg a, .imm 0]⟩) [a]
      [w32 z] = .ok (.pred (decide (sg z < 0))) := by
    simp only [coreF, coreW, oBits, h, pure, Except.pure, bind, Except.bind, DType.width]
    simp only [w32, trunc_idem, compare, sg, hk, hm]
    rfl
  rw [okVal_ok e]

theorem selp_ev {d a p : Nat} (hp : p ≠ a) (q : Bool) {w : Value} {x : EReal} (h : Ev w x)
    (v : Value) :
    Ev (okVal v (coreF (.int ⟨.selp, .float .f32, false, [some d],
      [.reg a, .f32imm 4286578688, .reg p]⟩) [a, p] [w, .pred q])) (if q then x else ⊥) := by
  have h1 : lk [a, p] [w, Value.pred q] a = w := by simp [lk]
  have h2 : lk [a, p] [w, Value.pred q] p = .pred q := by
    simp only [lk, List.zip_cons_cons, List.zip_nil_right, List.lookup, beq_false_of_ne hp,
      beq_self_eq_true, Option.getD_some]
  have hb : w.bytes = 4 := by
    obtain ⟨rfl, hx⟩ := h
    induction x using EReal.rec with
    | bot => rw [erealValue_bot]; rfl
    | coe r => rw [erealValue_coe]; rfl
    | top => exact absurd rfl hx
  have hi : Value.bits 32 (BitVec.ofNat 64 4286578688) = negInf32 := rfl
  cases q
  · have e : coreF (.int ⟨.selp, .float .f32, false, [some d],
        [.reg a, .f32imm 4286578688, .reg p]⟩) [a, p] [w, .pred false] = .ok negInf32 := by
      simp only [coreF, coreW, oVal, h2, bind, Except.bind, oBits, DType.width, Bool.false_eq_true,
        ↓reduceIte, pure, Except.pure]
      rfl
    rw [okVal_ok e]
    exact ev_bot
  · have e : coreF (.int ⟨.selp, .float .f32, false, [some d],
        [.reg a, .f32imm 4286578688, .reg p]⟩) [a, p] [w, .pred true] = .ok w := by
      simp only [coreF, coreW, oVal, h1, h2, bind, Except.bind, DType.width, ↓reduceIte, pure,
        Except.pure, hb]
    rw [okVal_ok e]
    exact h
end
end PTX.Kernels.InklingRelDecode.Proof.Softmax.Data
