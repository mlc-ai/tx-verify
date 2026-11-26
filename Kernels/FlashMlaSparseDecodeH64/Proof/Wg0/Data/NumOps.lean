-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.Mask
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Value

@[expose] public section

/-! # Core's value of the valid-mask chain's integer instructions

The mask chain (`Gen/Mask.lean`, pcs 290-393) turns the mask word `n` (a 32-bit word,
"reads as") into the masked high-half score words. Each instruction's value (`coreF` of its
decoded form, with `okVal`) on the values the chain has: the halfwords and shifted words of `n`
(`w0m_v291`, ...), the sign bytes (`cvt.s8`, `bfe.s32`, `sinkW`), the single-bit tests (`and`,
`setp`) and the selects. The bit lemmas turn the tests into `Nat.testBit` of `n`. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Flow PTX.Proof PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen

noncomputable section

set_option linter.unusedSimpArgs false

/-- `cvt.u16.u32`. -/
def w0mCvtU16 (dd a : Nat) : Op :=
  .cvt { dst := .int .u 16, src := .int .u 32, d := dd, srcs := [.reg a] }

/-- `cvt.s8.s32` with a 16-bit sign extension. -/
def w0mCvtS8 (dd a : Nat) : Op :=
  .cvt { dst := .int .s 8, src := .int .s 32, d := dd, ext := MemExt.sign 16, srcs := [.reg a] }

/-- The 16-bit sign extension of a byte. -/
def w0mSx (z : Nat) : Nat := if z < 128 then z else z + 65280

theorem w0m_cvt_u16 {dd a y : Nat} :
    coreF (w0mCvtU16 dd a) [a] [.bits 32 (BitVec.ofNat 64 y)] =
      .ok (.bits 16 (BitVec.ofNat 64 (y % 65536))) := by
  simp [w0mCvtU16, coreF, coreW, lk, cvtW, oVal, oBits, truncBits, DType.width, pure,
    Except.pure, bind, Except.bind]

theorem w0m_cvt_s8 {dd a y : Nat} :
    coreF (w0mCvtS8 dd a) [a] [.bits 32 (BitVec.ofNat 64 y)] =
      .ok (.bits 16 (BitVec.ofNat 64 (w0mSx (y % 256)))) := by
  simp [w0mCvtS8, w0mSx, coreF, coreW, lk, cvtW, oVal, oBits, truncBits, DType.width, pure,
    Except.pure, bind, Except.bind, MemExt.extendBits, cvtIntBits, intOf, intBits, intSat,
    toSigned]
  congr 1
  split_ifs <;> omega

theorem w0m_shr {dd a y kn : Nat} {k : Int} (hkn : k = (kn : Int)) (hy : y < 2 ^ 32)
    (hk : kn < 32) :
    coreF (.int ⟨.shr, .int .u 32, false, [some dd], [.reg a, .imm k]⟩) [a]
      [.bits 32 (BitVec.ofNat 64 y)] = .ok (.bits 32 (BitVec.ofNat 64 (y / 2 ^ kn))) := by
  subst hkn
  simp [coreF, coreW, lk, oBits, truncBits, DType.width, DType.kind?, pure, Except.pure, bind,
    Except.bind]
  rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega)),
    Nat.mod_eq_of_lt (by omega : y < 4294967296), Nat.mod_eq_of_lt (by omega : kn < 4294967296)]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hd : y / 2 ^ kn ≤ y := Nat.div_le_self _ _
  rw [Nat.mod_eq_of_lt (by omega : y < 18446744073709551616),
    Nat.mod_eq_of_lt (by omega : kn < 18446744073709551616),
    Nat.mod_eq_of_lt (by omega : y / 2 ^ kn < 18446744073709551616)]

theorem w0m_bitsFrom_congr {w : Nat} {f g : Nat → Bool} (h : ∀ i < w, f i = g i) :
    bitsFrom w f = bitsFrom w g := by
  unfold bitsFrom
  have : ∀ l : List Nat, (∀ j ∈ l, f j = g j) →
      l.foldr (fun j acc => if f j then acc + 2 ^ j else acc) 0 =
        l.foldr (fun j acc => if g j then acc + 2 ^ j else acc) 0 := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons a l ih =>
      intro hl
      simp only [List.foldr_cons]
      rw [ih (fun j hj => hl j (List.mem_cons_of_mem a hj)), hl a List.mem_cons_self]
  exact this _ fun j hj => h j (List.mem_range.mp hj)

set_option maxRecDepth 100000 in
theorem w0m_bitsFrom_byte : ∀ b < 256,
    bitsFrom 32 (fun i => if i < 8 then b.testBit i else b.testBit 7) =
      if b < 128 then b else b + 4294967040 := by
  decide

/-- `bfe.s32 d, a, p, 8`: the sign-extended byte at bit `p`. -/
theorem w0m_bfe {a y p : Nat} (hy : y < 2 ^ 32) (hp : p + 8 ≤ 32) :
    bfeW .s 32 (.reg a) (.imm (p : Int)) (.imm 8) (lk [a] [.bits 32 (BitVec.ofNat 64 y)]) =
      .ok (.bits 32 (BitVec.ofNat 64 (if y / 2 ^ p % 256 < 128 then y / 2 ^ p % 256
        else y / 2 ^ p % 256 + 4294967040))) := by
  simp [bfeW, lk, oBits, truncBits, DType.width, pure, Except.pure, bind, Except.bind, bfeBits]
  rw [Nat.mod_eq_of_lt (by omega : p < 256), Nat.mod_eq_of_lt (by omega : y < 4294967296)]
  have hb : y / 2 ^ p % 256 < 256 := Nat.mod_lt _ (by norm_num)
  rw [← w0m_bitsFrom_byte _ hb]
  congr 1
  apply w0m_bitsFrom_congr
  intro i hi
  rw [show (256 : Nat) = 2 ^ 8 by norm_num, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
  have hp' : p % 256 = p := by omega
  by_cases h8 : i < 8
  · have hc : p + i ≤ 31 := by omega
    simp [h8, hp', hc, show i + p = p + i by omega]
    rw [Nat.mod_eq_of_lt (by omega : y < 18446744073709551616)]
  · simp [h8, hp']
    rw [Nat.mod_eq_of_lt (by omega : y < 18446744073709551616),
      show min (p + 7) 31 = 7 + p by omega]

theorem w0m_and_imm {dd a w y kn : Nat} {k : Int} (hkn : k = (kn : Int)) (hw : w = 16 ∨ w = 32)
    (hy : y < 2 ^ w) (hk : kn < 2 ^ w) :
    coreF (.int ⟨.and, .int .b w, false, [some dd], [.reg a, .imm k]⟩) [a]
      [.bits w (BitVec.ofNat 64 y)] = .ok (.bits w (BitVec.ofNat 64 (y &&& kn))) := by
  subst hkn
  rcases hw with rfl | rfl
  · simp [coreF, coreW, lk, logicW, oBits, truncBits, DType.width, pure, Except.pure, bind,
      Except.bind]
    rw [Nat.mod_eq_of_lt (by omega : y < 65536), Nat.mod_eq_of_lt (by omega : kn < 65536)]
  · simp [coreF, coreW, lk, logicW, oBits, truncBits, DType.width, pure, Except.pure, bind,
      Except.bind]
    rw [Nat.mod_eq_of_lt (by omega : y < 4294967296),
      Nat.mod_eq_of_lt (by omega : kn < 4294967296)]

theorem w0m_setp_eq0 {dd a w y : Nat} (hw : w = 16 ∨ w = 32) (hy : y < 2 ^ w) :
    coreF (.int ⟨.setp .eq none, .int .b w, false, [some dd], [.reg a, .imm 0]⟩) [a]
      [.bits w (BitVec.ofNat 64 y)] = .ok (.pred (decide (y = 0))) := by
  rcases hw with rfl | rfl <;>
  · simp [coreF, coreW, lk, oBits, truncBits, DType.width, pure, Except.pure, bind, Except.bind,
      PTX.compare, DType.kind?]
    omega

theorem w0m_setp_ne0 {dd a y : Nat} (hy : y < 2 ^ 32) :
    coreF (.int ⟨.setp .ne none, .int .b 32, false, [some dd], [.reg a, .imm 0]⟩) [a]
      [.bits 32 (BitVec.ofNat 64 y)] = .ok (.pred (decide (y ≠ 0))) := by
  simp [coreF, coreW, lk, oBits, truncBits, DType.width, pure, Except.pure, bind, Except.bind,
    PTX.compare, DType.kind?]
  omega

theorem w0m_setp_gt16 {dd a y : Nat} (hy : y < 2 ^ 16) :
    coreF (.int ⟨.setp .gt none, .int .s 16, false, [some dd], [.reg a, .imm (-1)]⟩) [a]
      [.bits 16 (BitVec.ofNat 64 y)] = .ok (.pred (decide (y < 2 ^ 15))) := by
  simp [coreF, coreW, lk, oBits, truncBits, DType.width, pure, Except.pure, bind, Except.bind,
    PTX.compare, DType.kind?, toSigned]
  split_ifs <;> omega

theorem w0m_setp_gt32 {dd a y : Nat} (hy : y < 2 ^ 32) :
    coreF (.int ⟨.setp .gt none, .int .s 32, false, [some dd], [.reg a, .imm (-1)]⟩) [a]
      [.bits 32 (BitVec.ofNat 64 y)] = .ok (.pred (decide (y < 2 ^ 31))) := by
  simp [coreF, coreW, lk, oBits, truncBits, DType.width, pure, Except.pure, bind, Except.bind,
    PTX.compare, DType.kind?, toSigned]
  split_ifs <;> omega

theorem w0m_selp_hi {dd a p : Nat} (hap : a ≠ p) (v : Value) (hv : v.bytes = 4) (q : Bool) :
    coreF (.int ⟨.selp, .int .b 32, false, [some dd], [.reg a, .imm (-8388608), .reg p]⟩) [a, p]
      [v, .pred q] = .ok (if q then v else w0NegInf) := by
  have e : (p == a) = false := by simpa using hap.symm
  cases q <;> simp [coreF, coreW, lk, oVal, oBits, List.lookup, e, hv, truncBits, DType.width,
    Value.bytes, w0NegInf, pure, Except.pure, bind, Except.bind]

theorem w0m_selp_lo {dd a p : Nat} (hap : a ≠ p) (v : Value) (hv : v.bytes = 4) (q : Bool) :
    coreF (.int ⟨.selp, .int .b 32, false, [some dd], [.imm (-8388608), .reg a, .reg p]⟩) [a, p]
      [v, .pred q] = .ok (if q then w0NegInf else v) := by
  have e : (p == a) = false := by simpa using hap.symm
  cases q <;> simp [coreF, coreW, lk, oVal, oBits, List.lookup, e, hv, truncBits, DType.width,
    Value.bytes, w0NegInf, pure, Except.pure, bind, Except.bind]

/-! ### The bit tests -/

theorem w0m_and_pow (y b : Nat) : y &&& 2 ^ b = 0 ↔ ¬ y.testBit b = true := by
  constructor
  · intro h hb
    have := congrArg (fun z => z.testBit b) h
    simp [Nat.testBit_and, hb] at this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases hi : b = i
    · subst hi; simp [h]
    · simp [hi]

theorem w0m_bitA {y k n : Nat} (hy : y = n / 2 ^ k) : y &&& 1 ≠ 0 ↔ n.testBit k = true := by
  subst hy
  have h := w0m_and_pow (n / 2 ^ k) 0
  simp only [pow_zero, Nat.testBit_div_two_pow, Nat.zero_add] at h
  rw [Ne, h]; simp

theorem w0m_bitB {y k b n : Nat} (hy : y = n / 2 ^ k % 65536) (hb : b < 16) :
    y &&& 2 ^ b = 0 ↔ ¬ n.testBit (k + b) = true := by
  subst hy
  rw [w0m_and_pow, show (65536 : Nat) = 2 ^ 16 by norm_num, Nat.testBit_mod_two_pow,
    Nat.testBit_div_two_pow, Nat.add_comm b k]
  simp [hb]

theorem w0m_bitC {k n : Nat} :
    w0mSx (n / 2 ^ k % 256) < 2 ^ 15 ↔ ¬ n.testBit (k + 7) = true := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  simp only [w0mSx, decide_eq_true_eq]
  split_ifs <;> omega

theorem w0m_bitD {n : Nat} (hn : n < 2 ^ 32) : n < 2 ^ 31 ↔ ¬ n.testBit 31 = true := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  simp only [decide_eq_true_eq]
  omega

theorem w0m_sel {c : Prop} [Decidable c] {d : Bool} (h : c ↔ d = true) (x y : Value) :
    (if decide c = true then x else y) = if d = true then x else y := by
  simp [h]

theorem w0m_sel' {c : Prop} [Decidable c] {d : Bool} (h : c ↔ ¬ d = true) (x y : Value) :
    (if decide c = true then x else y) = if d = true then y else x := by
  by_cases hd : d = true <;> simp [h, hd]

/-! ### The four kinds of columns

A column of the mask chain tests one bit of the word: the lowest bit of a byte (`and.b32`,
`setp.ne`, `selp`), bits 1-6 (`and.b16`, `setp.eq`, `selp`), the top bit of a byte (`cvt.s8`,
`setp.gt.s16`) and bit 31 (`setp.gt.s32`). -/

theorem w0m_okVal (d : Value) (x : Value) : okVal d (.ok x) = x := rfl

theorem w0m_ok_sel_hi {d3 a p : Nat} (hap : a ≠ p) (v : Value) (hv : v.bytes = 4) (q : Bool) :
    okVal (.bits 32 0) (coreF (.int ⟨.selp, .int .b 32, false, [some d3],
      [.reg a, .imm (-8388608), .reg p]⟩) [a, p] [v, .pred q]) =
      if q then v else w0NegInf := by
  rw [w0m_selp_hi hap v hv q]; rfl

theorem w0m_ok_sel_lo {d3 a p : Nat} (hap : a ≠ p) (v : Value) (hv : v.bytes = 4) (q : Bool) :
    okVal (.bits 32 0) (coreF (.int ⟨.selp, .int .b 32, false, [some d3],
      [.imm (-8388608), .reg a, .reg p]⟩) [a, p] [v, .pred q]) =
      if q then w0NegInf else v := by
  rw [w0m_selp_lo hap v hv q]; rfl

theorem w0m_colA {d1 d2 d3 a1 a2 a p n : Nat} {src v : Value} (hn : n < 2 ^ 32) {k : Nat}
    (hs : src = .bits 32 (BitVec.ofNat 64 (n / 2 ^ k))) (hap : a ≠ p) (hv : v.bytes = 4) :
    okVal (.bits 32 0) (coreF (.int ⟨.selp, .int .b 32, false, [some d3],
      [.reg a, .imm (-8388608), .reg p]⟩) [a, p] [v,
      okVal (.bits 32 0) (coreF (.int ⟨.setp .ne none, .int .b 32, false, [some d2],
        [.reg a2, .imm 0]⟩) [a2] [okVal (.bits 32 0) (coreF (.int ⟨.and, .int .b 32, false,
        [some d1], [.reg a1, .imm 1]⟩) [a1] [src])])]) =
      if n.testBit k = true then v else w0NegInf := by
  have hy : n / 2 ^ k < 2 ^ 32 := lt_of_le_of_lt (Nat.div_le_self _ _) hn
  subst hs
  rw [w0m_and_imm (k := 1) (kn := 1) rfl (by simp) hy (by norm_num)]
  simp only [w0m_okVal]
  rw [w0m_setp_ne0 (lt_of_le_of_lt Nat.and_le_right (by norm_num))]
  simp only [w0m_okVal]
  rw [w0m_ok_sel_hi hap v hv]
  exact w0m_sel (w0m_bitA rfl) _ _

theorem w0m_colB {d1 d2 d3 a1 a2 a p n : Nat} {src v : Value} {k b : Nat}
    {km : Int} (hkm : km = ((2 ^ b : Nat) : Int)) (hb : b < 16)
    (hs : src = .bits 16 (BitVec.ofNat 64 (n / 2 ^ k % 65536))) (hap : a ≠ p)
    (hv : v.bytes = 4) :
    okVal (.bits 32 0) (coreF (.int ⟨.selp, .int .b 32, false, [some d3],
      [.imm (-8388608), .reg a, .reg p]⟩) [a, p] [v,
      okVal (.bits 32 0) (coreF (.int ⟨.setp .eq none, .int .b 16, false, [some d2],
        [.reg a2, .imm 0]⟩) [a2] [okVal (.bits 32 0) (coreF (.int ⟨.and, .int .b 16, false,
        [some d1], [.reg a1, .imm km]⟩) [a1] [src])])]) =
      if n.testBit (k + b) = true then v else w0NegInf := by
  have hy : n / 2 ^ k % 65536 < 2 ^ 16 := by omega
  subst hs
  rw [w0m_and_imm hkm (by simp) hy (Nat.pow_lt_pow_right (by norm_num) hb)]
  simp only [w0m_okVal]
  rw [w0m_setp_eq0 (by simp) (lt_of_le_of_lt Nat.and_le_left hy)]
  simp only [w0m_okVal]
  rw [w0m_ok_sel_lo hap v hv]
  exact w0m_sel' (w0m_bitB rfl hb) _ _

theorem w0m_colC {d2 d3 a2 a p n : Nat} {src v : Value} {k : Nat}
    (hs : src = .bits 16 (BitVec.ofNat 64 (w0mSx (n / 2 ^ k % 256)))) (hap : a ≠ p)
    (hv : v.bytes = 4) :
    okVal (.bits 32 0) (coreF (.int ⟨.selp, .int .b 32, false, [some d3],
      [.imm (-8388608), .reg a, .reg p]⟩) [a, p] [v,
      okVal (.bits 32 0) (coreF (.int ⟨.setp .gt none, .int .s 16, false, [some d2],
        [.reg a2, .imm (-1)]⟩) [a2] [src])]) =
      if n.testBit (k + 7) = true then v else w0NegInf := by
  subst hs
  rw [w0m_setp_gt16 (by unfold w0mSx; split_ifs <;> omega)]
  simp only [w0m_okVal]
  rw [w0m_ok_sel_lo hap v hv]
  exact w0m_sel' w0m_bitC _ _

theorem w0m_colD {d2 d3 a2 a p n : Nat} {src v : Value} (hn : n < 2 ^ 32)
    (hs : src = .bits 32 (BitVec.ofNat 64 n)) (hap : a ≠ p) (hv : v.bytes = 4) :
    okVal (.bits 32 0) (coreF (.int ⟨.selp, .int .b 32, false, [some d3],
      [.imm (-8388608), .reg a, .reg p]⟩) [a, p] [v,
      okVal (.bits 32 0) (coreF (.int ⟨.setp .gt none, .int .s 32, false, [some d2],
        [.reg a2, .imm (-1)]⟩) [a2] [src])]) =
      if n.testBit 31 = true then v else w0NegInf := by
  subst hs
  rw [w0m_setp_gt32 hn]
  simp only [w0m_okVal]
  rw [w0m_ok_sel_lo hap v hv]
  exact w0m_sel' (w0m_bitD hn) _ _

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
