-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.Sm
public import Lemmas.Flow.SignedBits
public import Lemmas.Flow.FloatRun

@[expose] public section

/-! # Tools of the softmax region's segment proofs

The register table of a state (`sm_vals`), the closing of one equation between a computed and a
stated value (`sm_close`: integers by the normal form of `Lemmas.Flow.Bits` with a discharger
that proves the range side goals of `Nat.mod_eq_of_lt` by `omega`, predicates by the comparison
normal form, packed pairs argument by argument), the facts about the thread index the code's bit
operations need, and the signed wide multiplication the bias row pointer is built with. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The value table at a literal register, evaluated. -/
macro "sm_vals" : tactic =>
  `(tactic| simp only [valueOf, PTX.Flow.lookupLit, Option.getD_some, Option.getD_none])

/-- A subtraction that does not wrap. -/
theorem sub_wrap64 (a b : Nat) (h : b ≤ a) (ha : a < 18446744073709551616) :
    (18446744073709551616 - b + a) % 18446744073709551616 = a - b := by omega

theorem toSigned32_ofNat (a : Nat) :
    toSigned 32 (truncBits 32 (BitVec.ofNat 64 a)) =
      if a % 2 ^ 32 < 2 ^ 31 then ((a % 2 ^ 32 : Nat) : Int)
      else ((a % 2 ^ 32 : Nat) : Int) - 2 ^ 32 := by
  simp only [toSigned, truncBits, BitVec.toNat_ofNat]
  have h1 : a % 2 ^ 64 % 2 ^ 32 = a % 2 ^ 32 := Nat.mod_mod_of_dvd a (by decide)
  have h2 : a % 2 ^ 32 % 2 ^ 64 = a % 2 ^ 32 := Nat.mod_eq_of_lt (by
    have := Nat.mod_lt a (show 0 < 2 ^ 32 by decide); omega)
  have h3 : a % 2 ^ 32 % 2 ^ 32 = a % 2 ^ 32 := Nat.mod_mod _ _
  simp only [h1, h2, h3]

/-- `cvt.s64.s32` of a 32-bit word is its sign extension `sxw`. -/
theorem cvt_s64_s32 (a : Nat) :
    MemExt.same.extendBits 64 (cvtIntBits false IType.s 64 IType.s 32
      (truncBits 32 (BitVec.ofNat 64 a))) = b64 (sxw a) := by
  simp only [MemExt.extendBits_same, cvtIntBits, intSat, intOf, intBits, ite_true,
    Bool.not_false, b64]
  rw [toSigned32_ofNat]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  unfold sxw
  have h := Nat.mod_lt a (show 0 < 2 ^ 32 by decide)
  split_ifs with h1 <;> push_cast <;> omega

/-- The normal form of integer values, with range side goals discharged by `omega`. -/
syntax "sm_nf" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| sm_nf $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| simp (disch := omega) only [b32, b64, b16, Value.bits.injEq, Value.pred.injEq,
      true_and,
      nf_toNat, nf_ofInt, nf_trunc, nf_add, nf_mul, nf_sub, nf_neg, nf_shl, nf_shr, nf_and, nf_or,
      nf_zero, nf_eq, nf_mod64_32, nf_mod32_64, Nat.mod_mod, sregValue, land31, PTX.DType.width,
      PTX.DType.kind?, Option.getD_some, Option.getD_none, kind_s_beq_s, kind_u_beq_s,
      kind_b_beq_s, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub,
      Nat.reduceDiv, Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff,
      Int.reduceMod, Int.reduceToNat, Int.reduceNeg, ge_iff_le, ↓reduceIte, Bool.false_eq_true,
      Nat.mod_eq_of_lt, sub_wrap64, $extra,*])

/-- An equation between a computed and a stated integer value. -/
syntax "sm_bits" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| sm_bits $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| ((try simp only [$extra,*]); all_goals ((try sm_nf [$extra,*]); all_goals omega)))

/-- An equation between a computed and a stated predicate. -/
syntax "sm_cmp" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| sm_cmp $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (
      (try simp only [Value.pred.injEq])
      all_goals (try rw [Bool.eq_iff_iff])
      all_goals (try sm_nf [PTX.compare, toSigned, Bool.and_eq_true, decide_eq_true_eq,
        Bool.not_eq_true', decide_not, ne_eq, decide_eq_false_iff_not, Int.natCast_inj,
        Nat.cast_zero, $extra,*])
      all_goals (try split_ifs)
      all_goals omega))

/-- Close one equation `computed = stated` left by `holds_facts`, by the shape of the value. -/
syntax "sm_close" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| sm_close $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| first
      | with_reducible rfl
      | (with_reducible exact cvt_s64_s32 _)
      | (show Value.bits _ _ = _; sm_bits [$extra,*]; done)
      | (show Value.pred _ = _; sm_cmp [$extra,*]; done)
      | (show Value.bits _ _ = _; norm_signed [intOf, intBits, eq_self, $extra,*]; done)
      | (show PTX.joinValue _ _ = _; congr 1 <;> sm_bits [$extra,*]; done)
      | (show Value.float _ _ = _; (try simp only [fl, $extra,*]); first | done | rfl)
      | (show Value.pair _ _ = _; (try simp only [fl, h16, $extra,*]); first | done | rfl)
      | decide +kernel)

/-! ### The thread index

The bit operations of the code on the thread index `T` of a softmax thread (below 128). -/

theorem land255 (a : Nat) : a &&& 255 = a % 256 := Nat.and_two_pow_sub_one_eq_mod a 8
theorem land127 (a : Nat) : a &&& 127 = a % 128 := Nat.and_two_pow_sub_one_eq_mod a 7
theorem land12 (t : Nat) (h : t < 128) : t * 4 &&& 12 = t % 4 * 4 := by
  revert t h; decide +kernel

theorem tid_and96 (t : Nat) (h : t < 128) : t &&& 96 = t / 32 % 4 * 32 := by
  revert t h; decide +kernel
theorem or_disj16 (a b : Nat) (ha : a % 16 = 0) (hb : b < 16) : a ||| b = a + b := by
  obtain ⟨q, rfl⟩ : ∃ q, a = 16 * q := ⟨a / 16, by omega⟩
  have h := Nat.two_pow_add_eq_or_of_lt (show b < 2 ^ 4 from hb) q
  have h16 : (2 : Nat) ^ 4 = 16 := by norm_num
  rw [h16] at h
  exact h.symm

theorem tid_and64 (t : Nat) (h : t < 128) : t * 4 &&& 64 = t / 16 % 2 * 64 := by
  revert t h; decide +kernel

theorem tid_and15 (t : Nat) (h : t < 128) : t &&& 15 = t % 16 := by
  revert t h; decide +kernel

/-- The clamped block count is a 32-bit word. -/
theorem Ent.Ok.r26_lt {e : Ent} (h : e.Ok) : e.r26 < 2 ^ 32 := by
  have := h.r25
  rw [h.r26]
  split_ifs <;> omega

/-- The block of an iteration up to `num_iters`, and the block after it, are below `2 ^ 31`. -/
theorem Ent.Ok.blk_lt {e : Ent} (h : e.Ok) {i : Nat} (hi : i ≤ e.r26) :
    blkOf e i + e.splits < 2 ^ 31 := by
  have := Nat.mul_le_mul_right e.splits hi
  have := h.blk
  unfold blkOf
  omega

/-! ### The signed wide multiplication

`mul.wide.s32` reads both operands as signed words and writes their product as a 64-bit word. With
`sxw` the sign extension as a number below `2 ^ 64`, the product is `sxw a * sxw b % 2 ^ 64`. -/

theorem mulwide_s32 (a b : Nat) :
    truncBits 64 (BitVec.ofInt 64 (toSigned 32 (truncBits 32 (BitVec.ofNat 64 a)) *
      toSigned 32 (truncBits 32 (BitVec.ofNat 64 b)))) =
      BitVec.ofNat 64 (sxw a * sxw b % 2 ^ 64) := by
  rw [toSigned32_ofNat, toSigned32_ofNat]
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  have ha : ((sxw a : Nat) : Int) % 2 ^ 64 =
      (if a % 2 ^ 32 < 2 ^ 31 then ((a % 2 ^ 32 : Nat) : Int)
        else ((a % 2 ^ 32 : Nat) : Int) - 2 ^ 32) % 2 ^ 64 := by
    unfold sxw
    split_ifs <;> push_cast <;> omega
  have hb : ((sxw b : Nat) : Int) % 2 ^ 64 =
      (if b % 2 ^ 32 < 2 ^ 31 then ((b % 2 ^ 32 : Nat) : Int)
        else ((b % 2 ^ 32 : Nat) : Int) - 2 ^ 32) % 2 ^ 64 := by
    unfold sxw
    split_ifs <;> push_cast <;> omega
  generalize (if a % 2 ^ 32 < 2 ^ 31 then ((a % 2 ^ 32 : Nat) : Int)
      else ((a % 2 ^ 32 : Nat) : Int) - 2 ^ 32) = sa at *
  generalize (if b % 2 ^ 32 < 2 ^ 31 then ((b % 2 ^ 32 : Nat) : Int)
      else ((b % 2 ^ 32 : Nat) : Int) - 2 ^ 32) = sb at *
  have h : Int.ModEq (2 ^ 64) (sa * sb) ((sxw a : Int) * (sxw b : Int)) :=
    Int.ModEq.mul ha.symm hb.symm
  have h' : (sa * sb) % ((2 ^ 64 : Nat) : Int) = (((sxw a * sxw b) % 2 ^ 64 : Nat) : Int) := by
    push_cast
    exact h
  rw [h', Int.toNat_natCast]
  simp
/-! ### Evaluating a piece of the straight-line code -/

/-- Evaluate a piece of the setup code from `h` and close the facts of its end state. The
hypothesis `hT : g % L.block < 128` (a softmax thread) is in the context; the lemmas after `[`
unfold the definitions of the registers the piece writes (one stage of a pointer chain at a time,
so that the products of the chain stay atoms of `omega`). -/
syntax "sm_seg " term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| sm_seg $h $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| seg_fp $h using
      sm_vals
      all_goals sm_close [tid_and96 _ hT, tid_and15 _ hT, or_disj16, tid_and64 _ hT,
        Nat.and_one_is_mod, land255, land127, land12 _ hT, tokOf, row, remOf, half, rowValid,
        Nat.reduceMul, kind_s_beq_s, kind_u_beq_s, ↓reduceIte, mulwide_s32, $extra,*])

/-! `mad.wide.s32` reads its multiplier and its addend as signed words; the sum wraps at 64
bits. -/

theorem toSigned64_ofNat (c : Nat) :
    toSigned 64 (truncBits 64 (BitVec.ofNat 64 c)) =
      if c % 2 ^ 64 < 2 ^ 63 then ((c % 2 ^ 64 : Nat) : Int)
      else ((c % 2 ^ 64 : Nat) : Int) - 2 ^ 64 := by
  simp only [toSigned, truncBits, BitVec.toNat_ofNat]
  have h1 : c % 2 ^ 64 % 2 ^ 64 = c % 2 ^ 64 := Nat.mod_mod _ _
  simp only [h1]

theorem sxw_two : sxw 2 = 2 := by decide

theorem ofInt_two : BitVec.ofInt 64 2 = BitVec.ofNat 64 2 := rfl

theorem madwide_s32 (a b c : Nat) :
    intBits 64 (intOf IType.s 32 (truncBits 32 (BitVec.ofNat 64 a)) *
      intOf IType.s 32 (truncBits 32 (BitVec.ofNat 64 b)) +
      intOf IType.s 64 (truncBits 64 (BitVec.ofNat 64 c))) =
      BitVec.ofNat 64 ((sxw a * sxw b + c) % 2 ^ 64) := by
  simp only [intBits, intOf, ite_true]
  rw [toSigned32_ofNat, toSigned32_ofNat, toSigned64_ofNat]
  apply BitVec.eq_of_toNat_eq
  simp only [truncBits, BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  have ha : ((sxw a : Nat) : Int) % 2 ^ 64 =
      (if a % 2 ^ 32 < 2 ^ 31 then ((a % 2 ^ 32 : Nat) : Int)
        else ((a % 2 ^ 32 : Nat) : Int) - 2 ^ 32) % 2 ^ 64 := by
    unfold sxw
    split_ifs <;> push_cast <;> omega
  have hb : ((sxw b : Nat) : Int) % 2 ^ 64 =
      (if b % 2 ^ 32 < 2 ^ 31 then ((b % 2 ^ 32 : Nat) : Int)
        else ((b % 2 ^ 32 : Nat) : Int) - 2 ^ 32) % 2 ^ 64 := by
    unfold sxw
    split_ifs <;> push_cast <;> omega
  have hc : (c : Int) % 2 ^ 64 =
      (if c % 2 ^ 64 < 2 ^ 63 then ((c % 2 ^ 64 : Nat) : Int)
        else ((c % 2 ^ 64 : Nat) : Int) - 2 ^ 64) % 2 ^ 64 := by
    split_ifs <;> omega
  generalize (if a % 2 ^ 32 < 2 ^ 31 then ((a % 2 ^ 32 : Nat) : Int)
      else ((a % 2 ^ 32 : Nat) : Int) - 2 ^ 32) = sa at *
  generalize (if b % 2 ^ 32 < 2 ^ 31 then ((b % 2 ^ 32 : Nat) : Int)
      else ((b % 2 ^ 32 : Nat) : Int) - 2 ^ 32) = sb at *
  generalize (if c % 2 ^ 64 < 2 ^ 63 then ((c % 2 ^ 64 : Nat) : Int)
      else ((c % 2 ^ 64 : Nat) : Int) - 2 ^ 64) = sc at *
  have h : Int.ModEq (2 ^ 64) (sa * sb + sc) ((sxw a : Int) * (sxw b : Int) + (c : Int)) :=
    Int.ModEq.add (Int.ModEq.mul ha.symm hb.symm) hc.symm
  have h' : (sa * sb + sc) % ((2 ^ 64 : Nat) : Int) =
      (((sxw a * sxw b + c) % 2 ^ 64 : Nat) : Int) := by
    push_cast
    exact h
  rw [h', Int.toNat_natCast]
  simp
/-! ### Bounds of the pointer functions

Each stage of the bias pointer is a residue, so its bound holds whatever the stage's body. A
segment that reads a stage as a table value (a fact) and computes the next one needs the bound to
equate the code's wrapping arithmetic with the stage's definition. -/

theorem p260_lt (e : Ent) (T : Nat) : p260 e T < 2 ^ 64 := Nat.mod_lt _ (by decide)
theorem p9_lt (e : Ent) (T : Nat) : p9 e T < 2 ^ 64 := Nat.mod_lt _ (by decide)
theorem r345_lt (e : Ent) (T : Nat) : r345 e T < 2 ^ 32 := Nat.mod_lt _ (by decide)
theorem key_lt (n : Nat) : key n < 2 ^ 32 := Nat.mod_lt _ (by decide)

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
