-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Regs
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-!
Normal forms for the integer arithmetic the semantics computes: everything is turned
into `Nat` arithmetic on `toNat` and handed to `omega`.
-/

namespace PTX.Proof
open PTX

/-! ### Normal form of integer values

Every 64-bit value the integer rules compute, from register facts `BitVec.ofNat 64 n`,
immediates, special registers and shared symbols, is rewritten bottom-up to
`BitVec.ofNat 64 e` with `e` a `Nat` expression, by the fixed rules below (one per
operation of `Core/Thread/Local.lean`). An equation between two values then becomes
`e % 2^64 = e' % 2^64`, which `omega` decides; that equation is the only arithmetic content
(absence of wrap-around).

The rules are proved by rewriting with the `BitVec` lemmas, never stated as those lemmas:
core proves `BitVec.toNat_add` and the like by `rfl`, so `simp` would apply them as
definitional steps and leave the kernel to check `(x + y).toNat ≡ (x.toNat + y.toNat) % 2^64`
by unfolding, once per unit of a literal operand such as `622592`. -/

theorem nf_toNat (w a : Nat) : (BitVec.ofNat w a).toNat = a % 2 ^ w := by
  rw [BitVec.toNat_ofNat]
theorem nf_ofInt (i : Int) : BitVec.ofInt 64 i = BitVec.ofNat 64 (i % 18446744073709551616).toNat :=
    by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofInt, BitVec.toNat_ofNat]; omega
theorem nf_trunc (w a : Nat) :
    truncBits w (BitVec.ofNat 64 a) = BitVec.ofNat 64 (a % 18446744073709551616 % 2 ^ w) := by
  rw [truncBits, BitVec.toNat_ofNat]
theorem nf_add (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]; omega
theorem nf_mul (a b : Nat) : BitVec.ofNat 64 a * BitVec.ofNat 64 b = BitVec.ofNat 64 (a * b) := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, ← Nat.mul_mod]
theorem nf_sub (a b : Nat) : BitVec.ofNat 64 a - BitVec.ofNat 64 b =
    BitVec.ofNat 64 (18446744073709551616 - b % 18446744073709551616 + a) := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]; omega
theorem nf_neg (a : Nat) : -BitVec.ofNat 64 a =
    BitVec.ofNat 64 (18446744073709551616 - a % 18446744073709551616) := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_neg, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
theorem nf_shl (a s : Nat) : BitVec.ofNat 64 a <<< s = BitVec.ofNat 64 (a * 2 ^ s) := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
theorem nf_shr (a s : Nat) : BitVec.ofNat 64 a >>> s =
    BitVec.ofNat 64 (a % 18446744073709551616 / 2 ^ s) := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  exact (Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _)
    (Nat.mod_lt _ (Nat.two_pow_pos 64)))).symm
theorem nf_and (a b : Nat) : BitVec.ofNat 64 a &&& BitVec.ofNat 64 b =
    BitVec.ofNat 64 (a % 18446744073709551616 &&& b % 18446744073709551616) := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (lt_of_le_of_lt Nat.and_le_left (Nat.mod_lt _ (Nat.two_pow_pos 64)))).symm
theorem nf_or (a b : Nat) : BitVec.ofNat 64 a ||| BitVec.ofNat 64 b =
    BitVec.ofNat 64 (a % 18446744073709551616 ||| b % 18446744073709551616) := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (Nat.or_lt_two_pow (Nat.mod_lt _ (Nat.two_pow_pos 64))
    (Nat.mod_lt _ (Nat.two_pow_pos 64)))).symm
theorem nf_zero : (0 : BitVec 64) = BitVec.ofNat 64 0 := rfl
/-- Collapse chains of truncations to one. -/
theorem nf_mod64_32 (a : Nat) : a % 18446744073709551616 % 4294967296 = a % 4294967296 :=
  Nat.mod_mod_of_dvd a (by decide)
theorem nf_mod32_64 (a : Nat) : a % 4294967296 % 18446744073709551616 = a % 4294967296 :=
  Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt a (by decide)) (by decide))
theorem nf_eq (a b : Nat) : BitVec.ofNat 64 a = BitVec.ofNat 64 b ↔
    a % 18446744073709551616 = b % 18446744073709551616 := by
  constructor
  · intro h; have := congrArg BitVec.toNat h; rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this
  · intro h; apply BitVec.eq_of_toNat_eq; rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat]

theorem land31 (a : Nat) : a &&& 31 = a % 32 := Nat.and_two_pow_sub_one_eq_mod a 5

/-- `or` of operands with disjoint bits (`x` a multiple of `4096`, `y < 4096`) is a sum. -/
theorem lor_4096 {x y : Nat} (hx : x % 4096 = 0) (hy : y < 4096) : x ||| y = x + y := by
  have e : x = 2 ^ 12 * (x / 2 ^ 12) := (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hx)).symm
  rw [e, ← Nat.two_pow_add_eq_or_of_lt (show y < 2 ^ 12 from hy)]

/-! ### Instruction types

The integer, move and conversion instructions carry their type as a `DType`, and the semantic
functions read its width (`DType.width`) and its integer kind (`DType.kind?`) from it. The normal
form evaluates both for the literal types of a decoded program, and evaluates the signedness test
`kind? == some .s` of `execInt` and the comparison kind `kind?.getD .b` of `setp`. A width is
used both in a value and in the decision procedure of a comparison, for example in
`if s.toNat ≥ w then 0 else x >>> s.toNat` of a shift; `simp` rewrites the width in the value but
leaves the instance of the comparison unchanged, so a lemma stated with the literal width no
longer matches the term. `ty_eval` therefore first rewrites every integer width with `rw`, which
abstracts the instances too; `seg_fp` applies it to each value a segment computes. -/

/-- The width of `DType.int k w` is `w`. -/
theorem _root_.PTX.DType.width_int (k : IType) (w : Nat) : (DType.int k w).width = w := rfl

/-- The signedness test of a signed type. -/
theorem kind_s_beq_s : (some IType.s == some IType.s) = true := rfl

/-- The signedness test of an unsigned type. -/
theorem kind_u_beq_s : (some IType.u == some IType.s) = false := rfl

/-- The signedness test of an untyped (bit-size) type. -/
theorem kind_b_beq_s : (some IType.b == some IType.s) = false := rfl

/-- Evaluate the width and the integer kind of the instruction types in the goal: every integer
width by `rw` (the instances of comparisons included), then the remaining widths and kinds. -/
macro "ty_eval" : tactic =>
  `(tactic| ((repeat rw [PTX.DType.width_int]) <;>
    try simp only [PTX.DType.width, PTX.DType.kind?]))

/-- The rules of the normal form, as one simp set. -/
syntax "nf_simp" (" [" Lean.Parser.Tactic.simpLemma,* "]")? (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| nf_simp $[[$extra,*]]? $[$loc]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| simp only [b32, b64, Value.bits.injEq, Value.pred.injEq, true_and, nf_toNat, nf_ofInt,
      nf_trunc, nf_add, nf_mul, nf_sub, nf_neg, nf_shl, nf_shr, nf_and, nf_or, nf_zero, nf_eq,
      nf_mod64_32, nf_mod32_64, Nat.mod_mod,
      sregValue, land31,
      -- instruction types
      PTX.DType.width, PTX.DType.kind?, Option.getD_some, Option.getD_none, kind_s_beq_s,
      kind_u_beq_s, kind_b_beq_s,
      -- constants: `simp only` evaluates ground arithmetic only with these
      Nat.reducePow, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceDiv,
      Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceEqDiff,
      Int.reduceMod, Int.reduceToNat, Int.reduceNeg, ge_iff_le, ↓reduceIte, Bool.false_eq_true,
      $extra,*] $[$loc]?)

/-- An equation between a computed and a stated integer value: the given lemmas on the
computed form, then the normal form, then `omega`. -/
syntax "norm_bits" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| norm_bits $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| ((try simp only [$extra,*]); all_goals ((try nf_simp [$extra,*]); all_goals omega)))

/-- An equation between a computed and a stated predicate (`setp`): normal form of both
operands, the comparison as a statement about integers, then `omega`. -/
syntax "norm_cmp" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| norm_cmp $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (
      try simp only [$extra,*]
      all_goals try nf_simp [PTX.compare, toSigned, decide_eq_decide, ne_eq, decide_not,
        Bool.not_not,
        Bool.not_inj_iff, $extra,*]
      all_goals (try split_ifs)
      all_goals omega))

/-- Close one equation `computed = stated` left by `holds_facts`, by the shape of the value:
syntactically equal, an integer (`norm_bits`), a predicate (`norm_cmp`), or a float or
packed pair (unfold the given definitions, then evaluate). Each branch starts with a `show`
that fails at once on a value of another shape. -/
syntax "close_fact" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| close_fact $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| first
      | with_reducible rfl
      | (show Value.bits _ _ = _; norm_bits [$extra,*]; done)
      | (show Value.pred _ = _; norm_cmp [$extra,*])
      | (show Value.float _ _ = _; (try simp only [fl, $extra,*]); first | done | rfl)
      | (show Value.pair _ _ = _; (try simp only [fl, h16, $extra,*]); first | done | rfl))

end PTX.Proof
