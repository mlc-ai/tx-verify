-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Bits

@[expose] public section

/-!
# Packs of two 32-bit integer halves

`mov.b64 d, {lo, hi}` of two 32-bit integer registers holds the 64-bit integer `lo + hi·2^32`
(`join_bits32`), when the halves' values are below `2^32`. `join_close` closes a register fact
`joinValue x y = .bits 64 (BitVec.ofNat 64 (a + b·2^32))` by the normal form of each half.
-/

namespace PTX.Proof
open PTX

/-- The halves `a` and `b` of `x ||| y <<< 32` make the integer `a + b·2^32`. -/
theorem or_shl32 {x y : BitVec 64} {a b : Nat} (hx : x = BitVec.ofNat 64 a)
    (hy : y = BitVec.ofNat 64 b) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    x ||| y <<< 32 = BitVec.ofNat 64 (a + b * 2 ^ 32) := by
  subst hx hy
  have he : a ||| b * 2 ^ 32 = a + b * 2 ^ 32 := by
    rw [Nat.or_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt ha]
    omega
  have h1 : a % 18446744073709551616 = a := Nat.mod_eq_of_lt (by omega)
  have h2 : b * 2 ^ 32 % 18446744073709551616 = b * 2 ^ 32 := Nat.mod_eq_of_lt (by omega)
  rw [nf_shl, nf_or, h1, h2, he]

/-- The pack of two 32-bit integer halves `a` and `b` is the integer `a + b·2^32`. -/
theorem join_bits32 {x y : BitVec 64} {a b : Nat} (hx : x = BitVec.ofNat 64 a)
    (hy : y = BitVec.ofNat 64 b) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    joinValue (.bits 32 x) (.bits 32 y) = .bits 64 (BitVec.ofNat 64 (a + b * 2 ^ 32)) := by
  simp only [joinValue, and_self, Nat.reduceMul, Nat.reduceLeDiff, ↓reduceIte,
    or_shl32 hx hy ha hb]

/-- Close `joinValue x y = v` where `v` unfolds (by the given lemmas) to
`.bits 64 (BitVec.ofNat 64 (a + b·2^32))`, or the same with the pack already evaluated
(`.bits 64 (x ||| y <<< 32) = v`): each half's normal form (literal `Fin` and `Bool` tests
evaluated) and range by `omega`. It fails at once on a goal of another shape. -/
syntax "join_close" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| join_close $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (
      first
        | show PTX.joinValue _ _ = _
        | show Value.bits 64 (_ ||| _ <<< 32) = _
      simp only [b32, b64, PTX.joinValue, Value.bits.injEq, true_and, and_self,
        Nat.reduceMul, Nat.reduceLeDiff, ↓reduceIte, $extra,*]
      refine PTX.Proof.or_shl32 ?_ ?_ ?_ ?_
      all_goals first
        | omega
        | ((try simp only [Fin.isValue, Fin.reduceEq, decide_false, decide_true,
            Bool.or_false, Bool.or_true, Bool.false_eq_true, ↓reduceIte, Fin.coe_ofNat_eq_mod,
            Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, $extra,*]) <;>
          (try nf_simp) <;> omega)))

end PTX.Proof
