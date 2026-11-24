-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Bits
public import Lemmas.Arith.CeilDiv
public meta import Lean

@[expose] public section

/-! # Signed integer values in the normal form

A proof tool, extending the normal form of `Lemmas/Flow/Bits.lean` (values `BitVec.ofNat 64 e`
with `e` a `Nat` expression, closed by `omega`) to what the signed integer rules compute:

* `toSigned w` (`.s` comparisons, `shr.s`) is unfolded to its case split, which `split_ifs`
  and `omega` handle; `toSigned_eq_toInt32` relates it to the word model of
  `Lemmas/Arith/CeilDiv.lean`.
* `and` with a literal mask of one block of ones, `2^n - 2^k` (an `and.b32 r, x, -2^k`
  clearing the low bits), is not linear; the simproc `reduceLandMask` rewrites it to
  `a % 2^n / 2^k * 2^k` (`CeilDiv.land_highMask`).
* `norm_signed [lemmas]` closes an equation between a computed and a stated integer or
  predicate value with these rules: a signed shift, a signed comparison, the mask of a
  ceiling division (`CeilDiv`). -/

namespace PTX.Proof
open PTX

theorem toSigned_eq_toInt32 (a : Nat) :
    toSigned 32 (BitVec.ofNat 64 a) = CeilDiv.toInt32 a := by
  have h : a % 2 ^ 64 % 2 ^ 32 = a % 2 ^ 32 := Nat.mod_mod_of_dvd a (by decide)
  simp only [toSigned, CeilDiv.toInt32, FastDivmod.W, BitVec.toNat_ofNat, h]
  rfl

open Lean Meta Simp in
/-- `a &&& m` for a literal mask `m = 2^n - 2^k` (`0 ≤ k < n ≤ 64`): the bits `k … n-1` of
`a`, as `a % 2^n / 2^k * 2^k`. -/
simproc_decl reduceLandMask ((_ : Nat) &&& _) := fun e => do
  let_expr HAnd.hAnd _ _ _ _ a m := e | return .continue
  let some mv ← Nat.fromExpr? m | return .continue
  if mv == 0 then return .continue
  if (← Nat.fromExpr? a).isSome then return .continue
  let mut k := 0
  while (mv >>> k) % 2 == 0 do k := k + 1
  let hi := (mv >>> k) + 1
  let n := k + hi.log2
  unless 2 ^ n - 2 ^ k == mv && n ≤ 64 do return .continue
  let (pn, pk) := (mkNatLit (2 ^ n), mkNatLit (2 ^ k))
  let rhs ← mkAppM ``HMul.hMul #[← mkAppM ``HDiv.hDiv #[← mkAppM ``HMod.hMod #[a, pn], pk], pk]
  let hle ← mkDecideProof (← mkAppM ``LE.le #[mkNatLit k, mkNatLit n])
  let pf := mkApp4 (mkConst ``CeilDiv.land_highMask) a (mkNatLit n) (mkNatLit k) hle
  return .done { expr := rhs, proof? := some (← mkExpectedTypeHint pf (← mkEq e rhs)) }

/-- Close an equation between a computed and a stated integer or predicate value that the
signed rules computed: the normal form with `toSigned`, comparisons and literal masks unfolded,
a case split on the signs, then `omega`. -/
syntax "norm_signed" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| norm_signed $[[$extra,*]]?) => do
    let extra := (extra.map (·.getElems)).getD #[]
    `(tactic| (
      nf_simp [toSigned, PTX.compare, Nat.min_def, reduceLandMask, ← Bool.decide_and,
        ← Bool.decide_or, decide_eq_decide, decide_eq_true_eq, decide_eq_false_iff_not,
        ne_eq, $extra,*]
      all_goals (try split_ifs)
      all_goals omega))

end PTX.Proof
