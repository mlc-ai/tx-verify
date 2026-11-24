-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.TcMmaIdealEval

@[expose] public section

/-! # The ideal `kind::f16` MMA is a sum of products

Under an ideal-real assumption whose scope holds `kind::f16` with an `.f32` accumulator, an MMA
without operand negation, outside the `.ws` M < 128 shapes, whose A elements of row `row` are
`x k` and whose B elements of column `col` are `y k` (`k < 16`), evaluates at `(row, col)` to the
single-precision float `Σ_{k < 16} x k · y k` plus its old value (`eval_sum`), or plus zero when
it does not accumulate. The ideal dot product of the first `n` elements is the sum of their
products (`idealMmaDot_sum`). -/

namespace PTX.TcMma
open PTX

/-- **The ideal dot product is the sum of the elements' products.** -/
theorem idealMmaDot_sum {d : Descriptor} {o : FloatFmt} (hk : d.kind = .f16 .f16 o)
    (hna : d.negateA = false) (hnb : d.negateB = false) {a b : List (Option Byte)}
    {row col : Nat} {x y : Nat → ℝ} :
    ∀ n, (∀ k, k < n → Assumption.idealMmaElement (.f16 .f16 o) .a a row k = .ok (x k)) →
      (∀ k, k < n → Assumption.idealMmaElement (.f16 .f16 o) .b b col k = .ok (y k)) →
      Assumption.idealMmaDot d a b row col n = .ok (∑ k ∈ Finset.range n, x k * y k)
  | 0, _, _ => by simp [Assumption.idealMmaDot]; rfl
  | n + 1, ha, hb => by
    have hr := idealMmaDot_sum hk hna hnb n (fun j hj => ha j (by omega))
      (fun j hj => hb j (by omega))
    simp only [Assumption.idealMmaDot, hr, hk, ha n (by omega), hb n (by omega), hna, hnb,
      Finset.sum_range_succ]
    rfl

/-- The old value of an accumulating MMA that reads a single-precision float `r`. -/
theorem idealMmaAccumulator_f32 (r : ℝ) :
    Assumption.idealMmaAccumulator .f32 true (some (.float .f32 r)) = .ok r := rfl

/-- The old value of an MMA that does not accumulate. -/
theorem idealMmaAccumulator_none (old : Option Value) :
    Assumption.idealMmaAccumulator .f32 false old = .ok 0 := rfl

/-- **The ideal `kind::f16` MMA is a sum of products** plus its old value `prev`. -/
theorem eval_sum {name why : String} {sc : Assumption.IdealScope} {rest A : List Assumption}
    (hA : A = Assumption.idealReal name sc why :: rest) {d : Descriptor}
    (hk : d.kind = .f16 .f16 .f32) (hs : d.kind ∈ sc.mma) (hv : Valid d) (hws : d.ws = false)
    (hna : d.negateA = false) (hnb : d.negateB = false) {a b : List (Option Byte)}
    (hla : a.length = Operand.bytes .a d) (hlb : b.length = Operand.bytes .b d) {row col : Nat}
    (hrow : row < d.m) (hcol : col < d.n) {x y : Nat → ℝ}
    (ha : ∀ k, k < 16 → Assumption.idealMmaElement (.f16 .f16 .f32) .a a row k = .ok (x k))
    (hb : ∀ k, k < 16 → Assumption.idealMmaElement (.f16 .f16 .f32) .b b col k = .ok (y k))
    {acc : Bool} {old : Option Value} {prev : ℝ}
    (hprev : Assumption.idealMmaAccumulator .f32 acc old = .ok prev) :
    eval A d acc a b old row col =
      .ok (.float .f32 (∑ k ∈ Finset.range 16, x k * y k + prev)) := by
  subst hA
  have hdot := idealMmaDot_sum (d := d) hk hna hnb (a := a) (b := b) (row := row) (col := col)
    16 ha hb
  have hr : (Assumption.idealReal name sc why).mmaRule d acc a b old row col =
      some (Assumption.execIdealMma d acc a b old row col) := by
    simp [Assumption.idealReal, hs]
  have hrow' : operandRow d row col = row := by simp [operandRow, hws]
  simp only [eval, hk, List.findSome?, hr, Option.getD_some]
  simp only [Assumption.execIdealMma, hk, hv, hrow, hcol, hla, hlb, and_self, hrow', Kind.k]
  simp [bind, Except.bind, pure, Except.pure, hdot, hprev]

end PTX.TcMma
