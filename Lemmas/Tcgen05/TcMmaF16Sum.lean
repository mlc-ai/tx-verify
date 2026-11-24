-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tcgen05.TcMmaIdealSum

@[expose] public section

/-! # The ideal `kind::f16` MMA of either input format is a sum of products

`eval_sum` and `idealMmaElement_of_bytes` for `kind::f16` with an FP16 or a BF16 input format: an
element is a number when its two bytes are the two bytes of one, and an MMA without operand negation
evaluates to the sum of the products of its sixteen elements plus its old value. -/

namespace PTX.TcMma
open PTX

/-- The input formats of two bytes whose elements are numbers. -/
def Input16 (f : FloatFmt) : Prop := f = .f16 ∨ f = .bf16

/-- **An element whose two bytes are those of a number is that number.** -/
theorem element_of_bytes {f o : FloatFmt} (hf : Input16 f) {op : Operand}
    {bs : List (Option Byte)} {row k : Nat} {x : ℝ}
    (hb : ∀ z, z < 2 →
      bs[2 * (row * 16 + k) + z]? = some (some ((Value.float f x).byteAt z))) :
    Assumption.idealMmaElement (.f16 f o) op bs row k = .ok x := by
  have h0 := hb 0 (by decide)
  rw [Nat.add_zero] at h0
  have h2 := take_two h0 (hb 1 (by decide))
  have hb' : elementBytes (.f16 f o) bs row k = (Value.float f x).toBytes.map some := by
    have : ((Value.float f x).toBytes.map some) =
        [some ((Value.float f x).byteAt 0), some ((Value.float f x).byteAt 1)] := by
      rcases hf with rfl | rfl <;>
        simp [Value.toBytes, Value.bytes, FloatFmt.bytes, List.range_succ]
    rw [this, ← h2]
    simp [elementBytes, Kind.k, Kind.width, Nat.mul_comm]
  unfold Assumption.idealMmaElement
  dsimp only
  rw [hb']
  rcases hf with rfl | rfl <;>
    simp [rebuild, Value.toBytes, Value.byteAt, Value.bytes, FloatFmt.bytes, valFloat,
      List.range_succ] <;> rfl

/-- **The ideal dot product is the sum of the elements' products.** -/
theorem dot_sum {d : Descriptor} {f o : FloatFmt} (hk : d.kind = .f16 f o)
    (hna : d.negateA = false) (hnb : d.negateB = false) {a b : List (Option Byte)}
    {row col : Nat} {x y : Nat → ℝ} :
    ∀ n, (∀ k, k < n → Assumption.idealMmaElement (.f16 f o) .a a row k = .ok (x k)) →
      (∀ k, k < n → Assumption.idealMmaElement (.f16 f o) .b b col k = .ok (y k)) →
      Assumption.idealMmaDot d a b row col n = .ok (∑ k ∈ Finset.range n, x k * y k)
  | 0, _, _ => by simp [Assumption.idealMmaDot]; rfl
  | n + 1, ha, hb => by
    have hr := dot_sum hk hna hnb n (fun j hj => ha j (by omega)) (fun j hj => hb j (by omega))
    simp only [Assumption.idealMmaDot, hr, hk, ha n (by omega), hb n (by omega), hna, hnb,
      Finset.sum_range_succ]
    rfl

/-- **The ideal `kind::f16` MMA is a sum of products** plus its old value `prev`. -/
theorem eval_sum16 {name why : String} {sc : Assumption.IdealScope} {rest A : List Assumption}
    (hA : A = Assumption.idealReal name sc why :: rest) {d : Descriptor} {f : FloatFmt}
    (hk : d.kind = .f16 f .f32) (hs : d.kind ∈ sc.mma) (hv : Valid d) (hws : d.ws = false)
    (hna : d.negateA = false) (hnb : d.negateB = false) {a b : List (Option Byte)}
    (hla : a.length = Operand.bytes .a d) (hlb : b.length = Operand.bytes .b d) {row col : Nat}
    (hrow : row < d.m) (hcol : col < d.n) {x y : Nat → ℝ}
    (ha : ∀ k, k < 16 → Assumption.idealMmaElement (.f16 f .f32) .a a row k = .ok (x k))
    (hb : ∀ k, k < 16 → Assumption.idealMmaElement (.f16 f .f32) .b b col k = .ok (y k))
    {acc : Bool} {old : Option Value} {prev : ℝ}
    (hprev : Assumption.idealMmaAccumulator .f32 acc old = .ok prev) :
    eval A d acc a b old row col =
      .ok (.float .f32 (∑ k ∈ Finset.range 16, x k * y k + prev)) := by
  subst hA
  have hdot := dot_sum (d := d) hk hna hnb (a := a) (b := b) (row := row) (col := col) 16 ha hb
  have hr : (Assumption.idealReal name sc why).mmaRule d acc a b old row col =
      some (Assumption.execIdealMma d acc a b old row col) := by
    simp [Assumption.idealReal, hs]
  have hrow' : operandRow d row col = row := by simp [operandRow, hws]
  simp only [eval, hk, List.findSome?, hr, Option.getD_some]
  simp only [Assumption.execIdealMma, hk, hv, hrow, hcol, hla, hlb, and_self, hrow', Kind.k]
  simp [bind, Except.bind, pure, Except.pure, hdot, hprev]

end PTX.TcMma
