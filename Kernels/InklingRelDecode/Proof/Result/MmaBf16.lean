-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Assumptions
public import Lemmas.Tcgen05.TcMmaIdealSum

@[expose] public section

/-!
# The ideal `kind::f16` MMA on bf16 elements

The kernel's MMAs are `kind::f16` with bf16 inputs and an f32 accumulator, the form
`[.f16 .bf16 .f32]` of `Assumptions.idealArith`. `Lemmas/Tcgen05/TcMmaIdealSum.lean` states the
sum-of-products reading for FP16 elements only; this file states it for bf16 elements:

* `idealMmaElement_of_bytes_bf16`: an element whose two bytes are the two bytes of one bf16 value
  is that value;
* `idealMmaDot_sum_bf16`, `eval_sum_bf16`: under the kernel's assumptions the MMA's value at
  `(row, col)` is the single-precision float `Σ_{k < 16} x k · y k` plus its old value
  (`eval_sum_bf16`), or plus zero when it does not accumulate.

Both are the FP16 statements with `.bf16` for `.f16`; the proofs are those of `TcMmaIdealSum`.
They are generic (nothing refers to the kernel but `Assumptions.all`) and listed for promotion to
`Lemmas/Tcgen05/TcMmaIdealSum.lean` in `MmaAll.lean`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Result.Mma
open PTX PTX.TcMma

noncomputable section

/-- **An element whose two bytes are those of a bf16 value is that value.** -/
theorem idealMmaElement_of_bytes_bf16 {o : FloatFmt} {op : TcMma.Operand}
    {bytes : List (Option Byte)} {row k : Nat} {x : ℝ}
    (hb : (bytes.drop (2 * (row * 16 + k))).take 2 = (Value.float .bf16 x).toBytes.map some) :
    Assumption.idealMmaElement (.f16 .bf16 o) op bytes row k = .ok x := by
  have hb' : elementBytes (.f16 .bf16 o) bytes row k = (Value.float .bf16 x).toBytes.map some := by
    rw [← hb]
    simp [elementBytes, Kind.k, Kind.width, Nat.mul_comm]
  unfold Assumption.idealMmaElement
  dsimp only
  rw [hb']
  simp [rebuild, Value.toBytes, Value.byteAt, Value.bytes, FloatFmt.bytes, valFloat,
    List.range_succ]
  rfl

/-- **The ideal dot product of bf16 elements is the sum of their products.** -/
theorem idealMmaDot_sum_bf16 {d : Descriptor} {o : FloatFmt} (hk : d.kind = .f16 .bf16 o)
    (hna : d.negateA = false) (hnb : d.negateB = false) {a b : List (Option Byte)}
    {row col : Nat} {x y : Nat → ℝ} :
    ∀ n, (∀ k, k < n → Assumption.idealMmaElement (.f16 .bf16 o) .a a row k = .ok (x k)) →
      (∀ k, k < n → Assumption.idealMmaElement (.f16 .bf16 o) .b b col k = .ok (y k)) →
      Assumption.idealMmaDot d a b row col n = .ok (∑ k ∈ Finset.range n, x k * y k)
  | 0, _, _ => by simp [Assumption.idealMmaDot]; rfl
  | n + 1, ha, hb => by
    have hr := idealMmaDot_sum_bf16 hk hna hnb n (fun j hj => ha j (by omega))
      (fun j hj => hb j (by omega))
    simp only [Assumption.idealMmaDot, hr, hk, ha n (by omega), hb n (by omega), hna, hnb,
      Finset.sum_range_succ]
    rfl

/-- **The ideal `kind::f16` MMA with bf16 inputs is a sum of products** plus its old value `prev`,
under any assumption list that starts with an ideal-real assumption whose scope has the form. -/
theorem eval_sum_bf16 {name why : String} {sc : Assumption.IdealScope} {rest A : List Assumption}
    (hA : A = Assumption.idealReal name sc why :: rest) {d : Descriptor}
    (hk : d.kind = .f16 .bf16 .f32) (hs : d.kind ∈ sc.mma) (hv : Valid d) (hws : d.ws = false)
    (hna : d.negateA = false) (hnb : d.negateB = false) {a b : List (Option Byte)}
    (hla : a.length = Operand.bytes .a d) (hlb : b.length = Operand.bytes .b d) {row col : Nat}
    (hrow : row < d.m) (hcol : col < d.n) {x y : Nat → ℝ}
    (ha : ∀ k, k < 16 → Assumption.idealMmaElement (.f16 .bf16 .f32) .a a row k = .ok (x k))
    (hb : ∀ k, k < 16 → Assumption.idealMmaElement (.f16 .bf16 .f32) .b b col k = .ok (y k))
    {acc : Bool} {old : Option Value} {prev : ℝ}
    (hprev : Assumption.idealMmaAccumulator .f32 acc old = .ok prev) :
    eval A d acc a b old row col =
      .ok (.float .f32 (∑ k ∈ Finset.range 16, x k * y k + prev)) := by
  subst hA
  have hdot := idealMmaDot_sum_bf16 (d := d) hk hna hnb (a := a) (b := b) (row := row)
    (col := col) 16 ha hb
  have hr : (Assumption.idealReal name sc why).mmaRule d acc a b old row col =
      some (Assumption.execIdealMma d acc a b old row col) := by
    simp [Assumption.idealReal, hs]
  have hrow' : operandRow d row col = row := by simp [operandRow, hws]
  simp only [eval, hk, List.findSome?, hr, Option.getD_some]
  simp only [Assumption.execIdealMma, hk, hv, hrow, hcol, hla, hlb, and_self, hrow', Kind.k]
  simp [bind, Except.bind, pure, Except.pure, hdot, hprev]

/-- The kernel's assumptions evaluate its `kind::f16` bf16 MMAs by the ideal-real rule: the sum of
the products of the 16 contraction elements plus the old value. -/
theorem eval_all {d : Descriptor} (hk : d.kind = .f16 .bf16 .f32) (hv : Valid d)
    (hws : d.ws = false) (hna : d.negateA = false) (hnb : d.negateB = false)
    {a b : List (Option Byte)} (hla : a.length = Operand.bytes .a d)
    (hlb : b.length = Operand.bytes .b d) {row col : Nat} (hrow : row < d.m) (hcol : col < d.n)
    {x y : Nat → ℝ}
    (ha : ∀ k, k < 16 → Assumption.idealMmaElement (.f16 .bf16 .f32) .a a row k = .ok (x k))
    (hb : ∀ k, k < 16 → Assumption.idealMmaElement (.f16 .bf16 .f32) .b b col k = .ok (y k))
    {acc : Bool} {old : Option Value} {prev : ℝ}
    (hprev : Assumption.idealMmaAccumulator .f32 acc old = .ok prev) :
    eval Assumptions.all d acc a b old row col =
      .ok (.float .f32 (∑ k ∈ Finset.range 16, x k * y k + prev)) :=
  by
  obtain ⟨name, sc, why, hI, hmma⟩ : ∃ name sc why, Assumptions.idealArith =
      Assumption.idealReal name sc why ∧ sc.mma = [.f16 .bf16 .f32] := ⟨_, _, _, rfl, rfl⟩
  have hA : Assumptions.all = Assumption.idealReal name sc why ::
      [Assumptions.approx, Assumptions.swExp2 kernel, Assumptions.lg2Exact,
        Assumptions.divFullExact, Assumptions.negExact, Assumptions.bf16Exact,
        Assumptions.commitOrder, Assumptions.pollAgree, Assumptions.setMaxNRegSync,
        Assumptions.inputReadOnly] := by
    rw [← hI]
    rfl
  exact eval_sum_bf16 hA hk (by simp [hk, hmma]) hv hws hna hnb hla hlb hrow hcol ha hb hprev

end
end PTX.Kernels.InklingRelDecode.Proof.Result.Mma
