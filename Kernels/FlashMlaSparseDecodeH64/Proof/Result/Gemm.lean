-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Assumptions

@[expose] public section

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result

open PTX

noncomputable section

/-- The two observed bytes of a BF16 element decode to its real payload. -/
theorem bf16MmaElement_of_bytes {op : TcMma.Operand} {bytes : List (Option Byte)}
    {row k : Nat} {x : ℝ}
    (h : (bytes.drop (2 * (row * 16 + k))).take 2 = (Value.float .bf16 x).toBytes.map some) :
    Assumption.idealMmaElement (.f16 .bf16 .f32) op bytes row k = .ok x := by
  have hb : TcMma.elementBytes (.f16 .bf16 .f32) bytes row k =
      (Value.float .bf16 x).toBytes.map some := by
    rw [← h]
    simp [TcMma.elementBytes, TcMma.Kind.k, TcMma.Kind.width, Nat.mul_comm]
  let v := Value.float .bf16 x
  have hlist : v.toBytes.map some = [some (v, 0), some (v, 1)] := rfl
  have hr : rebuild 1 (v.toBytes.map some) = .ok v := by
    rw [hlist]
    simp only [rebuild]
    have hok : v.bytes = ([some (v, 0), some (v, 1)] : List (Option Byte)).length ∧
        [some (v, 0), some (v, 1)] = v.toBytes.map some := ⟨rfl, hlist.symm⟩
    rw [ite_eq_left hok]
    rfl
  unfold Assumption.idealMmaElement
  dsimp only
  rw [hb, hr]
  change valFloat .bf16 v = .ok x
  exact valFloat_float

private theorem bf16Mma_dot {d : TcMma.Descriptor} (hk : d.kind = (.f16 .bf16 .f32))
    (hna : d.negateA = false) (hnb : d.negateB = false) {a b : List (Option Byte)}
    {row col : Nat} {x y : Nat → ℝ} :
    ∀ n, (∀ j < n, Assumption.idealMmaElement (.f16 .bf16 .f32) .a a row j = .ok (x j)) →
      (∀ j < n, Assumption.idealMmaElement (.f16 .bf16 .f32) .b b col j = .ok (y j)) →
      Assumption.idealMmaDot d a b row col n = .ok (∑ j ∈ Finset.range n, x j * y j)
  | 0, _, _ => by simp [Assumption.idealMmaDot]; rfl
  | n + 1, ha, hb => by
    have ht := bf16Mma_dot hk hna hnb n (fun j hj => ha j (by omega)) (fun j hj => hb j (by omega))
    simp only [Assumption.idealMmaDot, ht, hk, ha n (by omega), hb n (by omega), hna, hnb,
      Finset.sum_range_succ]
    rfl

/-- A BF16 issue evaluates to its sixteen products and optional old accumulator. The A row
is the compiled layout's datapath row, which may differ from the logical output row. -/
theorem bf16Mma_sum {d : TcMma.Descriptor} (hk : d.kind = (.f16 .bf16 .f32))
    (hv : TcMma.Valid d) (hna : d.negateA = false) (hnb : d.negateB = false)
    {a b : List (Option Byte)} (hla : a.length = TcMma.Operand.bytes .a d)
    (hlb : b.length = TcMma.Operand.bytes .b d) {row col : Nat} (hrow : row < d.m)
    (hcol : col < d.n) {x y : Nat → ℝ}
    (ha : ∀ k < 16,
      Assumption.idealMmaElement (.f16 .bf16 .f32) .a a (TcMma.operandRow d row col) k = .ok (x k))
    (hb : ∀ k < 16, Assumption.idealMmaElement (.f16 .bf16 .f32) .b b col k = .ok (y k))
    {acc : Bool} {old : Option Value} {prev : ℝ}
    (hprev : Assumption.idealMmaAccumulator .f32 acc old = .ok prev) :
    TcMma.eval Assumptions.all d acc a b old row col =
      .ok (.float .f32 ((∑ k ∈ Finset.range 16, x k * y k) + prev)) := by
  have hd := bf16Mma_dot hk hna hnb 16 ha hb
  have hprofile : Assumptions.idealArith.mmaRule d acc a b old row col =
      some (Assumption.execIdealMma d acc a b old row col) := by
    simp [Assumptions.idealArith, Assumption.idealReal, hk]
  simp only [TcMma.eval, hk, Assumptions.all, List.findSome?, hprofile, Option.getD_some]
  simp only [Assumption.execIdealMma, hk, hv, hrow, hcol, hla, hlb, and_self, TcMma.Kind.k]
  simp [bind, Except.bind, pure, Except.pure, hd, hprev]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Result
