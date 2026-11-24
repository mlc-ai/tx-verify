-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaOperandValues
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX
open scoped BigOperators

noncomputable section

private theorem idealBf16Dot {d : TcMma.Descriptor}
    (hk : d.kind = .f16 .bf16 .f32) (hna : d.negateA = false) (hnb : d.negateB = false)
    {a b : List (Option Byte)} {row col : Nat} {x y : Nat → ℝ} :
    ∀ n,
      (∀ k < n, Assumption.idealMmaElement (.f16 .bf16 .f32) .a a row k = .ok (x k)) →
      (∀ k < n, Assumption.idealMmaElement (.f16 .bf16 .f32) .b b col k = .ok (y k)) →
      Assumption.idealMmaDot d a b row col n = .ok (∑ k ∈ Finset.range n, x k * y k) := by
  intro n
  induction n with
  | zero =>
    intro _ _
    simp [Assumption.idealMmaDot, pure, Except.pure]
  | succ n ih =>
    intro ha hb
    rw [Finset.sum_range_succ, Assumption.idealMmaDot, hk, hna, hnb]
    have h := ih (fun k h => ha k (by omega)) (fun k h => hb k (by omega))
    simp [h, bind, Except.bind, pure, Except.pure, ha n (by omega), hb n (by omega)]

/-- An actual ideal BF16 MMA cell computes its sixteen products plus the selected old D. -/
theorem evalBf16Cell {d : TcMma.Descriptor} (hk : d.kind = .f16 .bf16 .f32)
    (hValid : TcMma.Valid d) (hWs : d.ws = false)
    (hna : d.negateA = false) (hnb : d.negateB = false)
    {a b : List (Option Byte)} (hla : a.length = TcMma.Operand.bytes .a d)
    (hlb : b.length = TcMma.Operand.bytes .b d)
    {row col : Nat} (hr : row < d.m) (hc : col < d.n) {x y : Nat → ℝ}
    (ha : ∀ k < 16, Assumption.idealMmaElement (.f16 .bf16 .f32) .a a row k = .ok (x k))
    (hb : ∀ k < 16, Assumption.idealMmaElement (.f16 .bf16 .f32) .b b col k = .ok (y k))
    {acc : Bool} {old : Option Value} {prev : ℝ}
    (hPrev : Assumption.idealMmaAccumulator .f32 acc old = .ok prev) :
    TcMma.eval Assumptions.all d acc a b old row col =
      .ok (.float .f32 ((∑ k ∈ Finset.range 16, x k * y k) + prev)) := by
  have hs : d.kind ∈ Assumptions.arithScope.mma := by rw [hk]; exact List.mem_cons_self
  have hRule : Assumptions.idealArith.mmaRule d acc a b old row col =
      some (Assumption.execIdealMma d acc a b old row col) := by
    simp [Assumptions.idealArith, Assumption.idealReal, hs]
  have hModel : TcMma.eval Assumptions.all d acc a b old row col =
      Assumption.execIdealMma d acc a b old row col := by
    simp only [TcMma.eval, hk, Assumptions.all, Assumptions.numeric, List.cons_append,
      List.findSome?, hRule, Option.getD_some]
  have hRow : TcMma.operandRow d row col = row := by simp [TcMma.operandRow, hWs]
  have hDot := idealBf16Dot hk hna hnb 16 ha hb
  rw [hModel]
  simp only [Assumption.execIdealMma, hk, hValid, hr, hc, hla, hlb, and_self, hRow, TcMma.Kind.k]
  simp [bind, Except.bind, pure, Except.pure, hDot, hPrev]

end
end PTX.Kernels.TmlFa4Fwd.Mma
