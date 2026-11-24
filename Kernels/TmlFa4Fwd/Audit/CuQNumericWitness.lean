-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Spec
import Lemmas.Tcgen05.FloatBits
import Lemmas.Flow.MemTmpl
import Mathlib.Tactic.NormNum

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Audit
open PTX

noncomputable section

/-- The base-two logit is the negative of the first component. The second component is
one normal BF16 value element. The first and the aggregate of the positive weights cancel
at the smallest normal magnitude, with a residual from the last element. -/
def cuQNormalTerms : List (Nat × Nat) :=
  [(0, 0x8080), (2, 0x0080), (2, 0x0080), (3, 0x0080), (3, 0x0080), (3, 0x0080),
    (4, 0x0080), (5, 0x0080), (6, 0x0080), (7, 0x0080), (8, 0x0080), (9, 0x0080),
    (10, 0x0080), (11, 0x0080), (12, 0x0080), (13, 0x0080), (14, 0x0080), (15, 0x0080),
    (15, 0x0105)]

/-- The ideal exp2 weights also have exact normal BF16 representations for the PV input. -/
def cuQNormalWeight (term : Nat × Nat) : ℚ := (2 : ℚ) ^ (-(term.1 : ℤ))

def cuQNormalValue (term : Nat × Nat) : ℚ := (FloatFmt.bf16.decode term.2).getD 0

theorem cuQNormalTermFormats :
    cuQNormalTerms.length = 19 ∧ cuQNormalTerms.all (fun term =>
      let weight := 128 * (127 - term.1)
      let magnitude := term.2 % 0x8000
      decide (0x80 ≤ weight ∧ weight < 0x7f80 ∧
        0x80 ≤ magnitude ∧ magnitude < 0x7f80 ∧
        FloatFmt.bf16.decode weight = some (cuQNormalWeight term))) = true := by
  decide +kernel

/-- The mass and PV accumulator in the ideal one-block arithmetic, computed over rationals. -/
theorem cuQNormalAccumulator :
    (cuQNormalTerms.map cuQNormalWeight).sum = 2 ∧
    (cuQNormalTerms.map (fun term => cuQNormalWeight term * cuQNormalValue term)).sum =
      2 * FloatFmt.f32.magnitude 138 := by
  decide +kernel

/-- The correction product is the PV accumulator times the reciprocal mass. -/
def cuQNormalCorrectionValue : Value := Value.float .f32
  ((↑(cuQNormalTerms.map (fun term => cuQNormalWeight term * cuQNormalValue term)).sum : ℝ) *
    (1 / (↑(cuQNormalTerms.map cuQNormalWeight).sum : ℝ)))

/-- All the live V and weight inputs are normal, while the correction product has an
exact positive FP32 subnormal encoding. -/
theorem cuQNormalCorrectionBits : cuQNormalCorrectionValue.bitPattern = some 138 := by
  have h : (2 : ℚ) * FloatFmt.f32.magnitude 138 * (1 / 2) =
      FloatFmt.f32.magnitude 138 := by decide +kernel
  have hCast := congrArg (fun q : ℚ => (q : ℝ)) h
  push_cast at hCast
  unfold cuQNormalCorrectionValue
  rw [cuQNormalAccumulator.1, cuQNormalAccumulator.2]
  push_cast
  rw [hCast]
  have hBits := Proof.encode_magnitude FloatFmt.f32 (F := 138) false (by decide) (by decide)
  simpa only [Value.bitPattern, Bool.false_eq_true, ↓reduceIte, one_mul, Nat.zero_add] using
    congrArg some hBits

/-- A scalar load of all four correction bytes uses the FP32 payload's integer encoding. -/
theorem cuQNormalCorrectionReadBits (l : Launch) (g : Nat) (t : TState) (reg : Nat)
    (hSub : t.sub = 0) (hAcc : t.acc = []) :
    readBits l g (afterLoad t [reg] (cuQNormalCorrectionValue.toBytes.map some)) 32 (.reg reg) =
      .ok (BitVec.ofNat 64 138) := by
  rw [Proof.afterLoad_ok hSub hAcc (Proof.rebuild_scalar (v := cuQNormalCorrectionValue)
    (by decide) rfl)]
  have hBits := cuQNormalCorrectionBits
  unfold cuQNormalCorrectionValue at hBits ⊢
  simp only [readBits, readReg, setReg, Function.update_self, bind, Except.bind, pure, Except.pure]
  rw [hBits]
  rfl

end
end PTX.Kernels.TmlFa4Fwd.Audit
