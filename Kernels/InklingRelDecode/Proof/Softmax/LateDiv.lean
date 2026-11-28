-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.GenRulesC
public import Lemmas.Flow.TypedFloatJ

@[expose] public section

/-! # `div.full.f32` at pc 600 on two numbers

The reading `divFullExact` divides two numbers whose divisor is not zero (the scale register,
`Pre.scalePos` through `scaleVal_float`) and writes a datum of four bytes, whatever the tags
know of the operands. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Assumption

noncomputable section
variable {L : Launch} {g : Nat}

/-- **The step of `div.full.f32 d, a, b` at pc 600** on operands that read as the numbers `x` and
`y`, with `y` not zero, writes the datum `x / y`. -/
theorem divFull_step {t : TState} (hpc : t.pc = 600) {d : Nat} {a b : Opnd} {va vb : Value}
    {x y : ℝ} (ha : OpndIs L g t a va) (hb : OpndIs L g t b vb) (hx : valFloat .f32 va = .ok x)
    (hy : valFloat .f32 vb = .ok y) (h0 : y ≠ 0) :
    ∃ v, execLocalA Assumptions.all L g t
        (.float { divFullI with dsts := [some d], srcs := [a, b] }) =
      .ok (PTX.next (setReg t d v)) ∧ Dat32 v := by
  refine ⟨.float .f32 (x / y), ?_, dat32_float _⟩
  rw [exec_divFull hpc ha hb]
  simp [divFullE, approxVal, finiteVal_of hx, finiteVal_of hy, bindRead, h0, pure, Except.pure,
    Except.map]

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax
