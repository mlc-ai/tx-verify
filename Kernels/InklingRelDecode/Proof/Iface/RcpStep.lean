-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Assumptions
public import Kernels.InklingRelDecode.Gen.TypedLateQt
public import Lemmas.Flow.TypedG

@[expose] public section

/-! # The reciprocal of the epilogue

The epilogue's windows take the step of `rcp.approx.ftz.f32` at pc 2602 as a fact: on a typed
state that satisfies the lane's fact it does not fault and writes a datum
(`Top.rcpStep_of`, from the value fact that the operand is not a zero). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Iface
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Kernels.InklingRelDecode.Gen.TypedLateQt

/-- **The reciprocal at 2602** does not fault, and writes a datum (the value chain's fact `R`). -/
def RcpStep (L : Launch) (g : Nat) (R : TState → Prop) : Prop :=
  ∀ op, kernel.code[2602]? = some ⟨none, op⟩ → ∀ t : TState, t.pc = 2602 →
    TypedF (lateQt 2602) t → R t →
    ∃ x, execLocalA Assumptions.all L g t op = .ok (PTX.next (setReg t 1761 x)) ∧ Dat32 x

end PTX.Kernels.InklingRelDecode.Proof.Iface
