-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerLoad.Base
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerLoad.load_value_0
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerLoad.load_value_1
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerLoad.load_value_2
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerLoad.load_value_3

@[expose] public section

/-! The values a load gives its destinations. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Consumer
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000

/-- The value the table gives destination `p` of load `j` after the load is its value `p`. -/
theorem load_value (L : Launch) (g : Nat) (s : Site) (m n m' n' cp ap : Nat) (resp : Value)
    (x : Nat) (acc : Nat → Value) (xs : List Value) (base : Value) (j : Fin 16) (p : Nat)
    (hp : p < (ldRegs j).length) :
    valueOf L g ⟨s, m, n, m', n', cp, ap, resp, x, loadAcc acc j.val xs, base⟩
      ((ldRegs j).getD p 0) = xs.getD p (b32 0) := by
  have hj : j.val / 4 < 4 := by omega
  interval_cases hk : j.val / 4
  · exact load_value_0 L g s m n m' n' cp ap resp x acc xs base j hk p hp
  · exact load_value_1 L g s m n m' n' cp ap resp x acc xs base j hk p hp
  · exact load_value_2 L g s m n m' n' cp ap resp x acc xs base j hk p hp
  · exact load_value_3 L g s m n m' n' cp ap resp x acc xs base j hk p hp

end
end PTX.Kernels.Fp16Gemm8192.Proof.Consumer
