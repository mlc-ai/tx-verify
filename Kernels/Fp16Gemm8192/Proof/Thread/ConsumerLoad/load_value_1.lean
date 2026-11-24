-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerLoad.Base

@[expose] public section

/-! The values loads 4 to 7 give their destinations. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Consumer
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000

set_option maxHeartbeats 4000000 in
/-- The value the table gives destination `p` of load `j` after the load is its value `p`
(loads `4` to `7`). -/
theorem load_value_1 (L : Launch) (g : Nat) (s : Site) (m n m' n' cp ap : Nat) (resp : Value)
    (x : Nat) (acc : Nat → Value) (xs : List Value) (base : Value) :
    ∀ (j : Fin 16), j.val / 4 = 1 → ∀ (p : Nat), p < (ldRegs j).length →
      valueOf L g ⟨s, m, n, m', n', cp, ap, resp, x, loadAcc acc j.val xs, base⟩
        ((ldRegs j).getD p 0) = xs.getD p (b32 0) := by
  intro j hj p hp
  rw [ldRegs_len] at hp
  fin_cases j <;> first | (exact absurd hj (by decide)) | (interval_cases p <;> kernel_rfl)

end
end PTX.Kernels.Fp16Gemm8192.Proof.Consumer
