-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionRescaleVisit
import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrTrip

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX

/-- The actual zero ballot makes its issuing lane's coefficient the identity
when that coefficient is at most one. -/
theorem RescaleVisit.factorOfZeroBallot {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g pos : Nat} {stage : Fin 2}
    {alpha : ℝ} {old : Fin 8 → Nat → ℝ} {word : BitVec 32} {coefficient : Value}
    (h : RescaleVisit l X g pos stage alpha old word coefficient)
    (hZero : word = 0) (hAlpha : alpha ≤ 1) :
    alpha = 1 := by
  have hMember : (2^32-1 : Nat).testBit (laneOf l g) = true := by
    rw [Nat.testBit_two_pow_sub_one, decide_eq_true_eq]
    exact Nat.mod_lt _ (by decide)
  have hBit := FlashAttn4Fwd.Proof.ballot_own hX h.ballot hMember
  rw [hZero] at hBit
  exact le_antisymm hAlpha (le_of_not_gt (by simpa using hBit.symm))

end PTX.Kernels.TmlFa4Fwd.Correction
