-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaPvResult
public import Kernels.TmlFa4Fwd.Proof.SoftmaxWeights

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX Softmax
open scoped BigOperators

noncomputable section

/-- PV's zero-filled V tails and the softmax's zero probability describe the same masked sum. -/
theorem pvMaskedWeightedBlock (p : Params) (batch head row blocks visit d : Nat) (reference : ℝ) :
    (∑ k ∈ Finset.range 128, shiftedWeight p batch head row (visitKey blocks visit k) reference *
      pvValue p batch head (visitKey blocks visit k) d) =
      (2 : ℝ) ^ (-reference) * maskedBlockSum (p.keyCount batch row) blocks visit
        (weightedValue p batch head row d) := by
  rw [shiftedBlockProducts p batch head row blocks visit reference
    (fun k => pvValue p batch head k d)]
  congr 1
  unfold maskedBlockSum
  apply Finset.sum_congr rfl
  intro k _
  by_cases hKey : visitKey blocks visit k < p.keyCount batch row
  · have hLive : visitKey blocks visit k < p.kLength batch := by
      exact hKey.trans_le (Nat.min_le_left _ _)
    simp [weightedValue, pvValue, hKey, hLive]
  · simp [hKey]

/-- The last PV fragment provides exactly the weighted block of the attention recurrence.
An earlier corrected numerator is carried through all eight fragments. -/
theorem pvCellWeightedBlock {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g use batch head qrow blocks visit : Nat} (block : Fin 4) (row col : Fin 128)
    (issues : Fin 8 → EvId) (reference : ℝ) (keep : Bool) (carry : ℝ) :
    let weights := fun k => shiftedWeight p batch head qrow (visitKey blocks visit k) reference
    let dst := outputColumn (pvSite block).stage
    let cell : TcMma.Cell := ⟨g / l.block, row.val, dst + col.val⟩
    PvCellInputs p l X g block use batch head (visitKey blocks visit 0) row col issues weights →
    (∀ step : Fin 8, X.MmaIssue (issues step) dst (pvOperands l g block step use)
      (keep || decide (0 < step.val)) (List.replicate 4 0)) →
    (∀ step : Fin 8, ∃ ops, X.async.mmaOperands (issues step) = some ops) →
    (∀ step : Fin 8, step.val ≠ 0 → TcMma.ReadSource l X .acc
      (issues ⟨step.val - 1, by have := step.isLt; omega⟩) (issues step) cell) →
    (keep = false → carry = 0) →
    (keep = true → ∃ source, TcMma.ReadSource l X .acc source (issues 0) cell ∧
      (TcMma.Result l Assumptions.all X source cell (.float .f32 carry) ∨
        TcMma.StoreValue l X source cell (.float .f32 carry))) →
    TcMma.Result l Assumptions.all X (issues 7) cell (.float .f32 (carry +
      (2 : ℝ) ^ (-reference) * maskedBlockSum (p.keyCount batch qrow) blocks visit
        (weightedValue p batch head qrow col.val))) := by
  dsimp only
  intro hIn hi ho hS hZero hCarry
  have h := pvCellResult hX block row col issues _ keep carry hIn hi ho hS hZero hCarry
  have hKey (k : Nat) : visitKey blocks visit 0 + k = visitKey blocks visit k := by simp [visitKey]
  simp only [hKey] at h
  rwa [pvMaskedWeightedBlock] at h

end
end PTX.Kernels.TmlFa4Fwd.Mma
