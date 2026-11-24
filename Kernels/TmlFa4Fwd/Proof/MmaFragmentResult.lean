-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaBf16Eval

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX
open scoped BigOperators

noncomputable section

/-- A fragment's contraction is sixteen consecutive elements of the logical dot product. -/
def fragmentDot (x y : Nat → ℝ) (step : Nat) : ℝ :=
  ∑ k ∈ Finset.range 16, x (16 * step + k) * y (16 * step + k)

theorem fragmentDot_partition (x y : Nat → ℝ) (n : Nat) :
    (∑ step ∈ Finset.range n, fragmentDot x y step) =
      ∑ k ∈ Finset.range (16 * n), x k * y k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, show 16 * (n + 1) = 16 * n + 16 by omega,
      Finset.sum_range_add]
    rfl

/-- Numeric and physical operands of the eight actual sequential MMA issues for a cell.
The first fragment can clear D or read the earlier corrected tile. -/
structure CellFragments (l : Launch) (X : Execution) (issues : Fin 8 → EvId)
    (spec : Fin 8 → TcMma.OperandSpec) (dst : Nat) (row col : Nat) (cell : TcMma.Cell)
    (keep : Bool) (x y : Nat → ℝ) : Prop where
  issue : ∀ step, X.MmaIssue (issues step) dst (spec step)
    (keep || decide (0 < step.val)) (List.replicate 4 0)
  position : ∀ step, TcMma.writeCell (spec step) dst (List.replicate 4 0) row col = some cell
  evaluation : ∀ step, ∃ operands, X.async.mmaOperands (issues step) = some operands ∧
    ∀ old prev, Assumption.idealMmaAccumulator .f32 (keep || decide (0 < step.val)) old =
      .ok prev →
      TcMma.eval Assumptions.all (spec step).descriptor (keep || decide (0 < step.val))
        operands.a operands.b old row col = .ok (.float .f32 (fragmentDot x y step.val + prev))
  previous : ∀ step, step.val ≠ 0 →
    TcMma.ReadSource l X .acc (issues ⟨step.val - 1, by have := step.isLt; omega⟩)
      (issues step) cell

variable {l : Launch} {X : Execution} {issues : Fin 8 → EvId} {spec : Fin 8 → TcMma.OperandSpec}
    {dst row col : Nat} {cell : TcMma.Cell} {keep : Bool} {x y : Nat → ℝ}
    (hF : CellFragments l X issues spec dst row col cell keep x y) (prev : ℝ)
    (hStart : keep = false → prev = 0)
    (hPrior : keep = true → ∃ source, TcMma.ReadSource l X .acc source (issues 0) cell ∧
      (TcMma.Result l Assumptions.all X source cell (.float .f32 prev) ∨
        TcMma.StoreValue l X source cell (.float .f32 prev)))
include hF prev hStart hPrior

private theorem fragmentResult :
    ∀ step : Fin 8, TcMma.Result l Assumptions.all X (issues step) cell
      (.float .f32 (prev + ∑ k ∈ Finset.range (step.val + 1), fragmentDot x y k)) := by
  suffices h : ∀ n (hn : n < 8), TcMma.Result l Assumptions.all X (issues ⟨n, hn⟩) cell
      (.float .f32 (prev + ∑ k ∈ Finset.range (n + 1), fragmentDot x y k)) by
    exact fun step => h step.val step.isLt
  intro n
  induction n with
  | zero =>
    intro hn
    let step : Fin 8 := ⟨0, hn⟩
    have he : (keep || decide (0 < step.val)) = keep := by simp [step]
    have hi := hF.issue step
    rw [he] at hi
    obtain ⟨ops, ho, hEval⟩ := hF.evaluation step
    rw [he] at hEval
    change TcMma.Result l Assumptions.all X (issues step) cell
      (.float .f32 (prev + ∑ k ∈ Finset.range 1, fragmentDot x y k))
    rw [Finset.sum_range_one]
    rw [add_comm prev]
    cases hk : keep
    · rw [hk] at hi hEval
      rw [hStart hk]
      exact .overwrite hi (hF.position step) ho (hEval none 0 rfl)
    · rw [hk] at hi hEval
      obtain ⟨source, hSource, hPrevious⟩ := hPrior hk
      have ha := hEval (some (.float .f32 prev)) prev rfl
      rcases hPrevious with hMma | hStore
      · exact .accumulate hi (hF.position step) ho hMma hSource ha
      · exact .accumulateStored hi (hF.position step) ho hStore hSource ha
  | succ n ih =>
    intro hn
    let step : Fin 8 := ⟨n + 1, hn⟩
    have he : (keep || decide (0 < step.val)) = true := by simp [step]
    have hi := hF.issue step
    rw [he] at hi
    obtain ⟨ops, ho, hEval⟩ := hF.evaluation step
    rw [he] at hEval
    have hSource := hF.previous step (by simp [step])
    have hMma := ih (by omega)
    let old := prev + ∑ k ∈ Finset.range (n + 1), fragmentDot x y k
    have ha := hEval (some (.float .f32 old)) old rfl
    rw [Finset.sum_range_succ, ← add_assoc, add_comm _ (fragmentDot x y (n + 1))]
    exact .accumulate hi (hF.position step) ho hMma hSource ha

/-- The last issue of the eight fragments has the real 128-element dot plus the preceding D. -/
theorem fullFragmentResult :
    TcMma.Result l Assumptions.all X (issues 7) cell
      (.float .f32 (prev + ∑ k ∈ Finset.range 128, x k * y k)) := by
  have h := fragmentResult hF prev hStart hPrior 7
  change TcMma.Result l Assumptions.all X (issues 7) cell
    (.float .f32 (prev + ∑ k ∈ Finset.range 8, fragmentDot x y k)) at h
  rwa [fragmentDot_partition] at h

end
end PTX.Kernels.TmlFa4Fwd.Mma
