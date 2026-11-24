-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxTerminalHandoff
public import Kernels.TmlFa4Fwd.Proof.SoftmaxNumerics
public import Kernels.TmlFa4Fwd.Proof.SoftmaxScoreNumeric

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Correction
open PTX PTX.Flow PTX.Proof Softmax Epilogue
open PTX.Kernels.TmlFa4Fwd.Correction

/-- The actual softmax lane's final sum and selected reference. -/
@[no_expose] def TerminalLaneValues (l : Launch) (X : Execution) (producer : Nat)
    (sum maximum : ℝ) : Prop :=
  ∃ s pos, s.pc = 7605 ∧ s.regs 7257 = some (fl sum) ∧
    s.regs 7256 = some (fl maximum) ∧
    Run kernel Assumptions.all l producer s ((X.tr producer).drop pos) none

/-- The lane whose terminal values were reached supplies its paired correction row. -/
theorem TerminalLaneValues.forCorrection {l : Launch} {X : Execution}
    {producer g : Nat} {stage : Fin 2} {sum maximum : ℝ}
    (h : TerminalLaneValues l X producer sum maximum)
    (hProducer : terminalStatsProducer l g stage = producer) :
    TerminalDrainValues l X g stage sum maximum := by
  obtain ⟨s,pos,hPc,hSum,hMax,hRun⟩ := h
  exact TerminalDrainValues.ofReached hPc hSum hMax (hProducer.symm ▸ hRun)

/-- Cover the terminal lane's finite reference using the actual completed
softmax recurrence and the canonical reference register. -/
theorem terminalLaneValuesOfFinishedSum {p : Params} {l : Launch} {X : Execution}
    {batch head row blocks producer pos : Nat} {s : TState}
    {reference : Nat → Option ℝ} {sums : Nat → ℝ} {maximum : Option ℝ}
    (hVisits : SoftmaxSumRun p batch head row blocks reference sums)
    (hReference : reference (blocks-1) = maximum.map (abiFloat p.scaleLog2Bits * ·))
    (hPositive : 0 < blocks) (hKey : 0 < p.keyCount batch row)
    (hPc : s.pc = 7605) (hSum : s.regs 7257 = some (fl (sums (blocks-1))))
    (hMax : s.regs 7256 = some (scoreValue maximum))
    (hRun : Run kernel Assumptions.all l producer s ((X.tr producer).drop pos) none) :
    ∃ value : ℝ, abiFloat p.scaleLog2Bits*value = (reference (blocks-1)).getD 0 ∧
      TerminalLaneValues l X producer (sums (blocks-1)) value := by
  have hFinite := hVisits.final_ref hPositive hKey
  cases maximum with
  | none => simp [hReference] at hFinite
  | some value =>
    have hScale : abiFloat p.scaleLog2Bits * value = (reference (blocks-1)).getD 0 := by
      rw [hReference]
      rfl
    exact ⟨value,hScale,s,pos,hPc,hSum,hMax,hRun⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Correction
