-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.TerminalPublishedWords
public import Kernels.TmlFa4Fwd.Proof.Thread.Softmax
public import Kernels.TmlFa4Fwd.Proof.Thread.Exit
import Kernels.TmlFa4Fwd.Proof.SoftmaxSingleVisitPublication

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Correction

open PTX PTX.Flow PTX.Proof Softmax
open PTX.Kernels.TmlFa4Fwd.Correction

/-- The actual producer suffix after its last sum and reference have been computed. -/
@[no_expose] def TerminalDrainValues (l : Launch) (X : Execution) (g : Nat)
    (stage : Fin 2) (sum maximum : ℝ) : Prop :=
  ∃ (state : TState) (pos : Nat),
    state.pc = 7605 ∧ state.regs 7257 = some (fl sum) ∧
      state.regs 7256 = some (fl maximum) ∧
    Run kernel Assumptions.all l (terminalStatsProducer l g stage) state
      ((X.tr (terminalStatsProducer l g stage)).drop pos) none

/-- Capture the sum and reference at the reached terminal drain. -/
theorem TerminalDrainValues.ofReached {l : Launch} {X : Execution} {g pos : Nat}
    {stage : Fin 2} {sum maximum : ℝ} {state : TState}
    (hPc : state.pc = 7605) (hSum : state.regs 7257 = some (fl sum))
    (hMax : state.regs 7256 = some (fl maximum))
    (hRun : Run kernel Assumptions.all l (terminalStatsProducer l g stage) state
      ((X.tr (terminalStatsProducer l g stage)).drop pos) none) :
    TerminalDrainValues l X g stage sum maximum := ⟨state, pos, hPc, hSum, hMax, hRun⟩

/-- The reached terminal values are written in the actual paired lane's final publication. -/
theorem TerminalDrainValues.publishedWords {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g publication : Nat} {stage : Fin 2} {sum maximum : ℝ}
    (hDrain : TerminalDrainValues l X g stage sum maximum)
    (hFinal : Scores.Publishes X (terminalStatsProducer l g stage, publication) .final)
    (hExit : Exited X (terminalStatsProducer l g stage)) :
    TerminalPublishedWords l X g stage publication (fl sum) (fl maximum) := by
  obtain ⟨state, pos, hPc, hSum, hMax, hRun⟩ := hDrain
  obtain ⟨hs, hm, ha, hl⟩ := terminalDrainAtFinalPublication hp hX
    (terminalStatsWarp l g stage) (terminalStatsProducerWarp hp g stage).symm
    hPc hSum hMax hRun hExit hFinal
  exact ⟨hs, hm, ha, hl⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Correction
