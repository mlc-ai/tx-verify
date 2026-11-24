-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionLseProducer
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStagingSetup
public import Kernels.TmlFa4Fwd.Proof.Thread.StatisticsWordOrder
import Kernels.TmlFa4Fwd.Proof.Thread.TerminalStatisticsWrites

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Correction
open PTX PTX.AsyncCopy Epilogue
open PTX.Kernels.TmlFa4Fwd.Correction

/-- An actual output element is at or above the first data tile and cannot
overwrite a terminal statistics word in the control area. -/
theorem StagingWrite.doesNotCoverStatistics {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {writer : EvId} {a : Acc} {bytes : List Byte} (h : StagingWrite X (.thread writer) a bytes)
    (g : Nat) (stage : Fin 2) (kind : StatsKind) {k : Nat} (hk : k < 4) :
    ¬ a.Covers ((statsLoc l g stage kind).at k) := by
  obtain ⟨outputStage, subbox, x, row, _, _, rfl, _⟩ := h.element hp hX
  intro hCover
  have hLower := hCover.2.2.1
  have hRow : rowOf l g < 128 := Nat.mod_lt _ (by decide)
  have hStage := stage.isLt
  cases kind <;> simp only [outputElementAccess, outputChunkLoc, sharedSlot, statsLoc, statsOff,
    Loc.at] at hLower <;> omega

/-- The matched terminal publication supplies the full byte-order premise for correction's
LSE statistics reads. All competing writers to these bytes occur no later than the chosen write. -/
theorem terminalWordOrderOfFinalPublication {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g publication wait : Nat} {stage : Fin 2}
    (hFinal : Scores.Publishes X (terminalStatsProducer l g stage, publication) .final) :
    TerminalWordOrder l X g stage (publication - 2) wait := by
  intro word k hk w a bytes hw
  dsimp only
  intro hCover
  rcases terminalWordOrderOrStaging hp hX hFinal word hk hw hCover with h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · obtain ⟨writer, rfl, _⟩ := terminalStatisticsWriterOrdinary hp hX hk hw hCover
    exact (h.doesNotCoverStatistics hp hX g stage (finalStatsKind word) hk hCover).elim

end PTX.Kernels.TmlFa4Fwd.Thread.Correction
