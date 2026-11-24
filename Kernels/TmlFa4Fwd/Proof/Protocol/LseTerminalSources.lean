-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.LseTerminalPeer
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionLseProducer
import Kernels.TmlFa4Fwd.Proof.Thread.TerminalStatisticsOrder
public import Kernels.TmlFa4Fwd.Proof.Thread.TerminalPublishedWords
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionLseTerminalStores

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Statistics

open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Correction
open PTX.Kernels.TmlFa4Fwd.Thread.Correction

noncomputable section

/-- A matched final peer selects the two actual stores and their barrier generation. -/
theorem terminalStoresOfFinalPeer {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g wait publication : Nat} {stage : Fin 2} (hPeer : TerminalPeer l X g stage wait
      publication .final) :
    ∃ first, first + 2 = publication ∧ TerminalGeneration l X g stage first wait ∧
      ∃ sumAcc maxAcc sum maximum,
        X.Writes (terminalStatsProducer l g stage, first) sumAcc sum ∧
        X.Writes (terminalStatsProducer l g stage, first + 1) maxAcc maximum := by
  obtain ⟨first, rfl, hWrites⟩ := terminalStoresOfPublication hX hPeer.publication
  obtain ⟨key, hArrival, hWait, _⟩ := hPeer.sameGeneration
  exact ⟨first, rfl, ⟨key, hArrival, hWait⟩, hWrites⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- Each actual final producer store is causally before the matching correction read. -/
theorem terminalStoresPrecedeReads {store : EvId} {stage : Fin 2} {publication wait : Nat}
    {sum maximum : List (Option Byte)} (hRead : TerminalLseReads l X store stage wait sum maximum)
    (hPeer : TerminalPeer l X store.1 stage wait publication .final) :
    ∃ first, first + 2 = publication ∧ ∃ sumAcc maxAcc sumBytes maxBytes,
      X.Writes (terminalStatsProducer l store.1 stage, first) sumAcc sumBytes ∧
      X.Writes (terminalStatsProducer l store.1 stage, first + 1) maxAcc maxBytes ∧
      ∀ word : Fin 2,
        baseCausality l X (terminalStatsProducer l store.1 stage, first + word.val)
          (store.1, wait + 1 + word.val) := by
  obtain ⟨first, hFirst, ⟨key, hArrival, hWait⟩, a, b, sumBytes, maxBytes, hs, hm⟩ :=
    terminalStoresOfFinalPeer hX hPeer
  let producer := terminalStatsProducer l store.1 stage
  obtain ⟨_, hPub, _⟩ := hPeer.publication
  obtain ⟨_, hLast⟩ := hRead.maxRead
  have hLength : wait + 2 < (X.tr store.1).length := (List.getElem?_eq_some_iff.mp hLast).1
  have hc : producer / l.block = store.1 / l.block := by
    have hRow : rowOf l store.1 < 128 := Nat.mod_lt _ (by decide)
    have hStage := stage.isLt
    unfold producer terminalStatsProducer
    rw [hp.block]
    omega
  have hSame : SameCta l producer store.1 :=
    ⟨event_thread_lt hX hPub, event_thread_lt hX (e := (store.1, wait + 2)) hLast, hc⟩
  refine ⟨first, hFirst, a, b, sumBytes, maxBytes, hs, hm, fun word => ?_⟩
  have hWord := word.isLt
  have hAfter : wait + 1 + word.val < (X.tr store.1).length := by omega
  exact Relation.TransGen.single (.inr (.inl
    ⟨hSame, key, first + 2, wait, hArrival, hWait, by omega, by omega, hAfter⟩))

/-- A completed producer provides the final writes causally preceding the observed LSE reads. -/
theorem terminalStoresOfExit (hCuQ : DrainCuQProtected p X) (hUsedK : UsedKProtected p X)
    {store : EvId} {stage : Fin 2} {wait : Nat} {sum maximum : List (Option Byte)}
    (hRead : TerminalLseReads l X store stage wait sum maximum)
    (hExit : Thread.Exited X (terminalStatsProducer l store.1 stage)) :
    ∃ publication first, first + 2 = publication ∧
      TerminalPeer l X store.1 stage wait publication .final ∧
      ∃ sumAcc maxAcc sumBytes maxBytes,
        X.Writes (terminalStatsProducer l store.1 stage,first) sumAcc sumBytes ∧
        X.Writes (terminalStatsProducer l store.1 stage,first+1) maxAcc maxBytes ∧
        ∀ word : Fin 2,
          baseCausality l X (terminalStatsProducer l store.1 stage,first+word.val)
            (store.1,wait+1+word.val) := by
  obtain ⟨publication, hPeer, _⟩ := terminalFinalPeerOfExit hp hX hCuQ hUsedK hRead hExit
  obtain ⟨first, hFirst, hWrites⟩ := terminalStoresPrecedeReads hp hX hRead hPeer
  exact ⟨publication, first, hFirst, hPeer, hWrites⟩

/-- In a complete execution, both actual correction reads have matching final stores. -/
theorem terminalStoresOfComplete (hCuQ : DrainCuQProtected p X) (hComplete : Complete l X)
    {store : EvId} {stage : Fin 2} {wait : Nat} {sum maximum : List (Option Byte)}
    (hRead : TerminalLseReads l X store stage wait sum maximum) :
    ∃ publication first, first + 2 = publication ∧
      TerminalPeer l X store.1 stage wait publication .final ∧
      ∃ sumAcc maxAcc sumBytes maxBytes,
        X.Writes (terminalStatsProducer l store.1 stage,first) sumAcc sumBytes ∧
        X.Writes (terminalStatsProducer l store.1 stage,first+1) maxAcc maxBytes ∧
        ∀ word : Fin 2,
          baseCausality l X (terminalStatsProducer l store.1 stage,first+word.val)
            (store.1,wait+1+word.val) := by
  let producer := terminalStatsProducer l store.1 stage
  obtain ⟨e, he, _⟩ := hRead.terminal
  have hConsumer := Step.CtaBar.thread_lt_of_get hX he
  have hBlock : 0 < l.block := by rw [hp.block]; decide
  have hCta : store.1 / l.block < l.grid := (Nat.div_lt_iff_lt_mul hBlock).2 hConsumer
  have hProducer : producer < l.threads := (Nat.div_lt_iff_lt_mul hBlock).1
    ((terminalStatsCta hp store.1 stage).symm ▸ hCta)
  exact terminalStoresOfExit hp hX hCuQ (usedKProtected hp hX)
    hRead (Thread.exitedOfComplete hX hComplete hProducer)

/-- The matched producer's actual terminal words supply the LSE registers for any positive
number of key blocks once the producer's sum recurrence is established. -/
theorem terminalStatisticsOfPublishedWords {store : EvId} {stage : Fin 2}
    {first wait publication batch tile head blocks : Nat} {s : TState}
    {sum maximum : List (Option Byte)} {refs : Nat → Option ℝ} {sums : Nat → ℝ} {maxValue : ℝ}
    (hRead : TerminalLseReads l X store stage wait sum maximum)
    (hWindow : LseWindowInputs l X store stage first s sum maximum)
    (hPeer : TerminalPeer l X store.1 stage wait publication .final)
    (hVisits : SoftmaxSumRun p batch head (stageRow tile stage + rowOf l store.1) blocks refs sums)
    (hBlocks : blocks = Mma.trips p batch tile) (hPositive : 0 < blocks)
    (hReference : abiFloat p.scaleLog2Bits * maxValue = (refs (blocks - 1)).getD 0)
    (hWords : TerminalPublishedWords l X store.1 stage publication
      (fl (sums (blocks - 1))) (fl maxValue)) (hScale : s.regs 7134 = some (b32 p.scaleLog2Bits))
    (hSelector : stage = 0 → FirstLseSelector s sum) (hb : batch < p.batch)
    (hr : stageRow tile stage + rowOf l store.1 < p.qLength batch) :
    LseStatisticsAt p batch head (stageRow tile stage + rowOf l store.1) stage s := by
  let row := stageRow tile stage + rowOf l store.1
  obtain ⟨source, hSource, hGen, _⟩ := terminalStoresOfFinalPeer hX hPeer
  have hPos : publication - 2 = source := by omega
  have hGen' : TerminalGeneration l X store.1 stage (publication - 2) wait := hPos.symm ▸ hGen
  obtain ⟨hSum, hMax⟩ := hWords.reads hp hX hRead rfl rfl hGen'
  have hSumRebuilt := hSum.symm ▸ PTX.Proof.rebuild_scalar (v := fl (sums (blocks - 1)))
    (by change 0 < 4; decide) rfl
  have hMaxRebuilt := hMax.symm ▸ PTX.Proof.rebuild_scalar (v := fl maxValue)
    (by change 0 < 4; decide) rfl
  obtain ⟨hSumReg, hMaxReg⟩ := hWindow.loadedRegisters _ _ hSumRebuilt hMaxRebuilt
  have hRowTile : row < 256 * (tile + 1) := by
    have hLocal : rowOf l store.1 < 128 := Nat.mod_lt _ (by decide)
    have hStage := stage.isLt
    dsimp only [row, stageRow]
    omega
  have hCover := p.keyCount_le_kvBlocks (b := batch) hRowTile
  change p.keyCount batch row ≤ 128 * Mma.trips p batch tile at hCover
  rw [← hBlocks] at hCover
  refine ⟨blocks, refs, sums, maxValue, hVisits, hPositive, hCover, hSumReg, hMaxReg,
    hScale, hReference, ?_⟩
  intro hStage
  have hPositiveSum := hVisits.final_sum_pos hPositive (hp.keyCount_pos hb hr) hCover
  have hSelected := (hSelector hStage) _ hSumRebuilt
  simpa only [hStage, lsePredReg, Fin.val_zero, Nat.mul_zero, Nat.add_zero,
    decide_eq_true (ne_of_gt hPositiveSum)] using hSelected

end
end PTX.Kernels.TmlFa4Fwd.Protocol.Statistics
