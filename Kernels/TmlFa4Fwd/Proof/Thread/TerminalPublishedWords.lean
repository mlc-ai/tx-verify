-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionLseProducer
import Kernels.TmlFa4Fwd.Proof.Thread.TerminalStatisticsOrder

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Correction
open PTX PTX.Proof Softmax
open PTX.Kernels.TmlFa4Fwd.Correction

/-- The final publication identifies the two adjacent same-row producer stores. -/
structure TerminalPublishedWords (l : Launch) (X : Execution) (g : Nat)
    (stage : Fin 2) (publication : Nat) (sumValue maxValue : Value) : Prop where
  sumStore : X.get (terminalStatsProducer l g stage, publication-2) = some
    ⟨7614,.wr (statsAcc l (terminalStatsProducer l g stage) (terminalStatsWarp l g stage) 2)
      sumValue.toBytes⟩
  maxStore : X.get (terminalStatsProducer l g stage, publication-2+1) = some
    ⟨7615,.wr (statsAcc l (terminalStatsProducer l g stage) (terminalStatsWarp l g stage) 3)
      maxValue.toBytes⟩
  arrival : X.get (terminalStatsProducer l g stage, publication) =
    some ⟨7616,.bar (3+(terminalStatsWarp l g stage).val) (some 64) .arrive⟩
  length : 2 ≤ publication

/-- The ordered terminal reads return the words of their matched producer publication. -/
theorem TerminalPublishedWords.read {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g : Nat} {stage : Fin 2} {publication wait : Nat}
    {sumValue maxValue : Value}
    (hWait : CorrectionWaits X (g,wait) .terminal stage)
    (hWords : TerminalPublishedWords l X g stage publication sumValue maxValue)
    (hSizeSum : sumValue.bytes = 4) (hSizeMax : maxValue.bytes = 4)
    (hGeneration : TerminalGeneration l X g stage (publication-2) wait)
    (word : Fin 2) {bytes : List (Option Byte)}
    (hRead : X.Reads (g,wait+1+word.val)
      {loc := statsLoc l g stage (finalStatsKind word),size := 4} bytes) :
    bytes = (if word = 0 then sumValue else maxValue).toBytes.map some := by
  have hNotice : Scores.Publishes X
      (terminalStatsProducer l g stage,publication) .final :=
    ⟨_,hWords.arrival,rfl⟩
  have hOrder := terminalWordOrderOfFinalPublication hp hX (wait := wait) hNotice
  have hBar : X.get (terminalStatsProducer l g stage, publication-2+2) =
      some ⟨7616,.bar (3+(terminalStatsWarp l g stage).val) (some 64) .arrive⟩ := by
    simpa only [Nat.sub_add_cancel hWords.length] using hWords.arrival
  exact terminalStatWordReadOfEvents hp hX hWait hSizeSum hSizeMax
    hWords.sumStore hWords.maxStore hBar hGeneration hOrder word hRead

/-- The ordered terminal reads return the words of their matched producer publication. -/
theorem TerminalPublishedWords.reads {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {store : EvId} {stage : Fin 2} {publication wait : Nat}
    {sum maximum : List (Option Byte)} {sumValue maxValue : Value}
    (hRead : TerminalLseReads l X store stage wait sum maximum)
    (hWords : TerminalPublishedWords l X store.1 stage publication sumValue maxValue)
    (hSizeSum : sumValue.bytes = 4) (hSizeMax : maxValue.bytes = 4)
    (hGeneration : TerminalGeneration l X store.1 stage (publication-2) wait) :
    sum = sumValue.toBytes.map some ∧ maximum = maxValue.toBytes.map some := by
  exact ⟨hWords.read hp hX hRead.terminal hSizeSum hSizeMax hGeneration 0 hRead.sumRead,
    hWords.read hp hX hRead.terminal hSizeSum hSizeMax hGeneration 1 hRead.maxRead⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Correction
