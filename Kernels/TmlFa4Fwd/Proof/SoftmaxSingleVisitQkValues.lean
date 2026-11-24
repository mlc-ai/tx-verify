-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxObservedQk
public import Kernels.TmlFa4Fwd.Proof.Protocol.InitialQueryValues
public import Kernels.TmlFa4Fwd.Proof.Protocol.InitialKeyValues
import Kernels.TmlFa4Fwd.Proof.Thread.InitialKeyOperandFrame

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.AsyncCopy PTX.TcMma
open Epilogue (assignedCoordinates)

/-- The observed initial score notification identifies the eight canonical QK fragments
on the final output issuer, including their true destination and accumulator flags. -/
theorem firstObservedQkIssues {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {stage : Fin 2} {producer consumer commit wait : Nat}
    (hPhase : FirstQkPhase l X stage producer consumer commit wait)
    {output : EvId} {s : TcCommit.Spec} (hOutput : Thread.SecondOutputCommit X output s)
    (hOutputCta : producer / l.block = output.1 / l.block) :
    ∃ start, ∀ step : Fin 8, X.get (producer, start + step.val) =
      some (Mma.qkIssueEvent l producer (firstQkBlock stage) step 0) := by
  have hLane := Thread.Mma.firstQkSecondOutputIssuer hp hX hPhase hOutput hOutputCta
  obtain ⟨base,hFrags⟩ :=
    Thread.initialCanonicalQkIssuesBeforeSecondOutputCommit hp hX hOutput stage
  refine ⟨base,?_⟩
  intro step
  obtain ⟨_,he,_⟩ := hFrags step
  exact hLane.symm ▸ he

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hDone : Complete l X)
    (hFrame : OutputFootprint p X) {batch : Nat} {stage : Fin 2}
    {producer consumer commit wait start read : Nat} (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ producer / l.block)
    (hHi : producer / l.block < tilePrefix p (batch + 1) * p.heads)
include hp hX hDone hFrame hb hLo hHi

/-- The actual initial QK score is the dot product of its observed Q and priming K
operands when the TMEM accumulator and the consuming load preserve its result. -/
theorem firstObservedScoreWordOfInitialOperands
    (hPhase : FirstQkPhase l X stage producer consumer commit wait) {output : EvId}
    {s : TcCommit.Spec} (hOutput : Thread.SecondOutputCommit X output s)
    (hOutputCta : producer / l.block = output.1 / l.block) (hAfter : wait < read)
    (hIssues : ∀ step : Fin 8, X.get (producer, start + step.val) =
      some (Mma.qkIssueEvent l producer (firstQkBlock stage) step 0)) (q : Fin 4) (word : Fin 32)
    {vals : List Value}
    (he : X.get (consumer, read) = some
      ⟨scorePc .first q, .tc (.ld (scoreAddress l consumer stage q) vals .s32x32b)⟩)
    (hPrior : ∀ step : Fin 8, step.val ≠ 0 →
      ReadSource l X .acc (producer, start + (step.val - 1)) (producer, start + step.val)
        (tcDataCell l consumer .s32x32b (scoreAddress l consumer stage q) word.val))
    (hOutside : ∀ other,
      let cell := tcDataCell l consumer .s32x32b (scoreAddress l consumer stage q) word.val
      (X.MmaCell other cell ∨ StoreCell l X other cell) →
      (∀ step : Fin 8, other ≠ (producer, start + step.val)) →
        WriteBefore l X other (producer, start + 7) ∨ ReadBefore l X .ld (consumer, read) other)
    (hLive : SourceLive l X (producer, start + 7) (consumer, read)
      (tcDataCell l consumer .s32x32b (scoreAddress l consumer stage q) word.val)) :
    let coords := assignedCoordinates p batch (producer / l.block)
    let firstQ := p.qOffset batch + 256 * coords.1 + 128 * stage.val
    let firstK := 128 * (Mma.trips p batch coords.1 - 1)
    vals[word.val]? =
      some (.float .f32 (firstScoreDot p l consumer batch coords.2 firstQ firstK q word)) := by
  dsimp only
  let block := firstQkBlock stage
  let coords := assignedCoordinates p batch (producer / l.block)
  let firstQ := p.qOffset batch + 256 * coords.1 + 128 * stage.val
  let firstK := 128 * (Mma.trips p batch coords.1 - 1)
  let row := tmemRow l consumer
  let col := firstScoreColumn q word
  have hInit (step : Fin 8) :
      Thread.Mma.InitialQueryFragment X stage (producer, start + step.val) :=
    Thread.Mma.initialQueryFragmentOfIssue step 0 (hIssues step)
  have hIssue (step : Fin 8) : X.MmaIssue (producer, start + step.val)
      (scoreColumn (Mma.qkStage block)) (Mma.qkOperands l producer block step 0)
      (decide (step.val ≠ 0)) (List.replicate 4 0) := ⟨_, hIssues step⟩
  have hInputs : Mma.QkCellInputs p l X producer block 0 batch coords.2 firstQ firstK row col
      (fun step => (producer, start + step.val)) := by
    constructor
    · intro step k byte hk hByte
      exact Protocol.initialQueryOperandByte hp hX hDone hFrame hb hLo hHi hPhase
        step row.isLt hk hByte (hInit step) (hIssue step)
    · intro step k byte hk hByte
      exact Protocol.initialKeyOperandByte hp hX hDone hFrame hb hLo hHi
        hPhase (hInit step) hOutput hOutputCta step col.isLt hk hByte (hIssue step)
  exact firstObservedQkScoreWord hX hPhase hAfter hIssues q word he hInputs hPrior hOutside hLive

/-- The initial score of a single-visit tile is the dot product of its observed Q and K
operands, with the TMEM accumulator and allocation order supplied by the score protocol. -/
theorem firstObservedSingleVisitScoreWord
    (hTrip : Mma.trips p batch (assignedCoordinates p batch (producer / l.block)).1 = 1)
    (hPhase : FirstQkPhase l X stage producer consumer commit wait) {output : EvId}
    {s : TcCommit.Spec} (hOutput : Thread.SecondOutputCommit X output s)
    (hOutputCta : producer / l.block = output.1 / l.block) (hAfter : wait < read)
    (hIssues : ∀ step : Fin 8, X.get (producer, start + step.val) =
      some (Mma.qkIssueEvent l producer (firstQkBlock stage) step 0)) (q : Fin 4) (word : Fin 32)
    {vals : List Value}
    (he : X.get (consumer, read) = some
      ⟨scorePc .first q, .tc (.ld (scoreAddress l consumer stage q) vals .s32x32b)⟩)
    (hPrior : ∀ step : Fin 8, step.val ≠ 0 →
      ReadSource l X .acc (producer, start + (step.val - 1)) (producer, start + step.val)
        (tcDataCell l consumer .s32x32b (scoreAddress l consumer stage q) word.val))
    (hOutside : ∀ other,
      let cell := tcDataCell l consumer .s32x32b (scoreAddress l consumer stage q) word.val
      (X.MmaCell other cell ∨ StoreCell l X other cell) →
      (∀ step : Fin 8, other ≠ (producer, start + step.val)) →
        WriteBefore l X other (producer, start + 7) ∨ ReadBefore l X .ld (consumer, read) other)
    (hLive : SourceLive l X (producer, start + 7) (consumer, read)
      (tcDataCell l consumer .s32x32b (scoreAddress l consumer stage q) word.val)) :
    let coords := assignedCoordinates p batch (producer / l.block)
    let firstQ := p.qOffset batch + 256 * coords.1 + 128 * stage.val
    vals[word.val]? =
      some (.float .f32 (firstScoreDot p l consumer batch coords.2 firstQ 0 q word)) := by
  simpa only [hTrip,Nat.sub_self,Nat.mul_zero] using
    firstObservedScoreWordOfInitialOperands hp hX hDone hFrame hb hLo hHi
      hPhase hOutput hOutputCta hAfter hIssues q word he hPrior hOutside hLive

end PTX.Kernels.TmlFa4Fwd.Softmax
