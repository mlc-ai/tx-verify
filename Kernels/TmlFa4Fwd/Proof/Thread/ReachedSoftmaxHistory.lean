-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.ReachedTerminalSoftmaxRow
public import Kernels.TmlFa4Fwd.Proof.Thread.FirstProbabilityPublicationValues
import Kernels.TmlFa4Fwd.Proof.Thread.OpeningRoundNumerics
public import Kernels.TmlFa4Fwd.Proof.SoftmaxTerminalNumerics
public import Kernels.TmlFa4Fwd.Proof.Protocol.RecordedSoftmaxRowPrefix

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Correction
open PTX PTX.Proof PTX.Numeric Epilogue Prologue Protocol Thread.Scores
open _root_.PTX.Kernels.TmlFa4Fwd.Softmax

/-- The record after the last visit, with the running denominator and the unscaled
reference still resident in the softmax producer. -/
@[no_expose] def ReachedSoftmaxRowDrain (p : Params) (l : Launch) (X : Execution)
    (producer : Nat) (reference : Option ℝ) (sum : ℝ) : Prop :=
  ∃ (s : TState) (pos : Nat) (maximum : Option ℝ),
    reference = maximum.map (abiFloat p.scaleLog2Bits * ·) ∧
    s.pc = 7605 ∧ s.regs 7257 = some (fl sum) ∧ s.regs 7256 = some (scoreValue maximum) ∧
    Run kernel Assumptions.all l producer s ((X.tr producer).drop pos) none

theorem ReachedSoftmaxRowDrain.ofRecorded
    {p : Params} {l : Launch} {X : Execution} {producer pos : Nat}
    {reference maximum : Option ℝ} {sum : ℝ} {s : TState}
    (hReference : reference = maximum.map (abiFloat p.scaleLog2Bits * ·))
    (hPc : s.pc = 7605) (hSum : s.regs 7257 = some (fl sum))
    (hMax : s.regs 7256 = some (scoreValue maximum))
    (hRun : Run kernel Assumptions.all l producer s ((X.tr producer).drop pos) none) :
    ReachedSoftmaxRowDrain p l X producer reference sum :=
  ⟨s,pos,maximum,hReference,hPc,hSum,hMax,hRun⟩

/-- The last reference is finite for a live output row. -/
theorem ReachedSoftmaxRowDrain.terminalLane
    {p : Params} {l : Launch} {X : Execution} {producer batch head row blocks : Nat}
    {refs : Nat → Option ℝ} {sums : Nat → ℝ}
    (hDrain : ReachedSoftmaxRowDrain p l X producer (refs (blocks-1)) (sums (blocks-1)))
    (hRecurrence : SoftmaxSumRun p batch head row blocks refs sums)
    (hBlocks : 0 < blocks) (hKeys : 0 < p.keyCount batch row) :
    ∃ maximum, abiFloat p.scaleLog2Bits*maximum = (refs (blocks-1)).getD 0 ∧
      TerminalLaneValues l X producer (sums (blocks-1)) maximum := by
  obtain ⟨_,_,_,hRef,hPc,hSum,hMax,hRun⟩ := hDrain
  exact terminalLaneValuesOfFinishedSum hRecurrence hRef hBlocks hKeys hPc hSum hMax hRun

/-- Recover the first probability tile of any completed live lane and attach
it to the initial scalar row history. -/
theorem recordedOpeningSoftmaxRow {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hDone : Complete l X)
    (hFootprint : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {g batch : Nat} (hg : g < l.threads) (stage : Fin 2) (hStage : warpIndex l g/4 = stage.val)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) :
    let coords := assignedCoordinates p batch (g/l.block)
    let blocks := Mma.trips p batch coords.1
    let row := 128*(2*coords.1+stage.val)+g%l.block%128
    let mx := scoreMax (fun c => maskedLogit p batch coords.2 row (visitKey blocks 0 c))
      (List.range 128)
    let ref := mx.map (abiFloat p.scaleLog2Bits * ·)
    let mass := (2 : ℝ)^(-(ref.getD 0)) *
      maskedBlockSum (p.keyCount batch row) blocks 0 (weight p batch coords.2 row)
    row < p.qLength batch →
    RecordedSoftmaxRowPrefix p l X g batch coords.2 row stage blocks 1
      (fun _ => ref) (fun _ => mass) := by
  let coords := assignedCoordinates p batch (g/l.block)
  let blocks := Mma.trips p batch coords.1
  let row := 128*(2*coords.1+stage.val)+g%l.block%128
  let mx := scoreMax (fun c => maskedLogit p batch coords.2 row (visitKey blocks 0 c))
    (List.range 128)
  let ref := mx.map (abiFloat p.scaleLog2Bits * ·)
  dsimp only
  intro hRow
  have hWarp : warpIndex l g < 8 := by have := stage.isLt; omega
  let warp : Fin 8 := ⟨warpIndex l g,hWarp⟩
  have hStageEq : stageOf warp = stage := Fin.ext hStage
  have hLive : 128*(2*coords.1+warpIndex l g/4)+g%l.block%128 < p.qLength batch := by
    rwa [hStage]
  obtain ⟨_,hRound⟩ := openingRoundOfCompletedLane hp hX hDone hFootprint hg hWarp hb
    hLo hHi hLive
  have ht := hRound.observedProbabilityTile hp hX rfl
  change ObservedProbabilityTile l X g (stageOf warp) 0 (fun c =>
    shiftedWeight p batch coords.2 (128*(2*coords.1+(stageOf warp).val)+g%l.block%128)
      (visitKey blocks 0 c)
      (firstReference p batch coords.2 (128*(2*coords.1+(stageOf warp).val)+g%l.block%128)
        blocks)) at ht
  rw [hStageEq] at ht
  change ObservedProbabilityTile l X g stage 0 (fun c =>
    shiftedWeight p batch coords.2 row (visitKey blocks 0 c)
      (firstReference p batch coords.2 row blocks)) at ht
  have hRef : firstReference p batch coords.2 row blocks = ref.getD 0 := by
    change abiFloat p.scaleLog2Bits * mx.getD 0 =
      (mx.map (abiFloat p.scaleLog2Bits * ·)).getD 0
    cases mx <;> simp
  rw [hRef] at ht
  exact RecordedSoftmaxRowPrefix.first ref _ (openingSoftmaxSumPrefix p batch coords.2 row blocks)
    ht

end PTX.Kernels.TmlFa4Fwd.Thread.Correction
