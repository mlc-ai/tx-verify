-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.ObservedPvProbabilities
public import Kernels.TmlFa4Fwd.Proof.Protocol.ProbabilityNumericalStore
import Kernels.TmlFa4Fwd.Proof.Thread.TmemConflictGeometry
import Kernels.TmlFa4Fwd.Proof.Thread.TmemProbabilityReadGeometry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX PTX.Flow PTX.TcMma Thread Thread.Scores Protocol.Scores Softmax
open _root_.PTX.Kernels.TmlFa4Fwd.Mma (pvSite pvOperands)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hCuQ : Epilogue.DrainCuQProtected p X)
    {g index use : Nat} {block : Fin 4} {row col : Fin 128}
    (visit : PvVisit l X g block use row col index) (step : Fin 8) (weights : Nat → ℝ)
    (hTile : ObservedProbabilityTile l X
      (probabilityProducer l (g/l.block) (pvSite block).stage row.val)
      (pvSite block).stage (use/2) weights)
include hp hX hCuQ visit step weights hTile

/-- An observed packed probability tile supplies the PV operand of its actual
row and score visit. -/
theorem PvVisit.probabilityPackingOfTile :
    PvProbabilityPacking l X (g,visit.issues step) (pvSite block).stage step row (use/2)
      weights := by
  intro cell seen hRead hRow hStage hRound _ _
  let stage := (pvSite block).stage
  let producer := probabilityProducer l (g/l.block) stage row.val
  let q := pvQuarter step
  have hOwner := seen.producer
  rw [hStage,hRow] at hOwner
  change seen.store.1 = producer at hOwner
  have hCta : producer/l.block = g/l.block := by
    unfold producer probabilityProducer
    rw [hp.block]
    have := stage.isLt
    have := row.isLt
    omega
  have hLane : laneBase l producer + laneOf l producer = row.val := by
    unfold producer probabilityProducer laneBase laneOf
    rw [hp.block]
    have := stage.isLt
    have := row.isLt
    omega
  have hPv := visit.fragment step
  have hAddress := hPv.probabilityAddress hp hX
  have hBounds := probabilityReadColumn ⟨_,hPv.decoded⟩ stage step hAddress hRead
  have hOff : 16*q.val ≤ 8*step.val ∧ 8*step.val+8 ≤ 16*q.val+16 := by
    change 16*(step.val/2) ≤ 8*step.val ∧ 8*step.val+8 ≤ 16*(step.val/2)+16
    omega
  let word : Fin 16 := ⟨cell.column-(probabilityColumn stage+16*q.val),by omega⟩
  have hCol : probabilityColumn stage+16*q.val < 512 := by
    have := probabilityColumn_range stage
    have := scoreColumn_range stage
    have := q.isLt
    omega
  have hCell : tcDataCell l producer .s32x32b (probabilityAddress l producer stage q)
      word.val = cell := by
    rw [probabilityAddress,tcDataCell_warp32 l producer word.val hCol,hCta,hLane]
    have hScope := mmaAOperandCta hp hX hRead
    have hColumn : probabilityColumn stage+16*q.val+word.val = cell.column := by
      dsimp only [word]
      omega
    change (⟨g/l.block,row.val,probabilityColumn stage+16*q.val+word.val⟩ : Cell) = cell
    cases cell
    rw [Cell.mk.injEq]
    exact ⟨hScope.symm,hRow.symm,hColumn⟩
  obtain ⟨idx,hWord,hRank,hStore⟩ := hTile q word
  rw [hCell] at hWord
  have hPack : PublishedProbabilityWord l X (producer,idx) cell seen.stage := hStage.symm ▸ hWord
  have hRank' : okPolls (scoreReadyObject l (g/l.block) seen.stage)
      ((X.tr producer).take idx) = seen.phase+1 := by
    rw [hStage,hRound,← hCta]
    exact hRank
  have hId := seen.eq_of_publishedWord hp hX hCuQ hRead hPack hRank'
  rw [hOwner]
  rw [hId] at hStore
  exact hStore

/-- Each recorded A operand element of a completed PV visit has the BF16 value
packed by its actual producer. -/
theorem PvVisit.probabilityElementOfTile {ops : AsyncCopy.MmaOperands}
    (hOperands : X.async.mmaOperands (g,visit.issues step) = some ops) {k : Nat} (hk : k < 16) :
    Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a row.val k =
      .ok (weights (16*step.val+k)) :=
  visit.probabilityElementOfPacking hp hX hCuQ weights step
    (visit.probabilityPackingOfTile hp hX hCuQ step weights hTile) hOperands hk

end PTX.Kernels.TmlFa4Fwd.Protocol
