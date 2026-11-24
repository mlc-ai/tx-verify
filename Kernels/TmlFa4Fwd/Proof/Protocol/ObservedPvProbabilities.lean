-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.ProbabilityVisitAlignment
public import Kernels.TmlFa4Fwd.Proof.Protocol.PvVisit
public import Kernels.TmlFa4Fwd.Proof.SoftmaxProbabilityOperandValues
import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueFrame
import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyProbabilityColumn
import Kernels.TmlFa4Fwd.Proof.Protocol.CorrectionProbabilityReuse

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX PTX.TcMma Thread Thread.Scores Protocol.Scores Softmax
open _root_.PTX.Kernels.TmlFa4Fwd.Mma

/-- Every selected probability store packs the values of its logical visit and row. -/
def PvProbabilityPacking (l : Launch) (X : Execution) (reader : EvId)
    (stage : Fin 2) (step : Fin 8) (row : Fin 128) (round : Nat) (weights : Nat → ℝ) : Prop :=
  ∀ (cell : Cell) (seen : ProbabilityCellPublication l X reader cell),
    X.MmaACell reader cell → cell.lane = row.val → seen.stage = stage → seen.phase = round →
    ∀ score : ProbabilityStoreScore l X seen.store seen.stage,
      scoreCommitOrdinal l X (reader.1/l.block) seen.stage score.commit = round →
      X.TSt seen.store (probabilityAddress l seen.store.1 stage (pvQuarter step))
        ((List.range 16).map (probabilityWord (fun i => weights (32*(pvQuarter step).val+i))))
        .s32x32b

/-- The chosen packed P word gives the BF16 element of the actual PV operand. -/
theorem PvVisit.probabilityElementOfPacking {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X)
    {g index use : Nat} {block : Fin 4} {row col : Fin 128}
    (visit : PvVisit l X g block use row col index) (weights : Nat → ℝ) (step : Fin 8)
    (hPack : PvProbabilityPacking l X (g,visit.issues step) (pvSite block).stage step
      row (use/2) weights)
    {ops : AsyncCopy.MmaOperands} (hObs : X.async.mmaOperands (g,visit.issues step) = some ops)
    {k : Nat} (hK : k < 16) :
    Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a row.val k =
      .ok (weights (16*step.val+k)) := by
  let stage := (pvSite block).stage
  let reader := (g,visit.issues step)
  let producer := probabilityProducer l (g/l.block) stage row.val
  have hCta : producer/l.block = g/l.block := by
    unfold producer probabilityProducer
    rw [hp.block]
    have := stage.isLt
    have := row.isLt
    omega
  have hRow : (tmemRow l producer).val = row.val := by
    change laneBase l producer + laneOf l producer = row.val
    unfold producer probabilityProducer laneBase laneOf
    rw [hp.block]
    have := stage.isLt
    have := row.isLt
    omega
  have hPv := visit.fragment step
  have hMma : X.MmaIssue reader (outputColumn stage) (pvOperands l g block step use)
      (visit.keep || decide (0 < step.val)) (List.replicate 4 0) := ⟨_,hPv.decoded⟩
  have hLo : (pvOperands l g block step use).lowCta = producer/l.block := hCta.symm
  have hAddr := hPv.probabilityAddress hp hX
  have hJoint : CorrectionJointGuards l X := correctionJointGuardsOfCuQ hp hX hCuQ
  have hByte (b : Nat) (hb : b < 2) :
      ops.a[qkByteIndex row.val k b]? =
        some (some ((Value.float .bf16 (weights (16*step.val+k))).byteAt b)) := by
    let byte : Fin 32 := ⟨2*k+b,by omega⟩
    let q := pvQuarter step
    let offset := 8*(step.val%2)+byte.val/4
    let cell := tcDataCell l producer .s32x32b (probabilityAddress l producer stage q) offset
    have hCell := pvFromProbability rfl hLo stage step byte hAddr
    have hRead : X.MmaACell reader cell := ⟨_,_,_,_,_,_,hMma,hCell⟩
    obtain ⟨seen⟩ := probabilityCellPublication hp hX hJoint hRead
    obtain ⟨hStage,hRound,score,hScore⟩ :=
      seen.exactPvVisit hp hX hCuQ hRead hPv (visit.ready step)
    have hLane : cell.lane = row.val := by
      have hCol : probabilityColumn stage+16*q.val < 512 := by
        have hLimit := probabilityColumn_range stage
        have hScore := scoreColumn_range stage
        have hQ := q.isLt
        omega
      unfold cell probabilityAddress
      rw [tcDataCell_warp32 l producer offset hCol]
      exact hRow
    have hOwner := seen.producer
    rw [hStage,hLane] at hOwner
    change seen.store.1 = producer at hOwner
    have hStore := hPack cell seen hRead hLane hStage hRound score hScore
    rw [hOwner] at hStore
    have hSrc := seen.readSource hp hX hCuQ hRead
    rw [← hRow]
    exact probabilityOperandByteOfStore hX stage step weights hK hb hMma rfl hLo hAddr
      hOwner hStore hObs hSrc
  exact idealBf16Element_of_bytes (hByte 0 (by decide)) (hByte 1 (by decide))

end PTX.Kernels.TmlFa4Fwd.Protocol
