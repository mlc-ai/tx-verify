-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.CorrectionFinalStats
public import Kernels.TmlFa4Fwd.Proof.SoftmaxTerminalPublish
public import Kernels.TmlFa4Fwd.Proof.SoftmaxNumerics
public import Lemmas.Protocol.NamedBarArrive
public import Lemmas.Order.ReadLast
import Lemmas.Step.CtaBar

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction

open PTX PTX.Flow PTX.Proof Prologue Epilogue

noncomputable section

/-- The two terminal words are written by the softmax lane with the same row in that stage. -/
def terminalStatsProducer (l : Launch) (g : Nat) (stage : Fin 2) : Nat :=
  (g / l.block) * l.block + 128 * stage.val + rowOf l g

def terminalStatsWarp (l : Launch) (g : Nat) (stage : Fin 2) : Fin 8 :=
  ⟨rowOf l g / 32 + 4 * stage.val, by
    have hRow : rowOf l g < 128 := Nat.mod_lt _ (by decide)
    have hStage := stage.isLt
    omega⟩

def finalStatsKind (word : Fin 2) : StatsKind :=
  if word = 0 then .sum else .maximum

def finalStatsWriteSite (word : Fin 2) : Fin 4 :=
  ⟨2 + word.val, by have := word.isLt; omega⟩

theorem terminalStatsCta {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (stage : Fin 2) : terminalStatsProducer l g stage / l.block = g / l.block := by
  have hRow : rowOf l g < 128 := Nat.mod_lt _ (by decide)
  have hStage := stage.isLt
  unfold terminalStatsProducer
  rw [hp.block]
  omega

private theorem terminalStatsLane {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (stage : Fin 2) : laneOf l (terminalStatsProducer l g stage) = rowOf l g % 32 := by
  have hRow : rowOf l g < 128 := Nat.mod_lt _ (by decide)
  have hStage := stage.isLt
  unfold terminalStatsProducer laneOf
  rw [hp.block]
  omega

theorem terminalStatsProducerWarp {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (stage : Fin 2) :
    warpIndex l (terminalStatsProducer l g stage) = (terminalStatsWarp l g stage).val := by
  have hRow : rowOf l g < 128 := Nat.mod_lt _ (by decide)
  have hStage := stage.isLt
  unfold warpIndex terminalStatsProducer terminalStatsWarp
  rw [hp.block]
  change ((g / 512 * 512 + 128 * stage.val + rowOf l g) % 512) / 32 =
    rowOf l g / 32 + 4 * stage.val
  omega

private theorem terminalStatsRowWarp (l : Launch) (g : Nat) :
    rowOf l g / 32 = warpIndex l g % 4 := by
  unfold rowOf warpIndex
  omega

/-- The same-row producer warp is paired with this correction stage's barrier. -/
theorem terminalStatsBarrier (l : Launch) (g : Nat) (stage : Fin 2) :
    3 + (terminalStatsWarp l g stage).val = statsBarrierId l g stage := by
  dsimp only [terminalStatsWarp, statsBarrierId]
  rw [terminalStatsRowWarp]
  omega

theorem terminalStatsLocation {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (g : Nat) (stage word : Fin 2) :
    (Softmax.statsAcc l (terminalStatsProducer l g stage) (terminalStatsWarp l g stage)
      (finalStatsWriteSite word)).loc = statsLoc l g stage (finalStatsKind word) := by
  have hOffset :
      (Softmax.statsStore (finalStatsWriteSite word)).offset + 512 * stage.val =
        statsOff stage (finalStatsKind word) := by
    fin_cases word <;> fin_cases stage <;> decide
  change Loc.mk .shared (terminalStatsProducer l g stage / l.block)
      (Softmax.statsBase l (terminalStatsProducer l g stage) (terminalStatsWarp l g stage) +
        (Softmax.statsStore (finalStatsWriteSite word)).offset) = _
  rw [terminalStatsCta hp]
  unfold Softmax.statsBase statsLoc
  rw [terminalStatsLane hp]
  congr 1
  change l.sharedBase + 4 * (32 * (rowOf l g / 32 + 4 * stage.val) + rowOf l g % 32) +
    (Softmax.statsStore (finalStatsWriteSite word)).offset =
      l.sharedBase + 4 * rowOf l g + statsOff stage (finalStatsKind word)
  omega

/-- The release generation and ordering of other writes to the reused statistics words.
The premises refer to the actual consumer synchronization and producer publication. -/
structure TerminalStatisticsPhase (l : Launch) (X : Execution) (g : Nat) (stage : Fin 2)
    (producerPos consumerPos : Nat) (members : Finset Nat) : Prop where
  sources : NamedBar.Sources l X (some 64) members (statsBarrierId l g stage)
  shape : NamedBar.Shape l (some 64) members (statsBarrierId l g stage)
  ordinal :
    ((X.tr (terminalStatsProducer l g stage)).take (producerPos + 2)).countP
        (Execution.isBarId (statsBarrierId l g stage)) =
      ((X.tr g).take consumerPos).countP (Execution.isBarId (statsBarrierId l g stage))
  writeOrder : ∀ (word : Fin 2) k, k < 4 →
    ∀ (w : AsyncCopy.Ref) a bytes, X.MemWrites w a bytes →
      let loc := (statsLoc l g stage (finalStatsKind word)).at k
      let writer := AsyncCopy.Ref.thread (terminalStatsProducer l g stage, producerPos + word.val)
      let reader := AsyncCopy.Ref.thread (g, consumerPos + 1 + word.val)
      a.Covers loc →
        w = writer ∨ modelCausality l X loc w writer ∨ modelCausality l X loc reader w

/-- The selected producer's last numerical visit at the sum/max publication cursor. -/
structure TerminalSoftmaxStatistics (p : Params) (l : Launch) (g batch tile head : Nat)
    (stage : Fin 2) (t : TState) (blocks : Nat) (refs : Nat → Option ℝ) (sums : Nat → ℝ)
    (maximum : ℝ) : Prop where
  visits : SoftmaxSumRun p batch head (stageRow tile stage + rowOf l g) blocks refs sums
  positiveCount : 0 < blocks
  coversRow : p.keyCount batch (stageRow tile stage + rowOf l g) ≤ 128 * blocks
  reference : abiFloat p.scaleLog2Bits * maximum = (refs (blocks - 1)).getD 0
  atPublication : At t 7614
    [(5814, b32 (Softmax.statsBase l (terminalStatsProducer l g stage)
      (terminalStatsWarp l g stage))), (7257, fl (sums (blocks - 1))), (7256, fl maximum),
      (5127, b32 (3 + (terminalStatsWarp l g stage).val))]

end
end PTX.Kernels.TmlFa4Fwd.Correction
