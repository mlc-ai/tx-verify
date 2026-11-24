-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.ProbabilitySourceOrder
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvScoreRank
import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyProbabilityColumn
import Kernels.TmlFa4Fwd.Proof.Thread.TmemProbabilityReadGeometry

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Scores
open PTX PTX.TcMma Thread Thread.Scores
open _root_.PTX.Kernels.TmlFa4Fwd.Mma

/-- The actual P writer and the actual V acquire of a PV fragment belong to
the same logical visit of its physical stage. -/
theorem ProbabilityCellPublication.exactPvVisit {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X) {g index use d : Nat} {block : Fin 4}
    {step : Fin 8} {op : OperandSpec} {acc : Bool} {mask : List Nat} {cell : Cell}
    (seen : ProbabilityCellPublication l X (g,index) cell)
    (hRead : X.MmaACell (g,index) cell)
    (hPv : PvInstruction X (g,index) block step d op acc mask)
    (hUse : Mma.LatestValueReadyUse l X g index use) :
    seen.stage = (pvSite block).stage ∧ seen.phase = use/2 ∧
    ∃ obs : ProbabilityStoreScore l X seen.store seen.stage,
      scoreCommitOrdinal l X (g/l.block) seen.stage obs.commit = use/2 := by
  let stage := (pvSite block).stage
  have hIssue : X.MmaIssue (g,index) d op acc mask := ⟨_,hPv.decoded⟩
  have hCols := probabilityReadColumn hIssue stage step (hPv.probabilityAddress hp hX) hRead
  have hLo := seen.footprint.columnLo
  have hHi := seen.footprint.columnHi
  have hStep := step.isLt
  have hStage : seen.stage = stage := by
    apply Fin.ext
    simp only [TensorStoreTile.columns,probabilityColumn,scoreColumn] at hLo hHi hCols
    omega
  obtain ⟨obs,hExact,hCount⟩ := seen.exactScore hp hX hCuQ hRead
  have hCta : seen.store.1/l.block = g/l.block :=
    seen.footprint.cta.symm.trans (mmaAOperandCta hp hX hRead)
  have hScore : ScoreCommit l X obs.commit (g/l.block) stage obs.spec obs.rank :=
    hStage ▸ (hCta ▸ obs.score)
  have hBefore : scoreCommitOrdinal l X (g/l.block) stage (g,index) =
      scoreCommitOrdinal l X (g/l.block) stage obs.commit+1 := by
    rw [← hStage,hCount,hExact]
  have hOrdinal := hPv.valueUseOfLatestScoreCommit hp hX hUse hScore hBefore
  change scoreCommitOrdinal l X (g/l.block) stage obs.commit = use/2 at hOrdinal
  rw [← hStage] at hOrdinal
  exact ⟨hStage,hExact.symm.trans hOrdinal,obs,hOrdinal⟩

end PTX.Kernels.TmlFa4Fwd.Protocol.Scores
