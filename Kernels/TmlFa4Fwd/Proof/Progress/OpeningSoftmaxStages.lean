-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningScoreReady
public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningSecondScoreReady
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxActiveScoreProgress
import Kernels.TmlFa4Fwd.Proof.Protocol.IdleStatisticsCredit
import Kernels.TmlFa4Fwd.Proof.OutputProtection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX Prologue Epilogue PTX.MBarrier Thread.Scores

/-- Opening score readiness for the softmax lane's actual stage. -/
theorem openingScoreReadyForSoftmaxStage {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X)
    {g batch : Nat} (hg : g < l.threads) (stage : Fin 2) (hw : warpIndex l g/4 = stage.val)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hMissing : ¬ ∃ j, FirstScoreAcquire l X (g,j) stage) :
    let log := X.objects (scoreReadyObject l (g/l.block) stage)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 1 := by
  fin_cases stage
  · exact openingScoreReadyPhaseForPendingLane hp hMax hFrame hg
      (by change warpIndex l g / 4 = 0 at hw; omega) hb hLo hHi hMissing
  · exact openingSecondScoreReadyPhaseForPendingLane hp hMax hFrame hg hw hb hLo hHi hMissing

/-- Each active softmax lane of either stage successfully acquires its opening score
in a maximal execution. -/
theorem openingSoftmaxAcquireOfAllStages {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X)
    {g batch : Nat} (hg : g < l.threads) (stage : Fin 2) (hRole : warpIndex l g/4 = stage.val)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) :
    ∃ j, FirstScoreAcquire l X (g,j) stage := by
  have hWarp : warpIndex l g < 8 := by have h := stage.isLt; omega
  let warp : Fin 8 := ⟨warpIndex l g,hWarp⟩
  have hStage : Softmax.stageOf warp = stage := Fin.ext hRole
  have hCuQ : DrainCuQProtected p X :=
    hp.cuQ_protected (fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame)
  have hUsedK := usedKProtected hp hMax.1
  obtain ⟨j,hJ⟩ := Softmax.stageScoreAcquireOfMaximal hp hMax hg hWarp hCuQ hb hLo hHi
    (fun off hof => hCuQ (batch+off) (by omega)) (hUsedK batch hb)
    (fun hMissing => by
      obtain ⟨s,hs,hPhase⟩ := Protocol.Statistics.initialStatisticsPhaseZeroForPendingLane
        hp hMax hCuQ hg hWarp stage hRole.symm hMissing
      rw [hStage]
      exact ⟨s,hs,by rw [hPhase]; decide⟩)
    (fun hMissing => by
      rw [hStage] at hMissing ⊢
      obtain ⟨s,hs,hPhase⟩ :=
        openingScoreReadyForSoftmaxStage hp hMax hFrame hg stage hRole hb hLo hHi hMissing
      exact ⟨s,hs,by rw [hPhase]; decide⟩)
  exact ⟨j,hStage ▸ hJ⟩

end PTX.Kernels.TmlFa4Fwd.Progress
