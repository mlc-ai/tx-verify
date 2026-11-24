-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxOpeningBiasAcquire
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxActiveScoreProgress
public import Kernels.TmlFa4Fwd.Proof.OutputProtection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

set_option maxRecDepth 2000 in
/-- Each lane of the actual selected warp returns from the opening score acquire at
Tensor Memory collective ordinal zero, with its Bias register frame intact. -/
theorem openingScoreReturnedWarpOfSelected {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch count : Nat} (hg : g < l.threads) (hw : warpIndex l g < 8)
    (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch+1) * p.heads)
    (hCuQ : DrainCuQProtected p X) (hUsedK : UsedKProtected p X)
    {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 3274
      (fun _ => firstActiveTileFacts p l g ⟨warpIndex l g,hw⟩ batch) count 1 ends)
    (hAck : ∀ peer, SameWarp l g peer → (¬ ∃ j, Thread.Scores.CreditAcquired X (peer,j)) →
      OpeningPollReady X (waitLoc l peer (stageOf ⟨warpIndex l g,hw⟩) 0) 1)
    (hScore : ∀ peer, SameWarp l g peer →
      (¬ ∃ j, Thread.Scores.FirstScoreAcquire l X (peer,j) (stageOf ⟨warpIndex l g,hw⟩)) →
      OpeningPollReady X (waitLoc l peer (stageOf ⟨warpIndex l g,hw⟩) 1) 0) :
    let warp : Fin 8 := ⟨warpIndex l g,hw⟩
    let F := fun lane => openingScoreReturnedFacts p l (warpLane l g lane) batch
      (assignedCoordinates p batch (g/l.block)).1 warp
    ∃ after : ∀ lane < 32, OpeningLaneCursor l X (warpLane l g lane) 3428 (F lane) (ends lane),
      ∀ lane (hl : lane < 32), ∃ j,
        Thread.Scores.FirstScoreAcquire l X (warpLane l g lane,j) (stageOf warp) ∧
        (after lane hl).pos = j+1 ∧
        ((X.tr (warpLane l g lane)).take (after lane hl).pos).countP isTcColl = 0 := by
  classical
  dsimp only
  let warp : Fin 8 := ⟨warpIndex l g,hw⟩
  let thread := warpLane l g
  let tile := (assignedCoordinates p batch (g/l.block)).1
  let F := fun lane => openingScoreReturnedFacts p l (thread lane) batch tile warp
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have each (lane : Nat) (hl : lane < 32) :
      ∃ after : OpeningLaneCursor l X (thread lane) 3428 (F lane) (ends lane), ∃ j,
        Thread.Scores.FirstScoreAcquire l X (thread lane,j) (stageOf warp) ∧
        after.pos = j+1 ∧ ((X.tr (thread lane)).take after.pos).countP isTcColl = 0 := by
    have hSame := (Step.sameWarp_lane hBlock hg hl).1
    have hCta : thread lane / l.block = g / l.block := hSame.1.2.2.symm
    have hAt : At (cur.state lane) 3274 (firstActiveTileFacts p l (thread lane) warp batch) := by
      simpa only [firstActiveTileFacts,hCta] using cur.checkpoint lane hl
    let c : OpeningLaneCursor l X (thread lane) 3274
        (firstActiveTileFacts p l (thread lane) warp batch) (ends lane) :=
      ⟨cur.pos lane,cur.before lane,cur.state lane,cur.positive lane hl,cur.bounded lane hl,
        cur.released lane hl,cur.recorded lane hl,cur.continuation lane hl,
        cur.localSteps lane hl,hAt⟩
    have hTile := (assignedCoordinates_valid hp hLo hHi).1
    have hTile' : 256*(assignedCoordinates p batch (thread lane/l.block)).1 < p.qLength batch := by
      rwa [hCta]
    obtain ⟨_,j,_,he,_,_,after,hPos⟩ :=
      openingScoreReturnOfSelected hp hMax hSame.1.2.1 warp hb hTile' c
        (fun off ho => hCuQ (batch+off) (by omega)) (hUsedK batch hb)
        (hAck _ hSame) (hScore _ hSame)
    have hA : Thread.Scores.FirstScoreAcquire l X (thread lane,j) (stageOf warp) :=
      Thread.Scores.FirstScoreAcquire.ofDecoded he
    have hCount := openingScoreLoadOrdinal hp hMax.1 hA
    have hFrame : openingScoreReturnedFacts p l (thread lane) batch
        (assignedCoordinates p batch (thread lane/l.block)).1 warp = F lane := by rw [hCta]
    have hFrame' : Holds after.ready.regs (F lane) := hFrame ▸ after.checkpoint.2.2.2.2
    let result : OpeningLaneCursor l X (thread lane) 3428 (F lane) (ends lane) :=
      after.weaken hFrame'
    have hPos' : result.pos = j+1 := hPos
    have hFinal : ((X.tr (thread lane)).take result.pos).countP isTcColl = 0 := by
      rw [hPos']
      exact hCount
    exact ⟨result,j,hA,hPos',hFinal⟩
  choose after hAfter using each
  exact ⟨after,hAfter⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax
