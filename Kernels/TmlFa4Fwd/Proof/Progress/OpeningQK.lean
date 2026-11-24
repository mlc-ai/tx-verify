-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningCacheReady
public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderActualReady
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaOpeningCursor
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaInitialScoreIssue
import Kernels.TmlFa4Fwd.Proof.Thread.MmaFirstGroupShuffles

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Proof Prologue Epilogue

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X) {g batch : Nat}
    (hg : g < l.threads) (hw : warpIndex l g = 12) (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
include hp hMax hFrame hg hw hb hLo hHi

/-- Every active MMA warp issues its opening QK packet and the matching stage-zero score commit. -/
theorem openingScoreCommitAndQueryOperandsOfMaximal :
    ∃ shuffles votes ends,
      Mma.OpeningSecondQueryMmaReachedWithOperands l X g shuffles votes ends ∧
      ∃ (issuer index : Nat), SameWarp l g issuer ∧
      (∀ i : Fin 8, Thread.Mma.InitialQueryFragment X 0 (issuer,index+i.val) ∧
        X.MmaIssue (issuer,index+i.val) (scoreColumn 0)
          (Mma.qkOperands l issuer 0 i 0) (decide (i.val ≠ 0)) (List.replicate 4 0)) ∧
      Thread.Scores.ScoreCommit l X (issuer,index+9) (issuer/l.block) 0
        (Mma.commitSpec l issuer (l.sharedBase+80)) 0 ∧
      Thread.Scores.OpeningScoreCommit X (issuer,index+9) 0
        (Mma.commitSpec l issuer (l.sharedBase+80)) := by
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hProtect : Epilogue.DrainCuQProtected p X :=
    hp.cuQ_protected (fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame)
  let shuffles := 11 + 7 * (batch / 31)
  let count := if batch % 31 = 0 then shuffles + 1 else shuffles + 2
  have hMetadata (lane : Nat) (hl : lane < 32) :
      Mma.OpeningMetadataCounts l X (warpLane l g lane) count 1 := by
    have hs : SameWarp l g (warpLane l g lane) := (Step.sameWarp_lane hBlock hg hl).1
    obtain ⟨pos,t,u,_,_,_,hS,hV,_,hAt,hPast,hLocal,_⟩ :=
      Thread.Allocation.mmaMetadataOfMaximal hp hMax hs.1.2.1 (hs.2.symm.trans hw)
        hProtect hb (hs.1.2.2 ▸ hLo) (hs.1.2.2 ▸ hHi)
    exact ⟨pos,t,u,hAt.1,hPast,hLocal,hS,hV⟩
  have hK (lane : Nat) (hl : lane < 32) :
      ∃ j, Thread.Mma.ReadyPoll l X (warpLane l g lane) j 0 0 true .cta ∧
        (Thread.Mma.atPrefix l X (warpLane l g lane) j).kvAcquires 0 = 0 := by
    have hs : SameWarp l g (warpLane l g lane) := (Step.sameWarp_lane hBlock hg hl).1
    exact openingKeyAcquireOfMaximal hp hMax hFrame hs.1.2.1 (hs.2.symm.trans hw)
      hb (hs.1.2.2 ▸ hLo) (hs.1.2.2 ▸ hHi)
  obtain ⟨_,⟨cur⟩⟩ := Mma.openingQKWarpOfAcquires hp hMax hg hw hMetadata hK
  exact ⟨_,_,_,Mma.openingScoreCommitAndQueryOperandsFromWarp hp hMax hg cur⟩

/-- Every active MMA warp issues its opening QK packet and the matching stage-zero score commit. -/
theorem openingScoreCommitAndQueryCursorOfMaximal :
    ∃ shuffles votes ends,
      Mma.OpeningSecondQueryMmaReached l X g shuffles votes ends ∧
      ∃ (issuer index : Nat), SameWarp l g issuer ∧
      (∀ i : Fin 8, Thread.Mma.InitialQueryFragment X 0 (issuer,index+i.val) ∧
        X.MmaIssue (issuer,index+i.val) (scoreColumn 0)
          (Mma.qkOperands l issuer 0 i 0) (decide (i.val ≠ 0)) (List.replicate 4 0)) ∧
      Thread.Scores.ScoreCommit l X (issuer,index+9) (issuer/l.block) 0
        (Mma.commitSpec l issuer (l.sharedBase+80)) 0 ∧
      Thread.Scores.OpeningScoreCommit X (issuer,index+9) 0
        (Mma.commitSpec l issuer (l.sharedBase+80)) := by
  obtain ⟨shuffles,votes,ends,⟨cur⟩,hCommit⟩ :=
    openingScoreCommitAndQueryOperandsOfMaximal hp hMax hFrame hg hw hb hLo hHi
  refine ⟨shuffles,votes,ends,?_,hCommit⟩
  exact cur.advanceLocal (G := fun _ => Mma.openingQueryAfterScoreFrame l)
    (fun lane hl => ⟨_,.refl,(cur.checkpoint lane hl).mono
      ((holds_append ..).mp (cur.checkpoint lane hl).2.2.2.2).1⟩)

/-- Every active MMA warp issues its opening QK packet and the matching stage-zero score commit. -/
theorem openingScoreCommitOfMaximal :
    ∃ (issuer index : Nat), SameWarp l g issuer ∧
      (∀ i : Fin 8, Thread.Mma.InitialQueryFragment X 0 (issuer,index+i.val) ∧
        X.MmaIssue (issuer,index+i.val) (scoreColumn 0)
          (Mma.qkOperands l issuer 0 i 0) (decide (i.val ≠ 0)) (List.replicate 4 0)) ∧
      Thread.Scores.ScoreCommit l X (issuer,index+9) (issuer/l.block) 0
        (Mma.commitSpec l issuer (l.sharedBase+80)) 0 ∧
      Thread.Scores.OpeningScoreCommit X (issuer,index+9) 0
        (Mma.commitSpec l issuer (l.sharedBase+80)) := by
  obtain ⟨_,_,_,_,hCommit⟩ :=
    openingScoreCommitAndQueryCursorOfMaximal hp hMax hFrame hg hw hb hLo hHi
  exact hCommit

end PTX.Kernels.TmlFa4Fwd.Progress
