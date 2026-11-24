-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxRecurringScoreValue
import Kernels.TmlFa4Fwd.Proof.SoftmaxOpeningScoreValue
import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedVisitRank
import Kernels.TmlFa4Fwd.Proof.Thread.BiasReadAddress
import Kernels.TmlFa4Fwd.Proof.Thread.ScoreActive

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.TcMma Epilogue Prologue Thread.Scores

/-- Every actual score load returns the selected descending QK dots on any consistent
prefix. The score commit proves that the lane's CTA owns an active request. -/
theorem scoreLoadWordsOfLaunch {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) (round : Round) (q : Fin 4)
    {g pos address : Nat} {values : List Value} {shape : TcShape}
    (he : X.get (g,pos) = some ⟨scorePc round q,.tc (.ld address values shape)⟩) :
    ∃ (stage : Fin 2) (batch : Nat), warpIndex l g/4 = stage.val ∧ batch < p.batch ∧
      tilePrefix p batch*p.heads ≤ g/l.block ∧ g/l.block < tilePrefix p (batch+1)*p.heads ∧
      ∀ word : Fin 32,
        let coords := assignedCoordinates p batch (g/l.block)
        let visit := probabilityOrdinal l X (g/l.block) stage 0 (g,pos)
        values[word.val]? = some (.float .f32
          (firstScoreDot p l g batch coords.2 (p.qOffset batch+256*coords.1+128*stage.val)
            (128*(Mma.trips p batch coords.1-1-visit)) q word)) := by
  let hCuQ := (hFrame.metadataProtected hp).1
  obtain ⟨warp,hWarp,hAddr,hLen,rfl⟩ := scoreLoadAddress hp hX round q he
  let stage := stageOf warp
  have hRole : warpIndex l g/4 = stage.val := by change _ = warp.val/4; rw [hWarp]
  subst address
  have hBank (word : Fin 32) : Nonempty (ScoreQkBank l X (g,pos)
      (tcDataCell l g .s32x32b (scoreAddress l g stage q) word.val) stage) := by
    have hIndex : word.val < values.length := hLen.symm ▸ word.isLt
    obtain ⟨other,hCell⟩ := ScoreLoadCell.ofDecoded hp hX round q he hIndex rfl
    obtain ⟨_,_,hOther,_,_⟩ := hCell.acquire hp hX
    have hStage : other = stage := Fin.ext (hOther.symm.trans hRole)
    subst other
    exact observedScoreQkBank hp hX hCuQ hCell
  obtain ⟨initial⟩ := hBank 0
  have hOwner := (scoreCommitActor hp hX initial.seen.score).1
  have hCommit := initial.seen.score
  rw [← hOwner] at hCommit
  have hActive := hOwner ▸ scoreCommitActive hp hX hCuQ hCommit
  obtain ⟨batch,⟨hb,hLo,hHi⟩,_⟩ := tileBatch_existsUnique p hActive
  refine ⟨stage,batch,hRole,hb,hLo,hHi,?_⟩
  intro word
  obtain ⟨bank⟩ := hBank word
  by_cases hFirst : round = .first
  · subst round
    have hZero := openingScoreLoadGeneration hp hX stage hRole q he
    have hValue := bank.wordOfOpeningInputs hp hX hFrame hCuQ q word he hZero hb hLo hHi
    dsimp only
    rw [hZero,Nat.sub_zero]
    exact hValue
  · have hWarpBound : warpIndex l g < 8 := hWarp ▸ warp.isLt
    have hPrevious := repeatedScoreHasEarlierVisit hp hX stage hWarpBound hRole round hFirst q he
    have hPositive : 0 < scoreCommitOrdinal l X (g/l.block) stage bank.seen.commit :=
      bank.seen.generation.symm ▸ hPrevious
    have hActor := (scoreCommitActor hp hX bank.seen.score).1
    have hValue := bank.recurringWordOfLaunchInputsInPrefix hp hX hCuQ hFrame q word he
      hPositive (batch := batch) hb (hActor.symm ▸ hLo) (hActor.symm ▸ hHi)
    have hRank : scoreCommitOrdinal l X (g/l.block) (stageOf warp) bank.seen.commit =
        probabilityOrdinal l X (g/l.block) stage 0 (g,pos) := bank.seen.generation
    rw [hRank] at hValue
    simpa only [hActor] using hValue

end PTX.Kernels.TmlFa4Fwd.Softmax
