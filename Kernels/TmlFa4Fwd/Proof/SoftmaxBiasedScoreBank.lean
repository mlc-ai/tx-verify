-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedVisitRank
public import Kernels.TmlFa4Fwd.Proof.SoftmaxObservedBiasedInputs
public import Kernels.TmlFa4Fwd.Proof.SoftmaxObservedQkBank

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.TcMma Prologue Thread Thread.Scores

/-- A biased score load identifies its stage and a strictly positive score generation. -/
theorem observedBiasedScoreBank {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X)
    {g pos : Nat} (stage : Fin 2) (q : Fin 4) (word : Fin 32) {xs : List Value}
    (he : X.get (g,pos) =
      some ⟨scorePc .biased q,.tc (.ld (scoreAddress l g stage q) xs .s32x32b)⟩) :
    warpIndex l g < 8 ∧ warpIndex l g/4 = stage.val ∧
    ∃ bank : ScoreQkBank l X (g,pos)
        (tcDataCell l g .s32x32b (scoreAddress l g stage q) word.val) stage,
      0 < scoreCommitOrdinal l X (g/l.block) stage bank.seen.commit := by
  obtain ⟨w,hw,hAddress,hLen,_⟩ := scoreLoadAddress hp hX .biased q he
  have hStage : warpIndex l g/4 = stage.val := by
    simp only [scoreAddress,scoreColumn] at hAddress
    rw [← hw]
    change (stageOf w).val = stage.val
    omega
  have hWarp : warpIndex l g < 8 := hw ▸ w.isLt
  have hWord : word.val < xs.length := by rw [hLen]; exact word.isLt
  obtain ⟨other,hCell⟩ := ScoreLoadCell.ofDecoded hp hX .biased q he hWord rfl
  obtain ⟨_,_,hOther,_,_⟩ := hCell.acquire hp hX
  have hEqual : other = stage := Fin.ext (hOther.symm.trans hStage)
  subst other
  obtain ⟨bank⟩ := observedScoreQkBank hp hX hCuQ hCell
  refine ⟨hWarp,hStage,bank,?_⟩
  rw [bank.seen.generation]
  exact biasedScoreHasEarlierVisit hp hX stage hWarp hStage q he

end PTX.Kernels.TmlFa4Fwd.Softmax
