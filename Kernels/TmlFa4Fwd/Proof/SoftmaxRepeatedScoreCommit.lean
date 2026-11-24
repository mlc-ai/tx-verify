-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxObservedQkBank
import Kernels.TmlFa4Fwd.Proof.Thread.BiasReadAddress
public import Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedScoreTrace
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.MBarrier PTX.Proof PTX.Flow Thread.Scores Protocol.Scores

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- The four load quarters in a repeated score replay observe the same actual
MMA score commit. An explicit load wait consumes a trace position in the plain round. -/
theorem repeatedScoreCommitsAgree (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (mode : Repeated) (stage : Fin 2) {g start : Nat} (values : Fin 4 → List Value)
    (hLoad : ∀ quarter : Fin 4,
      X.get (g,start+repeatedScoreStride mode*quarter.val) =
        some ⟨scorePc mode.round quarter,.tc
          (.ld (scoreAddress l g stage quarter) (values quarter) .s32x32b)⟩)
    (hWait : mode = .unbiased → ∀ quarter : Fin 4,
      X.get (g,start+repeatedScoreStride mode*quarter.val+1) =
        some ⟨scorePc mode.round quarter,.tc .waitLd⟩)
    (seen : ∀ quarter : Fin 4,
      ScoreLoadScore l X (g,start+repeatedScoreStride mode*quarter.val) stage) (a b : Fin 4)
    : (seen a).commit = (seen b).commit := by
  let cta := g/l.block
  let limit := probabilityObject l cta stage 0
  let count (quarter : Fin 4) := probabilityOrdinal l X cta stage 0
    (g,start+repeatedScoreStride mode*quarter.val)
  have hAdj (i : Fin 4) (hLast : i.val+1 < 4) :
      count ⟨i.val+1,hLast⟩ = count i := by
    have hAdd := countP_take_succ_false (p := arrivesOn limit) (hLoad i) rfl
    have hPos : start+repeatedScoreStride mode*(i.val+1) =
        start+repeatedScoreStride mode*i.val+repeatedScoreStride mode := by rw [Nat.mul_succ]; omega
    unfold count probabilityOrdinal arrivals
    dsimp only
    rw [hPos]
    cases mode
    · exact hAdd
    · have hKeep := countP_take_succ_false (p := arrivesOn limit) (hWait rfl i) rfl
      rw [show repeatedScoreStride .unbiased = 2 from rfl]
      exact hKeep.trans hAdd
  have hBase (i : Fin 4) : count i = count 0 := by
    have h01 := hAdj 0 (by decide)
    have h12 := hAdj 1 (by decide)
    have h23 := hAdj 2 (by decide)
    fin_cases i
    · rfl
    · exact h01
    · exact h12.trans h01
    · exact h23.trans (h12.trans h01)
  have hEq : count a = count b := (hBase a).trans (hBase b).symm
  have hOrd := (seen a).generation.trans (hEq.trans (seen b).generation.symm)
  exact (scoreCommitOrdinalInjective hp hX (seen a).score (seen b).score hOrd).1

/-- Every word in a repeated score tile reads the final fragment of the same
observed QK bank across all four quarter loads. -/
theorem observedRepeatedScoreTile (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X) (mode : Repeated) (stage : Fin 2) {g start : Nat}
    (hStage : Prologue.warpIndex l g/4 = stage.val) (values : Fin 4 → List Value)
    (hLoad : ∀ quarter : Fin 4,
      X.get (g,start+repeatedScoreStride mode*quarter.val) =
        some ⟨scorePc mode.round quarter,.tc
          (.ld (scoreAddress l g stage quarter) (values quarter) .s32x32b)⟩)
    (hWait : mode = .unbiased → ∀ quarter : Fin 4,
      X.get (g,start+repeatedScoreStride mode*quarter.val+1) =
        some ⟨scorePc mode.round quarter,.tc .waitLd⟩) :
    ∃ banks : ∀ (q : Fin 4) (w : Fin 32),
      ScoreQkBank l X (g,start+repeatedScoreStride mode*q.val)
        (tcDataCell l g .s32x32b (scoreAddress l g stage q) w.val) stage,
      ∀ q w, (banks q w).seen.commit = (banks 0 0).seen.commit := by
  have hBanks (q : Fin 4) (w : Fin 32) :
      Nonempty (ScoreQkBank l X (g,start+repeatedScoreStride mode*q.val)
        (tcDataCell l g .s32x32b (scoreAddress l g stage q) w.val) stage) := by
    obtain ⟨_,_,_,hLen,_⟩ := scoreLoadAddress hp hX mode.round q (hLoad q)
    have hLt : w.val < (values q).length := by rw [hLen]; exact w.isLt
    obtain ⟨other,hCell⟩ := ScoreLoadCell.ofDecoded hp hX mode.round q (hLoad q) hLt rfl
    have hSame : other = stage := by
      obtain ⟨_,_,hOther,_,_⟩ := hCell.acquire hp hX
      exact Fin.ext (hOther.symm.trans hStage)
    subst other
    exact observedScoreQkBank hp hX hCuQ hCell
  let banks := fun q w => Classical.choice (hBanks q w)
  refine ⟨banks,?_⟩
  intro q w
  have hQuarter := repeatedScoreCommitsAgree hp hX mode stage values hLoad hWait
    (fun j => (banks j 0).seen) q 0
  have hOrds := (banks q w).seen.generation.trans (banks q 0).seen.generation.symm
  exact ((scoreCommitOrdinalInjective hp hX (banks q w).seen.score
    (banks q 0).seen.score hOrds).1).trans hQuarter

end PTX.Kernels.TmlFa4Fwd.Softmax
