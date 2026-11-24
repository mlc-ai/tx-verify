-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RescaleReturnedCredits
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionEntryProgress
import all Kernels.TmlFa4Fwd.Proof.Thread.CorrectionProbabilityGate
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Correction
open PTX PTX.Flow PTX.Proof PTX.AsyncCopy PTX.MBarrier Prologue Epilogue Thread Thread.Scores

/-- A release adjacent to a statistics credit is strictly after both priming
probability arrivals. The paired named barrier is already past the priming sites. -/
private theorem afterInitialProbability {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g j : Nat} (hg : g < l.threads) (hw : 8 ≤ warpIndex l g ∧ warpIndex l g < 12)
    {e : Event} {s : Fin 2} (he : X.get (g,j+1) = some e)
    (ha : correctionAction e = some (.statsCredit s)) : 8 < j := by
  obtain ⟨a,n,kind⟩ := correctionStatsCreditKind ha
  have mark := (correctionStatsCreditMark_iff s e).mpr
    ((correctionStatsCreditObservation s kind).mp ha)
  obtain ⟨i,before,bar,_⟩ := correctionCreditAfterNamedWait hp hMax.1 s he mark
  have id : 3 ≤ statsBarrierId l g s ∧ statsBarrierId l g s < 11 := by
    unfold statsBarrierId
    have := s.isLt
    omega
  obtain ⟨_,_,⟨w,hGet,act⟩,_⟩ := correctionWaitOfStatisticsSync hp hMax.1 id bar
  obtain ⟨_,_,_,_,seed,_,_,_⟩ := schedulerEntryOfMaximal hp hMax hg hw.1 hw.2
  have later := traceOrderOfSegmentFloor hMax.1 (floor := initialCreditSite 1+1)
    (initialCreditFloor 1) (initialCreditSegments 1) seed hGet (by change 7754 < 7755; decide)
    ((by decide : initialCreditSite 1+1 ≤ 7980).trans (correctionStatsWaitSiteBounds act).1)
  omega

/-- Each successive paired return contributes a fresh main-P arrival on top
of the correction lane's priming credit. -/
theorem probabilityExtentOfPairedReturns {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X) {g : Nat}
    (hg : g < l.threads) (hw : 8 ≤ warpIndex l g ∧ warpIndex l g < 12)
    (stage : Fin 2) (round : Nat)
    (returns : ∀ k ≤ round, PairedRescaleCredit l X g stage (k+stage.val)) :
    round+2 ≤ (X.tr g).countP (arrivesOn (probabilityObject l (g/l.block) stage 0)) := by
  let addr := probabilityObject l (g/l.block) stage 0
  have step (i : Nat) (credit : ProbabilityCredit l X (g,i) (g/l.block) stage 0) :
      ((X.tr g).take (i+1)).countP (arrivesOn addr) =
        ((X.tr g).take i).countP (arrivesOn addr)+1 := by
    obtain ⟨pc,he⟩ := credit
    exact countP_take_succ he (by simp [addr,sourceArrive])
  have accumulated (k : Nat) (hk : k ≤ round) (i : Nat)
      (pCredit : ProbabilityCredit l X (g,i) (g/l.block) stage 0)
      (rank : (correctionBefore X (g,i+1)).count (.statsCredit stage.rev) = k+stage.val)
      (issued : ∃ e, X.get (g,i+1) = some e ∧ correctionAction e = some (.statsCredit stage.rev)) :
      k+2 ≤ ((X.tr g).take (i+1)).countP (arrivesOn addr) := by
    induction k generalizing i with
    | zero =>
      obtain ⟨e,he,ha⟩ := issued
      have lt := afterInitialProbability hp hMax hg hw he ha
      obtain ⟨_,_,_,zero,one,_,_,_⟩ := schedulerEntryOfMaximal hp hMax hg hw.1 hw.2
      have seed : ∃ j < i, ProbabilityCredit l X (g,j) (g/l.block) stage 0 := by
        fin_cases stage
        · exact ⟨7,by omega,_,zero⟩
        · exact ⟨8,lt,_,one⟩
      obtain ⟨j,hj,pj⟩ := seed
      have le := countP_take_mono (arrivesOn addr) (X.tr g) (show j+1 ≤ i by omega)
      rw [step j pj] at le
      rw [step i pCredit]
      omega
    | succ k ih =>
      obtain ⟨j,pj,e,he,ha,prev⟩ := returns k (by omega)
      have lt : j < i := by
        by_contra! reverse
        rw [correctionBefore_count] at prev rank
        dsimp only [Prod.fst,Prod.snd] at prev rank
        have le := countP_take_mono (fun e => decide (correctionAction e =
          some (.statsCredit stage.rev))) (X.tr g) (Nat.add_le_add_right reverse 1)
        omega
      have old := ih (by omega) j pj prev ⟨e,he,ha⟩
      have le := countP_take_mono (arrivesOn addr) (X.tr g) (show j+1 ≤ i by omega)
      rw [step i pCredit]
      omega
  obtain ⟨i,pc,e,he,ha,rank⟩ := returns round le_rfl
  have bound := accumulated round le_rfl i pc rank ⟨e,he,ha⟩
  have le := countP_take_mono (arrivesOn addr) (X.tr g) (len_of_get he).le
  rw [List.take_length] at le
  exact bound.trans le

end PTX.Kernels.TmlFa4Fwd.Correction
