-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.RepeatedVisitMachines
public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningStatistics
import Kernels.TmlFa4Fwd.Proof.OutputProtection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Flow Prologue Epilogue Thread Softmax
open Protocol.Bias (BiasEmptyReleased)

/-- The loop shape of a stage: at most `2^31` trips, a split no larger than the trips, and at
least two biased visits counting the opening one. -/
theorem stageShape {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) {cta batch : Nat}
    (hb : batch < p.batch) (lo : tilePrefix p batch*p.heads ≤ cta)
    (hi : cta < tilePrefix p (batch+1)*p.heads) (multiple : 2 ≤ tileTrips p batch cta)
    (stage : Fin 2) :
    tileTrips p batch cta < 2^31 ∧ stageSplit p batch cta stage ≤ tileTrips p batch cta ∧
      stageBiased p batch cta stage = tileTrips p batch cta-stageSplit p batch cta stage ∧
      2 ≤ stageBiased p batch cta stage := by
  obtain ⟨_,upper,_⟩ := Mma.trips_bounds hp hb (assignedCoordinates_valid hp lo hi).1
  obtain ⟨_,_,limit⟩ := hp.lengths batch hb
  unfold tileTrips at multiple ⊢
  refine ⟨by omega,?_,rfl,?_⟩
  · unfold stageSplit firstPlainSplit; dsimp only; omega
  · unfold stageBiased firstPlainSplit; dsimp only; omega

/-- One visit of a whole stage, biased or plain by the stage's loop shape. -/
theorem stageStep {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (frame : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {cta batch : Nat} (hc : cta < l.grid) (hb : batch < p.batch)
    (lo : tilePrefix p batch*p.heads ≤ cta) (hi : cta < tilePrefix p (batch+1)*p.heads)
    (multiple : 2 ≤ tileTrips p batch cta) (stage : Fin 2) {visit : Nat}
    (hVisit : 1 ≤ visit) (hLt : visit < tileTrips p batch cta)
    (heads : StageHeads p l X batch cta stage visit)
    (score : ∃ issue spec, Scores.ScoreCommit l X issue cta stage spec 0 ∧
      Scores.scoreCommitOrdinal l X cta stage issue = visit ∧ (0 : Fin 16) ∈ X.tcNotified issue)
    (bias : visit < stageBiased p batch cta stage → BiasGenerationDelivered l X cta stage visit) :
    StageVisitOutputs l X cta stage (stageBiased p batch cta stage) visit ∧
      (Protocol.Statistics.TerminalCorrectionCredits l X cta stage visit →
        ∃ barsW electsW : Nat → Nat, ∀ g, BiasedStageMember l cta stage g → ∃ pos,
          LoopNextAt p l X (tileTrips p batch cta) (stageSplit p batch cta stage) g (warpOf l g)
            visit (barsW (warpIndex l g)) (electsW (warpIndex l g)) pos ∧
          HeadArrivals l X cta stage (stageBiased p batch cta stage) g (visit+1) pos) := by
  obtain ⟨hTrips,hSplit,hBiased,_⟩ := stageShape hp hb lo hi multiple stage
  obtain ⟨barsW,electsW,H⟩ := heads
  rw [hBiased] at bias ⊢
  by_cases hB : visit < tileTrips p batch cta-stageSplit p batch cta stage
  · obtain ⟨out,next⟩ := biasedStageStep hp hMax frame hc stage hTrips hVisit hB barsW electsW
      H score (bias hB)
    exact ⟨out,fun c => ⟨barsW,electsW,next c⟩⟩
  · obtain ⟨out,next⟩ := plainStageStep hp hMax frame stage hTrips hSplit (by omega) hLt barsW
      electsW H score
    exact ⟨out,fun c => ⟨barsW,electsW,next c⟩⟩

/-- Heads of the next visit from the lanes' continuations. -/
theorem StageHeads.ofNext {p : Params} {l : Launch} {X : Execution} {cta batch : Nat}
    {stage : Fin 2} {visit : Nat} (hMore : visit+1 < tileTrips p batch cta)
    (h : ∃ barsW electsW : Nat → Nat, ∀ g, BiasedStageMember l cta stage g → ∃ pos,
      LoopNextAt p l X (tileTrips p batch cta) (stageSplit p batch cta stage) g (warpOf l g)
        visit (barsW (warpIndex l g)) (electsW (warpIndex l g)) pos ∧
      HeadArrivals l X cta stage (stageBiased p batch cta stage) g (visit+1) pos) :
    StageHeads p l X batch cta stage (visit+1) := by
  obtain ⟨barsW,electsW,H⟩ := h
  refine ⟨fun w => barsW w+1,fun w => electsW w+1,fun g hm => ?_⟩
  obtain ⟨pos,hNext,hA⟩ := H g hm
  exact ⟨pos,hNext.1 hMore,hA⟩

/-- The terminal statistics entry of every lane from the lanes' continuations. -/
theorem StageHeads.terminalOfNext {p : Params} {l : Launch} {X : Execution} {cta batch : Nat}
    {stage : Fin 2} {visit : Nat} (hLast : visit+1 = tileTrips p batch cta)
    (h : ∃ barsW electsW : Nat → Nat, ∀ g, BiasedStageMember l cta stage g → ∃ pos,
      LoopNextAt p l X (tileTrips p batch cta) (stageSplit p batch cta stage) g (warpOf l g)
        visit (barsW (warpIndex l g)) (electsW (warpIndex l g)) pos ∧
      HeadArrivals l X cta stage (stageBiased p batch cta stage) g (visit+1) pos) :
    ∀ g, BiasedStageMember l cta stage g → ∃ maximum sum,
      Nonempty (SoftmaxTerminalAt p l X g (warpOf l g) (tileTrips p batch cta) maximum sum) := by
  obtain ⟨barsW,electsW,H⟩ := h
  intro g hm
  obtain ⟨pos,hNext,_⟩ := H g hm
  exact hNext.2 hLast

/-- What the last visit leaves for the terminal assembly: every softmax lane at its terminal
statistics, the MMA cohorts of all steady visits and of the last visit, every ring use
published, and the Bias-empty releases of all biased visits. -/
structure FinalState (p : Params) (l : Launch) (X : Execution) (batch cta : Nat) : Prop where
  terminal : ∀ stage : Fin 2, ∀ g, BiasedStageMember l cta stage g → ∃ maximum sum,
    Nonempty (SoftmaxTerminalAt p l X g (warpOf l g) (tileTrips p batch cta) maximum sum)
  cohorts : ∀ j, j < tileTrips p batch cta-1 →
    Mma.SteadyVisitCohorts l X (cta*l.block+384) j
  probability : ∀ stage packet : Fin 2,
    Protocol.Scores.ProbabilityCohort l X cta stage packet (tileTrips p batch cta-1)
  loader : ∀ g < l.threads, 14 ≤ warpIndex l g → g/l.block = cta →
    ∀ use < 2*tileTrips p batch cta, use-1 ≤ (X.tr g).countP Loader.recurringPublicationMark
  biasReleased : ∀ stage : Fin 2,
    BiasEmptyReleased l X cta stage (min (tileTrips p batch cta) (stageBiased p batch cta stage))

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
    (frame : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y) {cta batch : Nat}
    (hc : cta < l.grid) (hb : batch < p.batch) (lo : tilePrefix p batch*p.heads ≤ cta)
    (hi : cta < tilePrefix p (batch+1)*p.heads) (multiple : 2 ≤ tileTrips p batch cta)
include hp hMax frame hc hb lo hi multiple

/-- One level of the induction: the visit `visit` of both stages, the MMA iterations and
loader rounds it needs, and the correction credits that release it. -/
theorem levelStep {visit : Nat} (hVisit : 1 ≤ visit) (hLt : visit < tileTrips p batch cta)
    (S : LevelState p l X batch cta visit) :
    (visit+1 < tileTrips p batch cta → LevelState p l X batch cta (visit+1)) ∧
      (visit+1 = tileTrips p batch cta → FinalState p l X batch cta) := by
  obtain ⟨hm,hw,hmc⟩ := mmaLaneFacts hp hc
  obtain ⟨hAll,hIter,counts,hBD⟩ := mmaLevel hp hMax frame hc hb lo hi multiple hVisit hLt
    S.cohorts S.probability S.biasReleased
  have score (stage : Fin 2) : ∃ issue spec, Scores.ScoreCommit l X issue cta stage spec 0 ∧
      Scores.scoreCommitOrdinal l X cta stage issue = visit ∧
      (0 : Fin 16) ∈ X.tcNotified issue := by
    have h := scoreDeliveredOfAges hp hMax (frame X hMax.1) (hIter (visit-1) (by omega)).2 stage
    rw [hmc,Nat.sub_add_cancel hVisit] at h
    exact h
  obtain ⟨out0,next0⟩ := stageStep hp hMax frame hc hb lo hi multiple 0 hVisit hLt S.zero
    (score 0) (hBD 0)
  have P0 := out0.publishedThrough
  have heads1 := S.one P0
  obtain ⟨out1,next1⟩ := stageStep hp hMax frame hc hb lo hi multiple 1 hVisit hLt heads1
    (score 1) (hBD 1)
  have P1 := out1.publishedThrough
  have probability (stage packet : Fin 2) :
      Protocol.Scores.ProbabilityCohort l X cta stage packet visit := by
    fin_cases packet
    · fin_cases stage
      · exact mainCohortOfOutputs hp hMax frame hc hb lo hi hVisit hLt P0 S.publishedOne out0
      · exact mainCohortOfOutputs hp hMax frame hc hb lo hi hVisit hLt P0
          (by show SoftmaxStagePublishedThrough l X cta 1 (visit-1+1)
              rw [Nat.sub_add_cancel hVisit]; exact P1) out1
    · fin_cases stage
      · exact tailCohortOfOutputs hp hMax.1 hc S.zero out0
      · exact tailCohortOfOutputs hp hMax.1 hc heads1 out1
  have released (stage : Fin 2) : BiasEmptyReleased l X cta stage
      (min (visit+1) (stageBiased p batch cta stage)) := by
    have hOut : StageVisitOutputs l X cta stage (stageBiased p batch cta stage) visit := by
      fin_cases stage
      · exact out0
      · exact out1
    by_cases hB : visit < stageBiased p batch cta stage
    · rw [Nat.min_eq_left (by omega)]
      exact biasReleasedOfOutputs hp hMax.1 hc hB hOut
    · rw [show min (visit+1) (stageBiased p batch cta stage) =
          min visit (stageBiased p batch cta stage) by omega]
      exact S.biasReleased stage
  have hActive0 : visit-1+1 < Mma.trips p batch (assignedCoordinates p batch cta).1 := by
    unfold tileTrips at hLt; omega
  have C0 : Protocol.Statistics.TerminalCorrectionCredits l X cta 0 visit := by
    have h := statisticsCreditsOfRescalePublications hp hMax frame hc hb lo hi (visit-1)
      hActive0 1 (by rw [Nat.sub_add_cancel hVisit]; exact P0)
      (by rw [show visit-1+(1 : Fin 2).val = visit by simp; omega]; exact P1)
    rwa [show visit-1+(1 : Fin 2).val = visit by simp; omega] at h
  refine ⟨fun hMore => ?_,fun hLast => ?_⟩
  · refine ⟨StageHeads.ofNext hMore (next0 C0),fun P0' => ?_,?_,fun j hj => hAll j (by omega),
      ?_,released⟩
    · have C1 := statisticsCreditsOfRescalePublications hp hMax frame hc hb lo hi visit
        (by unfold tileTrips at hMore; omega) 0 P0' (by simpa using P1)
      exact StageHeads.ofNext hMore (next1 (by simpa using C1))
    · simpa using P1
    · simpa using probability
  · have C1 := lastStageOneCreditOfPublications hp hMax frame hc hb lo hi multiple
      (by rw [← show visit = tileTrips p batch cta-1 by omega]; exact P0)
      (by rw [← show visit = tileTrips p batch cta-1 by omega]; exact P1)
    have hv : visit = tileTrips p batch cta-1 := by omega
    refine ⟨fun stage => ?_,fun j hj => hAll j (by omega),by rw [← hv]; exact probability,
      fun g hg hw hCta use hu => counts g hg hw hCta use (by omega),by rw [← hLast]; exact released⟩
    fin_cases stage
    · exact StageHeads.terminalOfNext hLast (next0 C0)
    · exact StageHeads.terminalOfNext hLast (next1 (by rw [hv]; exact C1))

/-- The visit-one heads of a stage in the form of the induction. -/
theorem visitOneStageHeads (stage : Fin 2)
    (published : stage = 1 → SoftmaxStagePublishedThrough l X cta 0 1) :
    StageHeads p l X batch cta stage 1 := by
  obtain ⟨_,_,hBiased,hTwo⟩ := stageShape hp hb lo hi multiple stage
  obtain ⟨barsW,electsW,H⟩ := visitOneBiasedHeads hp hMax frame hc hb lo hi multiple stage
    published
  refine ⟨barsW,electsW,fun g hm => ?_⟩
  obtain ⟨maximum,sum,head,_,hSplit,_,hMain,hBias,i,inst,leader,_,hE,hTail⟩ := H g hm
  refine ⟨head.cursor.pos,.inl ⟨by omega,_,_,_,maximum,sum,?_,head,rfl,hSplit⟩,hMain,
    ⟨leader,⟨i,_,inst,hE⟩,hTail⟩,fun hLane => ?_⟩
  · rfl
  · rw [Nat.min_eq_left (by omega)]
    exact hBias hLane

/-- The state before visit one. -/
theorem levelStateOne : LevelState p l X batch cta 1 := by
  refine ⟨visitOneStageHeads hp hMax frame hc hb lo hi multiple 0 (fun h => absurd h (by decide)),
    fun h => visitOneStageHeads hp hMax frame hc hb lo hi multiple 1 (fun _ => h),?_,
    fun j hj => by omega,fun stage packet => ?_,fun stage => ?_⟩
  · intro g hg hCta hw
    obtain ⟨i,pub⟩ := openingStatisticsOfMaximal hp hMax (frame X hMax.1) hg 1 hw hb
      (by rw [hCta]; exact lo) (by rw [hCta]; exact hi)
    exact ⟨i,_,pub,Nat.zero_le _⟩
  · exact openingProbabilityCohortOfMaximal hp hMax (frame X hMax.1) hc stage packet hb lo hi
  · obtain ⟨_,_,_,hTwo⟩ := stageShape hp hb lo hi multiple stage
    rw [Nat.min_eq_left (by omega)]
    exact Protocol.Bias.biasEmptyReleasedOpeningOfMaximal hp hMax (frame X hMax.1) hc hb lo hi
      stage

/-- Every visit of a scheduled multi-visit CTA completes, ending in the final state. -/
theorem finalStateOfMaximal : FinalState p l X batch cta := by
  have walk (k : Nat) : k+2 ≤ tileTrips p batch cta → LevelState p l X batch cta (k+1) := by
    induction k with
    | zero => exact fun _ => levelStateOne hp hMax frame hc hb lo hi multiple
    | succ k ih =>
      intro hk
      exact (levelStep hp hMax frame hc hb lo hi multiple (by omega) (by omega)
        (ih (by omega))).1 (by omega)
  have S := walk (tileTrips p batch cta-2) (by omega)
  rw [show tileTrips p batch cta-2+1 = tileTrips p batch cta-1 by omega] at S
  exact (levelStep hp hMax frame hc hb lo hi multiple (by omega) (by omega) S).2 (by omega)

end PTX.Kernels.TmlFa4Fwd.Progress
