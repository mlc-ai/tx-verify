-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.RepeatedVisitLevel
public import Kernels.TmlFa4Fwd.Proof.Progress.RecurringCacheDelivery
import Kernels.TmlFa4Fwd.Proof.OutputProtection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Flow Prologue Epilogue Thread Softmax
open Protocol.Bias (BiasEmptyReleased)

/-- The MMA lane of a CTA's warp 12 used to index its steady visits. -/
theorem mmaLaneFacts {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) {cta : Nat}
    (hc : cta < l.grid) :
    cta*l.block+384 < l.threads ∧ warpIndex l (cta*l.block+384) = 12 ∧
      (cta*l.block+384)/l.block = cta := by
  have hLane : 384 < l.block := by rw [hp.block]; decide
  have hb : 0 < l.block := by rw [hp.block]; decide
  obtain ⟨hCta,hLocal⟩ := NamedBar.lane_cta (c := cta) hb hLane
  exact ⟨NamedBar.cta_thread_lt hc hLane,by unfold warpIndex; rw [hLocal],hCta⟩

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
    (frame : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y) {cta batch : Nat}
    (hc : cta < l.grid) (hb : batch < p.batch) (lo : tilePrefix p batch*p.heads ≤ cta)
    (hi : cta < tilePrefix p (batch+1)*p.heads)
include hp hMax frame hc hb lo hi

/-- The steady MMA retirements of the visits before `visit-1` release every cache use the
loader rounds before `visit` wait for. -/
theorem levelCacheReleases {visit : Nat} (hVisit : 1 ≤ visit) (hT : visit+1 ≤ tileTrips p batch cta)
    (cohorts : ∀ j, j+1 < visit → Mma.SteadyVisitCohorts l X (cta*l.block+384) j) {g : Nat}
    (hg : g < l.threads) (hCta : g/l.block = cta) :
    CacheUsesReleased l X g (2*visit+2) := by
  obtain ⟨hm,hw,hmc⟩ := mmaLaneFacts hp hc
  have hmc' : (cta*l.block+384)/l.block = g/l.block := hmc.trans hCta.symm
  by_cases hOne : visit = 1
  · subst hOne
    exact openingCacheUsesReleased hp hMax (frame X hMax.1) hg hm hw hmc' hb
      (by rw [hCta]; exact lo)
      (by rw [hCta]; exact hi)
  · have hAges := mmaIterationsThroughOfCohorts hp hMax (frame X hMax.1) hm hw hb
      (by rw [hmc]; exact lo) (by rw [hmc]; exact hi) (k := visit-2)
      (by rw [hmc]; unfold tileTrips at hT; omega)
      (fun j hj => cohorts j (by omega))
    have h := steadyCacheUsesReleased hp hMax (frame X hMax.1) hg hm hw hmc' hb
      (by rw [hCta]; exact lo)
      (by rw [hCta]; exact hi) (k := visit-2) (fun j hj => (hAges j hj).2)
    rwa [show 2*(visit-2)+6 = 2*visit+2 by omega] at h

/-- Each loader lane runs its rounds before `visit`: it publishes every ring use below
`2*visit+2`, and warp 14 issues the Bias generations of those rounds. -/
theorem loaderLevel (multiple : 2 ≤ tileTrips p batch cta) {visit : Nat} (hVisit : 1 ≤ visit)
    (hT : visit+1 ≤ tileTrips p batch cta)
    (cohorts : ∀ j, j+1 < visit → Mma.SteadyVisitCohorts l X (cta*l.block+384) j)
    (released : ∀ stage : Fin 2,
      BiasEmptyReleased l X cta stage (min visit (stageBiased p batch cta stage))) {g : Nat}
    (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hCta : g/l.block = cta) :
    (∀ use < 2*visit+2, use-1 ≤ (X.tr g).countP Loader.recurringPublicationMark) ∧
    (warpIndex l g = 14 → ∀ stage, ∀ round < Loader.warmRounds p l g batch, round+1 ≤ visit →
      BiasGenerationDelivered l X cta stage (round+1)) ∧
    (warpIndex l g = 14 → Loader.warmTailSkips p l g batch = false →
      Loader.warmRounds p l g batch < visit →
      BiasGenerationDelivered l X cta 0 (Loader.warmRounds p l g batch+1)) := by
  subst hCta
  unfold tileTrips at hT multiple
  have hPos : 0 < Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 := by omega
  have hRel := levelCacheReleases hp hMax frame hc hb lo hi hVisit hT cohorts hg rfl
  obtain ⟨hPub,hBD,hTailBD⟩ := loaderRoundsThrough hp hMax (frame X hMax.1) hg hw hb lo hi
    multiple (visit-1) (by omega)
    (by unfold Loader.cacheUseOfRound; rw [show 2+2*(visit-1)+2 = 2*visit+2 by omega]
        exact hRel)
    (fun h14 round hr hle stage => by
      obtain ⟨hW,_⟩ := biasScheduleMatch p l h14 hPos stage
      exact biasEmptyReleased_mono (released stage) (by omega))
    (fun h14 hSkip hle => by
      obtain ⟨hW,_,_,_,_,hTail⟩ := biasScheduleMatch p l h14 hPos 0
      exact biasEmptyReleased_mono (released 0) (by have := hTail rfl hSkip; omega))
  have hSelf : warpLane l g (laneOf l g) = g := Step.warpLane_of_sameWarp ⟨⟨hg,hg,rfl⟩,rfl⟩
  refine ⟨fun use hu => ?_,fun h14 stage round hr hle => hBD h14 stage round hr (by omega),
    fun h14 hSkip hle => hTailBD h14 hSkip (by omega)⟩
  have h := hPub (laneOf l g) (Nat.mod_lt _ (by decide)) use
    (by unfold Loader.cacheUseOfRound; omega)
  rwa [hSelf] at h

omit hp hMax frame hc hb lo hi in
/-- The logical producer lanes of a CTA are its loader lanes. -/
theorem producerLaneFacts {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) {cta : Nat}
    (hc : cta < l.grid) (lane : Fin 64) :
    Loader.producer l cta lane < l.threads ∧ 14 ≤ warpIndex l (Loader.producer l cta lane) ∧
      Loader.producer l cta lane/l.block = cta := by
  have hl : 448+lane.val < l.block := by rw [hp.block]; have := lane.isLt; omega
  have hb : 0 < l.block := by rw [hp.block]; decide
  obtain ⟨hCta,hLocal⟩ := NamedBar.lane_cta (c := cta) hb hl
  have e : Loader.producer l cta lane = cta*l.block+(448+lane.val) := by
    simp only [Loader.producer,TmlFa4Fwd.Loader.readyProducer,Nat.add_assoc]
  rw [e]
  exact ⟨NamedBar.cta_thread_lt hc hl,by unfold warpIndex; rw [hLocal]; omega,hCta⟩

omit hp hMax frame hc hb lo hi in
/-- A ring use published by every loader lane is delivered to the MMA as one cohort. -/
theorem deliveredOfLoaderCounts {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (frame : OutputFootprint p X) {cta mma use : Nat} (hc : cta < l.grid)
    (hm : mma/l.block = cta) (hUse : 2 ≤ use)
    (counts : ∀ g < l.threads, 14 ≤ warpIndex l g → g/l.block = cta →
      use-1 ≤ (X.tr g).countP Loader.recurringPublicationMark) :
    Protocol.LoaderReady.DeliveredCohort l X mma (Mma.readyStage use) (use/3) := by
  apply Protocol.LoaderReady.IssuedCohort.deliveredOfMaximal hp hMax frame
  apply Protocol.LoaderReady.issuedCohortOfRecurringCounts hp hMax.1 hUse
  intro lane
  rw [hm]
  obtain ⟨h1,h2,h3⟩ := producerLaneFacts hp hc lane
  exact counts _ h1 h2 h3

/-- At visit `visit` the MMA has the cohorts of every visit before it and has run all those
steady iterations; the loader has delivered the Bias generation of a biased visit. -/
theorem mmaLevel (multiple : 2 ≤ tileTrips p batch cta) {visit : Nat} (hVisit : 1 ≤ visit)
    (hT : visit+1 ≤ tileTrips p batch cta)
    (cohorts : ∀ j, j+1 < visit → Mma.SteadyVisitCohorts l X (cta*l.block+384) j)
    (probability : ∀ stage packet : Fin 2,
      Protocol.Scores.ProbabilityCohort l X cta stage packet (visit-1))
    (released : ∀ stage : Fin 2,
      BiasEmptyReleased l X cta stage (min visit (stageBiased p batch cta stage))) :
    (∀ j, j < visit → Mma.SteadyVisitCohorts l X (cta*l.block+384) j) ∧
    (∀ j, j < visit → Mma.SteadyIterationIssues l X (cta*l.block+384) j ∧
      Mma.SteadyRetirementAges l X (cta*l.block+384) j) ∧
    (∀ g < l.threads, 14 ≤ warpIndex l g → g/l.block = cta → ∀ use < 2*visit+2,
      use-1 ≤ (X.tr g).countP Loader.recurringPublicationMark) ∧
    (∀ stage : Fin 2, visit < stageBiased p batch cta stage →
      BiasGenerationDelivered l X cta stage visit) := by
  obtain ⟨hm,hw,hmc⟩ := mmaLaneFacts hp hc
  have loader := fun g hg hw hCta =>
    loaderLevel hp hMax frame hc hb lo hi multiple hVisit hT cohorts released (g := g) hg hw hCta
  have counts (g : Nat) (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hCta : g/l.block = cta) :
      ∀ use < 2*visit+2, use-1 ≤ (X.tr g).countP Loader.recurringPublicationMark :=
    (loader g hg hw hCta).1
  have hLast : Mma.SteadyVisitCohorts l X (cta*l.block+384) (visit-1) := by
    by_cases hOne : visit = 1
    · subst hOne
      exact firstSteadyVisitCohorts hp hMax (frame X hMax.1) hm hb (by rw [hmc]; exact lo)
        (by rw [hmc]; exact hi) (by rw [hmc]; exact multiple)
    · refine ⟨?_,?_,?_⟩
      · exact deliveredOfLoaderCounts hp hMax (frame X hMax.1) hc hmc (by omega)
          (fun g hg hw hCta => counts g hg hw hCta _ (by omega))
      · exact deliveredOfLoaderCounts hp hMax (frame X hMax.1) hc hmc (by omega)
          (fun g hg hw hCta => counts g hg hw hCta _ (by omega))
      · intro stage packet
        rw [hmc]
        exact probability stage packet
  have hAll (j : Nat) (hj : j < visit) : Mma.SteadyVisitCohorts l X (cta*l.block+384) j := by
    by_cases h : j+1 < visit
    · exact cohorts j h
    · rw [show j = visit-1 by omega]; exact hLast
  have hIter := mmaIterationsThroughOfCohorts hp hMax (frame X hMax.1) hm hw hb
    (by rw [hmc]; exact lo) (by rw [hmc]; exact hi) (k := visit-1)
    (by rw [hmc]; unfold tileTrips at hT; omega) (fun j hj => hAll j (by omega))
  refine ⟨hAll,fun j hj => hIter j (by omega),counts,fun stage hB => ?_⟩
  let g14 := cta*l.block+(448+0)
  have h14 : 448+0 < l.block := by rw [hp.block]; decide
  have hb0 : 0 < l.block := by rw [hp.block]; decide
  obtain ⟨hCta14,hLocal14⟩ := NamedBar.lane_cta (c := cta) hb0 h14
  have hg14 : g14 < l.threads := NamedBar.cta_thread_lt hc h14
  have hw14 : warpIndex l g14 = 14 := by unfold warpIndex; rw [hLocal14]
  obtain ⟨_,hBD,hTailBD⟩ := loader g14 hg14 (by omega) hCta14
  have hPos : 0 < Mma.trips p batch (assignedCoordinates p batch (g14/l.block)).1 := by
    rw [hCta14]; unfold tileTrips at multiple; omega
  obtain ⟨hWB,_,_,_,hBeyond,_⟩ := biasScheduleMatch p l hw14 hPos stage
  rw [hCta14] at hWB hBeyond
  by_cases hWarm : visit-1 < Loader.warmRounds p l g14 batch
  · have h := hBD hw14 stage (visit-1) hWarm (by omega)
    rwa [Nat.sub_add_cancel hVisit] at h
  · obtain ⟨hStage,hEq,hSkip⟩ := hBeyond visit hB (by omega)
    subst hStage
    have h := hTailBD hw14 hSkip (by omega)
    rwa [← hEq] at h

end PTX.Kernels.TmlFa4Fwd.Progress
