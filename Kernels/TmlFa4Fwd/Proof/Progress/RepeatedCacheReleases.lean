-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.LoaderAllTripsExit
public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderRoundReusePhase
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyTailLedger
public import Kernels.TmlFa4Fwd.Proof.Progress.MmaIterationWalk
import Kernels.TmlFa4Fwd.Proof.Progress.OpeningKeyReturn
import all Kernels.TmlFa4Fwd.Proof.Progress.SingleVisitLoaderRetire
import Kernels.TmlFa4Fwd.Proof.Protocol.QueryEmptyFaults
import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Kernels.TmlFa4Fwd.Proof.Protocol.CorrectionProbabilityReuse

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX Prologue Epilogue
open Protocol.Loader (UnitRelease cacheEmptyUnits releasedOfRetiredUse unitReleaseUnitsLower)
open Thread.Loader (secondQueryEmpty queryEmptyObject)
open PTX.Kernels.TmlFa4Fwd.Loader (kvUseStage)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
include hp hMax hFrame

/-- The opening K release puts one completed phase on cache slot zero of the CTA. -/
theorem openingKeyUnitsOfMaximal {g mma batch : Nat} (hm : mma < l.threads)
    (hw : warpIndex l mma = 12) (hCta : mma/l.block = g/l.block) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) :
    1 ≤ cacheEmptyUnits l X g 0 := by
  obtain ⟨_,_,_,_,_,_,r,hr,_,hA,hF⟩ :=
    openingKeyReleasedOfMaximal hp hMax hFrame hm hw hb (hCta ▸ hLo) (hCta ▸ hHi)
  have hObj : Thread.Mma.Observation.emptyObject l mma 0 =
      Thread.Mma.Observation.emptyObject l g 0 := by
    simp only [Thread.Mma.Observation.emptyObject,hCta]
  rw [hObj] at hr
  exact unitReleaseUnitsLower ⟨r,hr,hA,hF⟩

/-- The opening K release and the retirements of the steady MMA iterations before `n`
release every cache use whose previous use of the same slot is at most `2*n`. -/
theorem cacheUsesReleasedOfAges {g mma batch n : Nat} (hg : g < l.threads) (hm : mma < l.threads)
    (hw : warpIndex l mma = 12) (hCta : mma/l.block = g/l.block) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hAges : ∀ j < n, Mma.SteadyRetirementAges l X mma j) :
    CacheUsesReleased l X g (2*n+4) := by
  intro use hTwo hUse
  by_cases hSmall : use < 4
  · by_cases hThree : use = 3
    · subst use
      exact openingKeyUnitsOfMaximal hp hMax hFrame hm hw hCta hb hLo hHi
    · have : use/3 = 0 := by omega
      omega
  · rcases Nat.even_or_odd (use-3) with ⟨j,hj⟩ | ⟨j,hj⟩
    · have hj' : use-3 = 2*(j-1)+2 := by omega
      have hRetired := (hAges (j-1) (by omega)).keyReturnsUse hp hMax.1 hw
      rw [← hj'] at hRetired
      exact releasedOfRetiredUse hp hMax hFrame hg (by omega) hCta hRetired
    · have hRetired := (hAges j (by omega)).valueReturnsUse hp hMax.1 hw
      rw [show 2*j+1 = use-3 by omega] at hRetired
      exact releasedOfRetiredUse hp hMax hFrame hg (by omega) hCta hRetired

/-- Uses two and three are released by the opening K return alone. -/
theorem openingCacheUsesReleased {g mma batch : Nat} (hg : g < l.threads) (hm : mma < l.threads)
    (hw : warpIndex l mma = 12) (hCta : mma/l.block = g/l.block) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) :
    CacheUsesReleased l X g 4 :=
  cacheUsesReleasedOfAges (n := 0) hp hMax hFrame hg hm hw hCta hb hLo hHi (fun _ h => by omega)

/-- The retirements of the steady iterations through `k` release every use below `2*k+6`. -/
theorem steadyCacheUsesReleased {g mma batch k : Nat} (hg : g < l.threads) (hm : mma < l.threads)
    (hw : warpIndex l mma = 12) (hCta : mma/l.block = g/l.block) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hAges : ∀ j ≤ k, Mma.SteadyRetirementAges l X mma j) :
    CacheUsesReleased l X g (2*k+6) :=
  cacheUsesReleasedOfAges (n := k+1) hp hMax hFrame hg hm hw hCta hb hLo hHi
    (fun j hj => hAges j (by omega))

/-- The final cache and query releases needed by the loader exit of a multi-visit CTA. The
cohorts of the recurring visits, the delivered final V cohort and the four final probability
cohorts take the MMA warp through its terminal visit. Its steady retirements, its terminal V
release and its final query return release every cache use below `2*trips+3` and the second
query buffer. -/
theorem loaderFinalReleasesOfTailCohorts {g batch : Nat} (hg : g < l.threads) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTrips : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (hCohorts : ∀ visit < Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1,
      Mma.SteadyVisitCohorts l X (g/l.block*l.block+384) visit)
    (hValue : Protocol.LoaderReady.DeliveredCohort l X (g/l.block*l.block+384)
      (Mma.readyStage (2*(Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1)+1))
      ((2*(Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1)+1)/3))
    (hProb : ∀ stage packet : Fin 2, Protocol.Scores.ProbabilityCohort l X (g/l.block)
      stage packet (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1)) :
    CacheUsesReleased l X g (2*Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1+3) ∧
      UnitRelease X (secondQueryEmpty l (g/l.block)) := by
  let T := Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1
  let mma := g/l.block*l.block+384
  have hLane : 384 < l.block := by rw [hp.block]; decide
  have hm : mma < l.threads := NamedBar.cta_thread_lt (NamedBar.cta_lt hg) hLane
  obtain ⟨hCta,hLocal⟩ := NamedBar.lane_cta (c := g/l.block)
    (NamedBar.block_pos_of_thread_lt hg) hLane
  change mma/l.block = g/l.block at hCta
  have hw : warpIndex l mma = 12 := by unfold warpIndex mma; rw [hLocal]
  have hLow := hCta.symm ▸ hLo
  have hHigh := hCta.symm ▸ hHi
  have hOpen := openingKeyReturnedWithTripsOfMaximal hp hMax hFrame hm hw hb hLow hHigh
  rw [hCta] at hOpen
  obtain ⟨_,_,_,⟨cur⟩⟩ := hOpen
  obtain ⟨_,upper,_⟩ := Mma.trips_bounds hp hb (assignedCoordinates_valid hp hLo hHi).1
  obtain ⟨_,_,limit⟩ := hp.lengths batch hb
  have hProtected := hFrame.metadataProtected hp
  have hGuard : Protocol.Scores.CorrectionJointGuards l X :=
    Protocol.Scores.correctionJointGuardsOfCuQ hp hMax.1 hProtected.1
  have hProbM : ∀ stage packet : Fin 2,
      Protocol.Scores.ProbabilityCohort l X (mma/l.block) stage packet (T-1) := by
    rw [hCta]
    exact hProb
  obtain ⟨_,_,_,hRetired,hQuery⟩ := Mma.steadyTerminalAndRelinquishOfTailCohorts hp hMax
    hProtected.1 hGuard hm hw hTrips (by omega) cur hCohorts hValue hProbM
  have hHighT : T-2+2 ≤ Mma.trips p batch (assignedCoordinates p batch (mma/l.block)).1 := by
    rw [hCta]
    omega
  have hSteps := mmaIterationsThroughOfCohorts hp hMax hFrame hm hw hb hLow hHigh hHighT
    (fun j hj => hCohorts j (by omega))
  have hAges : ∀ j < T-1, Mma.SteadyRetirementAges l X mma j :=
    fun j hj => (hSteps j (by omega)).2
  refine ⟨?_,?_⟩
  · intro use hTwo hUse
    by_cases hLast : use < 2*(T-1)+4
    · exact cacheUsesReleasedOfAges hp hMax hFrame hg hm hw hCta hb hLo hHi hAges use hTwo hLast
    · have hRet : Mma.RetiredCacheUse l X mma (use-3) .tailValue := by
        rw [show use-3 = 2*(T-1)+1 by omega]
        exact hRetired
      exact releasedOfRetiredUse hp hMax hFrame hg (by omega) hCta hRet
  · obtain ⟨qi,qj,hQ,hQueryCommit⟩ := hQuery 1
    have hQueryCta := hQ.1.2.2.symm.trans hCta
    have hQueryTarget : TcCommit.target (Mma.commitSpec l qi
        (l.sharedBase+16+8*(1 : Fin 2).val)) 0 = some (secondQueryEmpty l (g/l.block)) := by
      simp [Mma.commitSpec,TcCommit.target,secondQueryEmpty,queryEmptyObject,hQueryCta,
        Nat.add_assoc]
    exact unitReleaseOfCommit hp hMax hFrame hQueryCommit hQueryTarget
      (fun _ => Protocol.Query.queryEmptyHistoryClean hp hMax.1 1)

end PTX.Kernels.TmlFa4Fwd.Progress
