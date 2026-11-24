-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyOpeningLedger
public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningTailValue
import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Kernels.TmlFa4Fwd.Proof.Protocol.CorrectionProbabilityReuse

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX Prologue Epilogue
open Mma (SteadyIterationCursor SteadyVisitLedger SteadyVisitCohorts SteadyIterationIssues
  SteadyRetirementAges)

/-- A reached steady MMA cursor issues every visit whose cohorts are already published.
Unlike `steadyIterationsOfCohorts`, the cohorts of later visits are not needed. -/
theorem steadyIterationsPrefixOfCohorts {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hGuard : Protocol.Scores.CorrectionJointGuards l X)
    {g : Nat} (hg : g < l.threads) (hWarp : warpIndex l g = 12) (k : Nat) :
    ∀ (visit remaining shuffles votes : Nat) {ends : Nat → Option TState},
      k+2 ≤ remaining → remaining < 2^32 →
      ∀ cur : SteadyIterationCursor l X g visit remaining shuffles votes ends,
      SteadyVisitLedger l X g visit cur.pos →
      (∀ j ≤ k, SteadyVisitCohorts l X g (visit+j)) →
      ∀ j ≤ k, SteadyIterationIssues l X g (visit+j) ∧
        SteadyRetirementAges l X g (visit+j) := by
  induction k with
  | zero =>
    intro visit remaining shuffles votes ends hRemaining hBound cur hLedger hCohorts j hj
    obtain rfl : j = 0 := by omega
    obtain ⟨_,_,_,hIssue,_,hAges⟩ := Mma.steadyIterationOfCohorts hp hMax hGuard hg hWarp
      (by omega) hBound cur hLedger (by simpa using hCohorts 0 le_rfl)
    exact ⟨by simpa using hIssue,by simpa using hAges⟩
  | succ k ih =>
    intro visit remaining shuffles votes ends hRemaining hBound cur hLedger hCohorts j hj
    have hStep := Mma.steadyIterationOfCohorts hp hMax hGuard hg hWarp
      (by omega) hBound cur hLedger (by simpa using hCohorts 0 (Nat.zero_le _))
    rw [ite_eq_left (by omega : 2 < remaining)] at hStep
    obtain ⟨_,next,hNext,hIssue,_,hAges⟩ := hStep
    rcases j with _ | j
    · exact ⟨by simpa using hIssue,by simpa using hAges⟩
    · have h := ih (visit+1) (remaining-1) _ votes (by omega) (by omega) next hNext
        (fun i hi => by
          have c := hCohorts (i+1) (by omega)
          rwa [show visit+(i+1) = visit+1+i by omega] at c)
        j (by omega)
      rwa [show visit+1+j = visit+(j+1) by omega] at h

/-- The scheduled MMA warp of a multi-visit tile issues each recurring visit through `k`
once the cohorts of the visits through `k` are published. -/
theorem mmaIterationsThroughOfCohorts {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (frame : OutputFootprint p X) {g batch : Nat} (hg : g < l.threads) (hw : warpIndex l g = 12)
    (hb : batch < p.batch) (lo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hi : g/l.block < tilePrefix p (batch+1)*p.heads) {k : Nat}
    (hk : k+2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (cohorts : ∀ j ≤ k, SteadyVisitCohorts l X g j) :
    ∀ j ≤ k, SteadyIterationIssues l X g j ∧ SteadyRetirementAges l X g j := by
  obtain ⟨_,_,_,⟨opening⟩⟩ := openingKeyReturnedWithTripsOfMaximal hp hMax frame hg hw hb lo hi
  obtain ⟨_,upper,_⟩ := Mma.trips_bounds hp hb (assignedCoordinates_valid hp lo hi).1
  obtain ⟨_,_,limit⟩ := hp.lengths batch hb
  obtain ⟨cur,ledger⟩ := Mma.openingSteadyIterationWithLedger hp hMax hg hw (by omega)
    (by omega) opening
  have h := steadyIterationsPrefixOfCohorts hp hMax
    (Protocol.Scores.correctionJointGuardsOfCuQ hp hMax.1 (frame.metadataProtected hp).1)
    hg hw k 0 _ _ _ hk (by omega) cur ledger (by simpa using cohorts)
  simpa using h

end PTX.Kernels.TmlFa4Fwd.Progress
