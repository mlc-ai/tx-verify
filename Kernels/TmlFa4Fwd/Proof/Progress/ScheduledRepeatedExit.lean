-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.RepeatedVisitInduction
public import Kernels.TmlFa4Fwd.Proof.Progress.RepeatedRowRetire
public import Kernels.TmlFa4Fwd.Proof.Thread.Machine
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxSingleVisitRetire
import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxActiveGroupProgress
import Kernels.TmlFa4Fwd.Proof.Progress.OpeningTailValue
import Kernels.TmlFa4Fwd.Proof.OutputProtection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Flow Prologue Epilogue Thread Softmax
open Protocol.Bias (BiasEmptyReleased)

/-- The cohorts of a steady visit depend on the consuming lane only through its CTA. -/
theorem steadyVisitCohortsOfCta {l : Launch} {X : Execution} {g h visit : Nat}
    (e : g/l.block = h/l.block) (c : Mma.SteadyVisitCohorts l X g visit) :
    Mma.SteadyVisitCohorts l X h visit := by
  obtain ⟨v,k,pr⟩ := c
  refine ⟨?_,?_,?_⟩
  · unfold Protocol.LoaderReady.DeliveredCohort Loader.readyObject at v ⊢
    rw [← e]; exact v
  · unfold Protocol.LoaderReady.DeliveredCohort Loader.readyObject at k ⊢
    rw [← e]; exact k
  · rw [← e]; exact pr

/-- Every non-output lane of a scheduled CTA whose tile has at least two visits exits in every
maximal execution. -/
theorem scheduledRepeatedExitsOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (frame : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {g batch : Nat} (hg : g < l.threads) (hb : batch < p.batch)
    (lo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (multiple : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (hRole : Thread.roleOf l g ≠ .output) : Thread.Exited X g := by
  have hc : g/l.block < l.grid := NamedBar.cta_lt hg
  have eT : tileTrips p batch (g/l.block) =
      Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 := rfl
  have F := finalStateOfMaximal hp hMax frame hc hb lo hi multiple
  have hFrame := frame X hMax.1
  have hCuQ := (hFrame.metadataProtected hp).1
  obtain ⟨hm,hw12,hmc⟩ := mmaLaneFacts hp hc
  obtain ⟨_,upper,_⟩ := Mma.trips_bounds hp hb (assignedCoordinates_valid hp lo hi).1
  obtain ⟨_,_,limit⟩ := hp.lengths batch hb
  have hBound : tileTrips p batch (g/l.block) < 2^31 := by omega
  have hValue (mma : Nat) (hCta : mma/l.block = (g/l.block)) :
      Protocol.LoaderReady.DeliveredCohort l X mma
        (Mma.readyStage (2*(tileTrips p batch (g/l.block)-1)+1))
        ((2*(tileTrips p batch (g/l.block)-1)+1)/3) :=
    deliveredOfLoaderCounts hp hMax hFrame hc hCta (by omega)
      (fun h hh hw hCta' => F.loader h hh hw hCta' _ (by omega))
  -- the MMA warp
  have mmaTerminal (h : Nat) (hh : h < l.threads) (hw : warpIndex l h = 12)
      (hCta : h/l.block = (g/l.block)) :
      Mma.TerminalOutputIssues l X h ∧ Mma.MmaRelinquishPrefix l X h := by
    obtain ⟨_,_,_,⟨cur⟩⟩ := openingKeyReturnedWithTripsOfMaximal hp hMax hFrame hh hw hb
      (by rw [hCta]; exact lo) (by rw [hCta]; exact hi)
    rw [hCta] at cur
    obtain ⟨hIssues,hRel,_⟩ := Mma.steadyTerminalAndRelinquishOfTailCohorts hp hMax hCuQ
      (Protocol.Scores.correctionJointGuardsOfCuQ hp hMax.1 hCuQ) hh hw multiple hBound cur
      (fun v hv => steadyVisitCohortsOfCta (hmc.trans hCta.symm) (F.cohorts v hv))
      (hValue h hCta) (by rw [hCta]; exact F.probability)
    exact ⟨hIssues,hRel⟩
  -- the softmax terminal rows
  have rows : TerminalProducerRows p l X (g/l.block) (tileTrips p batch (g/l.block)) := by
    intro h hh hCta w hw
    have hw8 : warpIndex l h < 8 := hw ▸ w.isLt
    let stage : Fin 2 := ⟨warpIndex l h/4,by omega⟩
    have hm : BiasedStageMember l (g/l.block) stage h := ⟨hh,hCta,hw8,rfl⟩
    obtain ⟨maximum,sum,⟨term⟩⟩ := F.terminal stage h hm
    have hWork : h/l.block < tilePrefix p p.batch*p.heads := by
      rw [hCta]
      exact hi.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p (Nat.succ_le_of_lt hb)))
    obtain ⟨_,_,_,_,_,⟨geometry⟩⟩ := activeGroupOfMaximal hp hMax hh hw8 hCuQ hWork
    have hSelf : warpLane l h (laneOf l h) = h := Step.warpLane_of_sameWarp ⟨⟨hh,hh,rfl⟩,rfl⟩
    obtain ⟨source⟩ := activeSchedulerGeometry geometry (laneOf l h) (Nat.mod_lt _ (by decide))
    rw [hSelf] at source
    have hwOf : warpOf l h = w := Fin.ext ((warpOf_val hw8).trans hw)
    rw [← hwOf]
    exact term.producerRow hp hMax hh (warpOf_val hw8) source
  by_cases hRow : warpIndex l g < 13
  · obtain ⟨hIssues,_⟩ := mmaTerminal _ hm hw12 hmc
    exact repeatedRowsAndMmaExitOfTerminals hp hMax frame hc hb lo hi multiple rows hmc hIssues
      (fun h hh hw hCta => (mmaTerminal h hh hw hCta).2) g hg rfl hRow
  · have h13 : warpIndex l g ≠ 13 := by
      intro h; apply hRole; simp [Thread.roleOf,h]
    have hw : 14 ≤ warpIndex l g := by omega
    obtain ⟨hReleased,hQuery⟩ := loaderFinalReleasesOfTailCohorts hp hMax hFrame hg hb lo hi
      multiple (fun v hv => F.cohorts v hv) (hValue _ hmc) F.probability
    have hPos : 0 < Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 := by omega
    exact loaderPublishesAndExits hp hMax hFrame hg hw hb lo hi multiple hReleased
      (fun h14 round hr stage => by
        obtain ⟨hW,_⟩ := biasScheduleMatch p l h14 hPos stage
        have : Loader.warmRounds p l g batch =
            min (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1) 9 := rfl
        exact biasEmptyReleased_mono (F.biasReleased stage) (by omega))
      (fun h14 hSkip => by
        obtain ⟨hW,_,_,_,_,hTail⟩ := biasScheduleMatch p l h14 hPos 0
        have := hTail rfl hSkip
        have : Loader.warmRounds p l g batch =
            min (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1) 9 := rfl
        exact biasEmptyReleased_mono (F.biasReleased 0) (by omega))
      (fun _ => hQuery)

end PTX.Kernels.TmlFa4Fwd.Progress
