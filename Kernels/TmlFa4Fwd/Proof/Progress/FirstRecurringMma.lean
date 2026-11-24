-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.FirstWarmKeyPublication
public import Kernels.TmlFa4Fwd.Proof.Progress.MmaRecurringNotifications
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyOpeningLedger
public import Kernels.TmlFa4Fwd.Proof.Progress.OpeningProbabilityCohorts
import Kernels.TmlFa4Fwd.Proof.Progress.OpeningTailValue
import Kernels.TmlFa4Fwd.Proof.Progress.RecurringCacheDelivery
import Kernels.TmlFa4Fwd.Proof.OutputProtection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX Prologue Epilogue Thread Protocol.LoaderReady

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (frame : OutputFootprint p X)
include hp hMax frame

private theorem firstDeliveredOfPublications {g : Nat} (hg : g < l.threads) (s : Fin 3)
    (all : ∀ h < l.threads, 14 ≤ warpIndex l h → h/l.block = g/l.block →
      ∃ j, X.AsyncArrive (h,j) (Thread.Loader.readyObject l h s) true) :
    DeliveredCohort l X g s 0 := by
  intro lane
  let h := Thread.Loader.producer l (g/l.block) lane
  have hl : 448+lane.val < l.block := by rw [hp.block]; have := lane.isLt; omega
  have wb : 0 < l.block := by rw [hp.block]; decide
  obtain ⟨hc,off⟩ := NamedBar.lane_cta (c := g/l.block) wb hl
  have owner : h/l.block = g/l.block := by
    simpa only [h,Thread.Loader.producer,Loader.readyProducer,Nat.add_assoc] using hc
  have localLane : h%l.block = 448+lane.val := by
    simpa only [h,Thread.Loader.producer,Loader.readyProducer,Nat.add_assoc] using off
  have hh : h < l.threads := (Nat.div_lt_iff_lt_mul wb).mp (owner.symm ▸ NamedBar.cta_lt hg)
  obtain ⟨j,issued⟩ := all h hh (by unfold warpIndex; rw [localLane]; omega) owner
  have addr : Thread.Loader.readyObject l h s = Thread.Loader.readyObject l g s := by
    simp only [Thread.Loader.readyObject,owner]
  rw [addr] at issued
  cases gen : generation l X (h,j) s with
  | zero => exact ⟨_,rfl,issued,drainedCachePublication hp hMax frame issued,gen⟩
  | succ k => exact earlierCohortsOfPublication hp hMax.1 issued gen 0 (Nat.zero_le _) lane

/-- The cohorts of the first steady MMA visit: the opening P cohorts, the first V and the
next K, delivered by both loader warps. -/
theorem firstSteadyVisitCohorts {g batch : Nat} (hg : g < l.threads) (hb : batch < p.batch)
    (lo : tilePrefix p batch*p.heads ≤ g/l.block) (hi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (multiple : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1) :
    Mma.SteadyVisitCohorts l X g 0 := by
  constructor
  · apply firstDeliveredOfPublications hp hMax frame hg 1
    intro h hh wh cta
    have self : warpLane l h (laneOf l h) = h := Step.warpLane_of_sameWarp ⟨⟨hh,hh,rfl⟩,rfl⟩
    have packet : OpeningValuePacketPublished p l X h batch := by
      by_cases h14 : warpIndex l h = 14
      · exact openingValuePacketPublishedByFirstLoaderOfMaximal hp hMax frame hh h14 hb
          (cta.symm ▸ lo) (cta.symm ▸ hi)
      · have h15 : warpIndex l h = 15 := by have := warpIndex_lt hp h; omega
        exact openingValuePacketPublishedBySecondLoaderOfMaximal hp hMax frame hh h15 hb
          (cta.symm ▸ lo) (cta.symm ▸ hi)
    obtain ⟨i,pub,_⟩ := packet.1 (laneOf l h) (Nat.mod_lt _ (by decide))
    have issued := pub.arrive
    rw [self] at issued
    exact ⟨i,issued⟩
  · apply firstDeliveredOfPublications hp hMax frame hg 2
    intro h hh wh cta
    obtain ⟨key⟩ := openingAndFirstWarmKeyPublishedOfMaximal hp hMax frame hh wh hb
      (cta.symm ▸ lo) (cta.symm ▸ hi) (cta.symm ▸ multiple)
    obtain ⟨i,_,pub⟩ := key.published (laneOf l h) (Nat.mod_lt _ (by decide))
    have self : warpLane l h (laneOf l h) = h := Step.warpLane_of_sameWarp ⟨⟨hh,hh,rfl⟩,rfl⟩
    exact ⟨i,by simpa only [self] using pub⟩
  · exact fun s b => openingProbabilityCohortOfMaximal hp hMax frame (NamedBar.cta_lt hg)
      s b hb lo hi

end PTX.Kernels.TmlFa4Fwd.Progress
