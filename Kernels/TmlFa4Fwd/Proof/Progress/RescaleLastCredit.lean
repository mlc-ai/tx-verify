-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.RescaleCreditFrontier

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Flow Prologue Epilogue Thread
open _root_.PTX.Kernels.TmlFa4Fwd.Correction
open Protocol.Statistics

/-- The publications of both stages through the generation before the last
are the publications the rescale walk consumes. -/
theorem repeatedStatisticsPublishedOfStages {l : Launch} {X : Execution} {g n : Nat}
    (zero : SoftmaxStagePublishedThrough l X (g/l.block) 0 (n-1))
    (one : SoftmaxStagePublishedThrough l X (g/l.block) 1 (n-1)) :
    RepeatedStatisticsPublished l X g n := by
  intro gen _ bound stage h hh hc hw
  have hs : warpIndex l h/4 = stage.val := by
    simp only [waitingWarp] at hw
    have := stage.isLt
    omega
  fin_cases stage
  · obtain ⟨i,r,pub,rank⟩ := zero h hh hc hs
    exact ⟨i,r,pub,by omega⟩
  · obtain ⟨i,r,pub,rank⟩ := one h hh hc hs
    exact ⟨i,r,pub,by omega⟩

/-- After its last rescale round a correction lane returns stage one's
statistics slot once more. Before this credit the lane has returned stage
one's slot once for every earlier generation of the tile. -/
theorem lastStageOneCreditAt {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (frame : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {g batch : Nat} (hg : g < l.threads) (hw : 8 ≤ warpIndex l g ∧ warpIndex l g < 12)
    (hb : batch < p.batch) (lo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (multiple : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (zero : SoftmaxStagePublishedThrough l X (g/l.block) 0
      (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1))
    (one : SoftmaxStagePublishedThrough l X (g/l.block) 1
      (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1)) :
    ∃ j e, X.get (g,j) = some e ∧ correctionAction e = some (.statsCredit 1) ∧
      (correctionBefore X (g,j)).count (.statsCredit 1) =
        Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1 := by
  have self : SameWarp l g g := ⟨⟨hg,hg,rfl⟩,rfl⟩
  obtain ⟨_,_,⟨last⟩⟩ := repeatedCorrectionLastReturnOfPublications hp hMax frame hg hw hb
    lo hi multiple (repeatedStatisticsPublishedOfStages zero one)
  obtain ⟨⟨pc,he⟩,_⟩ := last.terminal hp hMax self
  let pos := (last.lane g self).pos
  let e : Event := ⟨pc,.arrive (statsCreditLoc l (g/l.block) 1) 0 1 true .cta⟩
  have recorded : X.get (g,pos) = some e := he
  have action := statsCreditArrivalAction hp hMax.1 1 recorded
  have mark := (correctionStatsCreditMark_iff 1 e).mpr
    ((correctionStatsCreditObservation 1 (show e.kind = _ from rfl)).mp action)
  have balance := correctionCreditRequiresWait hMax.1 1 recorded mark
  rw [correctionWaitPrefixCount hp hMax.1 1 (len_of_get recorded) hw] at balance
  have named := last.named g self 1
  change ((X.tr g).take pos).countP (Execution.isBarId (statsBarrierId l g 1)) = _ at named
  change ((X.tr g).take pos).countP (Execution.isBarId (statsBarrierId l g 1)) =
    ((X.tr g).take pos).countP (correctionStatsCreditMark 1) + 1 at balance
  refine ⟨pos,e,recorded,action,?_⟩
  rw [correctionCreditCursor hp hMax.1 1 recorded]
  change ((X.tr g).take pos).countP (correctionStatsCreditMark 1) = _
  omega

/-- Stage one's correction credit of the last generation of a tile with
several KV blocks, from all 128 correction lanes. -/
theorem lastStageOneCreditOfPublications {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (frame : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {cta batch : Nat} (hc : cta < l.grid) (hb : batch < p.batch)
    (lo : tilePrefix p batch*p.heads ≤ cta) (hi : cta < tilePrefix p (batch+1)*p.heads)
    (multiple : 2 ≤ Mma.trips p batch (assignedCoordinates p batch cta).1)
    (zero : SoftmaxStagePublishedThrough l X cta 0
      (Mma.trips p batch (assignedCoordinates p batch cta).1-1))
    (one : SoftmaxStagePublishedThrough l X cta 1
      (Mma.trips p batch (assignedCoordinates p batch cta).1-1)) :
    TerminalCorrectionCredits l X cta 1
      (Mma.trips p batch (assignedCoordinates p batch cta).1-1) := by
  intro lane
  let h := statsCreditLane l cta lane
  have hl : 256+lane.val < l.block := by rw [hp.block]; have := lane.isLt; omega
  have hh : h < l.threads := by
    simpa only [h,statsCreditLane,Nat.add_assoc] using NamedBar.cta_thread_lt hc hl
  obtain ⟨owner,offset⟩ := NamedBar.lane_cta (c := cta) (NamedBar.block_pos_of_thread_lt hh) hl
  have ctaEq : h/l.block = cta := by simpa only [h,statsCreditLane,Nat.add_assoc] using owner
  have localLane : h%l.block = 256+lane.val := by
    simpa only [h,statsCreditLane,Nat.add_assoc] using offset
  have hw : 8 ≤ warpIndex l h ∧ warpIndex l h < 12 := by
    rw [warpIndex,localLane]
    have := lane.isLt
    omega
  have credit := lastStageOneCreditAt hp hMax frame hh hw hb (ctaEq.symm ▸ lo)
    (ctaEq.symm ▸ hi) (ctaEq.symm ▸ multiple) (ctaEq.symm ▸ zero) (ctaEq.symm ▸ one)
  rw [ctaEq] at credit
  exact credit

end PTX.Kernels.TmlFa4Fwd.Progress
