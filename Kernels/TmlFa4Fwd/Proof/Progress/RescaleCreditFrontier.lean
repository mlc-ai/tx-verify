-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.RescaleLoopTerminal
public import Kernels.TmlFa4Fwd.Proof.Thread.RescaleReturnedCredits
public import Kernels.TmlFa4Fwd.Proof.Protocol.TerminalStatisticsCredit
import Kernels.TmlFa4Fwd.Proof.OutputProtection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Flow Prologue Epilogue Thread
open _root_.PTX.Kernels.TmlFa4Fwd.Correction
open Protocol.Statistics

/-- Only the earlier rounds are needed to reach the current stage-zero rendezvous. -/
theorem rescaleJoinOfEarlierPublications {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (frame : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {g batch : Nat} (hg : g < l.threads) (hw : 8 ≤ warpIndex l g ∧ warpIndex l g < 12)
    (hb : batch < p.batch) (lo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hi : g/l.block < tilePrefix p (batch+1)*p.heads) (round : Nat)
    (active : round+1 < Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (pub : RepeatedStatisticsPublished l X g (round+1)) :
    ∃ votes rank, Nonempty (RescaleWarpJoin p l X g batch
      (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-round)
      0 (fun _ => round+1) votes rank) := by
  let trips := Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1
  have bound : trips < 2^31 := by
    obtain ⟨_,upper,_⟩ := Mma.trips_bounds hp hb (assignedCoordinates_valid hp lo hi).1
    obtain ⟨_,_,limit⟩ := hp.lengths batch hb
    dsimp only [trips]
    omega
  change round+1 < trips at active
  induction round with
  | zero => exact ⟨_,_,openingRescaleWarpOfMaximal hp hMax (frame X hMax.1) hw hb lo hi active⟩
  | succ k ih =>
    obtain ⟨_,_,⟨c⟩⟩ := ih (fun gen pos lt => pub gen pos (by omega)) (by omega)
    obtain ⟨_,_,⟨a⟩⟩ := rescaleWarpReturnedOfPublications hp hMax frame hg hw c
      (pub (k+1) (by omega) (by omega) 0)
    obtain ⟨b⟩ := a.stageOne hp hMax
    obtain ⟨_,_,⟨z⟩⟩ := rescaleWarpReturnedOfPublications hp hMax frame hg hw b
      (pub (k+1) (by omega) (by omega) 1)
    change RescaleWarpReturned _ _ _ _ _ (trips-k) _ _ _ _ at z
    obtain ⟨next⟩ := z.nextRound hp hMax (by omega) (by omega)
    have counts : rescaleNextGeneration (rescaleNextGeneration (fun _ => k+1) 0) 1 =
        fun _ => k+1+1 := by
      funext stage
      fin_cases stage <;> simp [rescaleNextGeneration]
    rw [counts] at next
    exact ⟨_,_,⟨next⟩⟩

/-- A cohort may publish a later generation before the consumer claims this one. -/
def SoftmaxStagePublishedThrough (l : Launch) (X : Execution) (cta : Nat)
    (stage : Fin 2) (number : Nat) : Prop :=
  ∀ h < l.threads, h/l.block = cta → warpIndex l h/4 = stage.val →
    ∃ i r, Scores.Publishes X (h,i) r ∧ number ≤ observedBarrierOrdinal X (h,i) (3+warpIndex l h)

private theorem SoftmaxStagePublishedThrough.paired {l : Launch} {X : Execution}
    {g n : Nat} {stage : Fin 2} (s : SoftmaxStagePublishedThrough l X (g/l.block) stage n) :
    ∀ h < l.threads, h/l.block = g/l.block → warpIndex l h = (waitingWarp l g stage).val →
      ∃ i r, Scores.Publishes X (h,i) r ∧ n ≤ observedBarrierOrdinal X (h,i) (3+warpIndex l h) := by
  intro h ht hc hw
  apply s h ht hc
  simp only [waitingWarp] at hw
  omega

/-- Each stage releases the opposite softmax statistics slot. Stage zero
can release stage one while stage one's current publication is still pending. -/
theorem pairedRescaleCreditsOfPublications {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (frame : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {cta batch : Nat} (hb : batch < p.batch)
    (lo : tilePrefix p batch*p.heads ≤ cta) (hi : cta < tilePrefix p (batch+1)*p.heads)
    (round : Nat) (active : round+1 < Mma.trips p batch (assignedCoordinates p batch cta).1)
    (stage : Fin 2) (zero : SoftmaxStagePublishedThrough l X cta 0 (round+1))
    (one : SoftmaxStagePublishedThrough l X cta 1 (round+stage.val)) :
    ∀ h < l.threads, h/l.block = cta → 8 ≤ warpIndex l h ∧ warpIndex l h < 12 →
      PairedRescaleCredit l X h stage (round+stage.val) := by
  intro h hh ctaEq hw
  have self : SameWarp l h h := ⟨⟨hh,hh,rfl⟩,rfl⟩
  have previous : RepeatedStatisticsPublished l X h (round+1) := by
    intro gen _ bound s g hg hc' w
    fin_cases s
    · obtain ⟨i,r,pub,rank⟩ := (SoftmaxStagePublishedThrough.paired
        (g := h) (ctaEq.symm ▸ zero)) g hg hc' w
      exact ⟨i,r,pub,by omega⟩
    · obtain ⟨i,r,pub,rank⟩ := (SoftmaxStagePublishedThrough.paired
        (g := h) (ctaEq.symm ▸ one)) g hg hc' w
      exact ⟨i,r,pub,by omega⟩
  obtain ⟨_,_,⟨start⟩⟩ := rescaleJoinOfEarlierPublications hp hMax frame hh hw hb
    (ctaEq.symm ▸ lo) (ctaEq.symm ▸ hi) round (ctaEq.symm ▸ active) previous
  obtain ⟨_,_,⟨a⟩⟩ := rescaleWarpReturnedOfPublications hp hMax frame hh hw start
    (SoftmaxStagePublishedThrough.paired (ctaEq.symm ▸ zero))
  fin_cases stage
  · exact a.pairedCredit hp hMax.1 self hw rfl
  · obtain ⟨b⟩ := a.stageOne hp hMax
    obtain ⟨_,_,⟨z⟩⟩ := rescaleWarpReturnedOfPublications hp hMax frame hh hw b
      (SoftmaxStagePublishedThrough.paired (ctaEq.symm ▸ one))
    exact z.pairedCredit hp hMax.1 self hw rfl

/-- Each stage releases the opposite softmax statistics slot. Stage zero
can release stage one while stage one's current publication is still pending. -/
theorem statisticsCreditsOfRescalePublications {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (frame : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {cta batch : Nat} (hc : cta < l.grid) (hb : batch < p.batch)
    (lo : tilePrefix p batch*p.heads ≤ cta) (hi : cta < tilePrefix p (batch+1)*p.heads)
    (round : Nat) (active : round+1 < Mma.trips p batch (assignedCoordinates p batch cta).1)
    (stage : Fin 2) (zero : SoftmaxStagePublishedThrough l X cta 0 (round+1))
    (one : SoftmaxStagePublishedThrough l X cta 1 (round+stage.val)) :
    TerminalCorrectionCredits l X cta stage.rev (round+stage.val) := by
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
  obtain ⟨j,_,e,he,ha,n⟩ := pairedRescaleCreditsOfPublications hp hMax frame hb lo hi round
    active stage zero one h hh ctaEq hw
  exact ⟨j+1,e,he,ha,n⟩

end PTX.Kernels.TmlFa4Fwd.Progress
