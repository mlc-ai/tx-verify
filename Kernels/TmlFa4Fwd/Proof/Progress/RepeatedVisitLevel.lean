-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.SoftmaxStageStep
public import Kernels.TmlFa4Fwd.Proof.Progress.SoftmaxVisitOneHeads
public import Kernels.TmlFa4Fwd.Proof.Progress.BiasScheduleMatch
public import Kernels.TmlFa4Fwd.Proof.Progress.LoaderRoundsThrough
public import Kernels.TmlFa4Fwd.Proof.Progress.RepeatedCacheReleases
public import Kernels.TmlFa4Fwd.Proof.Progress.RepeatedJointProbability
public import Kernels.TmlFa4Fwd.Proof.Progress.RescaleLastCredit
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderFirstWarmBias
public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningDenominatorProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.BiasedScoreProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedScorePollRanks
public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningDenominatorScoreCount
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedScoreRoundProgress
public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedVisitRank
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxScorePhase
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedAffineOrdinals
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedScoreBiasProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedBiasAcquireInput

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Flow Prologue Epilogue Thread Softmax
open Protocol.Bias (BiasEmptyReleased)

/-- The trip count of the tile assigned to a CTA. -/
abbrev tileTrips (p : Params) (batch cta : Nat) : Nat :=
  Mma.trips p batch (assignedCoordinates p batch cta).1

/-- Every lane of a softmax stage is at the head of visit `visit`, with warp-uniform
warp-barrier and election counts and the arrivals of the earlier visits. -/
def StageHeads (p : Params) (l : Launch) (X : Execution) (batch cta : Nat) (stage : Fin 2)
    (visit : Nat) : Prop :=
  ∃ barsW electsW : Nat → Nat, ∀ g, BiasedStageMember l cta stage g → ∃ pos,
    LoopHeadAt p l X (tileTrips p batch cta) (stageSplit p batch cta stage) g (warpOf l g) visit
      (barsW (warpIndex l g)) (electsW (warpIndex l g)) pos ∧
    HeadArrivals l X cta stage (stageBiased p batch cta stage) g visit pos

/-- The state of a scheduled multi-visit CTA before visit `visit` of both softmax stages.
Stage zero is at its heads; stage one reaches its heads once stage zero has published the
visit; the MMA cohorts of the earlier visits and the probability cohorts of the previous visit
are published; each stage has released its Bias storage once per earlier biased visit. -/
structure LevelState (p : Params) (l : Launch) (X : Execution) (batch cta visit : Nat) :
    Prop where
  zero : StageHeads p l X batch cta 0 visit
  one : SoftmaxStagePublishedThrough l X cta 0 visit → StageHeads p l X batch cta 1 visit
  publishedOne : SoftmaxStagePublishedThrough l X cta 1 (visit-1)
  cohorts : ∀ j, j+1 < visit → Mma.SteadyVisitCohorts l X (cta*l.block+384) j
  probability : ∀ stage packet : Fin 2,
    Protocol.Scores.ProbabilityCohort l X cta stage packet (visit-1)
  biasReleased : ∀ stage : Fin 2,
    BiasEmptyReleased l X cta stage (min visit (stageBiased p batch cta stage))

theorem biasEmptyReleased_mono {l : Launch} {X : Execution} {cta : Nat} {stage : Fin 2}
    {a b : Nat} (h : BiasEmptyReleased l X cta stage b) (hab : a ≤ b) :
    BiasEmptyReleased l X cta stage a := by
  obtain ⟨s,hs,hb⟩ := h
  exact ⟨s,hs,hab.trans hb⟩

/-- A stage that published a visit has published through that visit. -/
theorem StageVisitOutputs.publishedThrough {l : Launch} {X : Execution} {cta : Nat}
    {stage : Fin 2} {biased visit : Nat}
    (h : StageVisitOutputs l X cta stage biased visit) :
    SoftmaxStagePublishedThrough l X cta stage visit := by
  intro g hg hc hw
  have hs := stage.isLt
  have h8 : warpIndex l g < 8 := by omega
  exact h.published g ⟨hg,hc,h8,hw⟩

/-- Lane `lane` of the softmax warp `4*stage+w` of a CTA. -/
theorem stageLaneMember {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m) {cta : Nat}
    (hc : cta < l.grid) (stage : Fin 2) (w : Fin 4) {lane : Nat} (hl : lane < 32) :
    let g := cta*l.block+(32*(4*stage.val+w.val)+lane)
    BiasedStageMember l cta stage g ∧ laneOf l g = lane ∧
      warpIndex l g = 4*stage.val+w.val := by
  intro g
  have hs := stage.isLt
  have hw := w.isLt
  have hLocal : 32*(4*stage.val+w.val)+lane < l.block := by rw [hp.block]; omega
  have hb : 0 < l.block := by rw [hp.block]; decide
  obtain ⟨hCta,hMod⟩ := NamedBar.lane_cta (c := cta) hb hLocal
  have hg : g < l.threads := NamedBar.cta_thread_lt hc hLocal
  have hWarp : warpIndex l g = 4*stage.val+w.val := by
    unfold warpIndex; rw [hMod]; omega
  refine ⟨⟨hg,hCta,by omega,by rw [hWarp]; omega⟩,?_,hWarp⟩
  unfold laneOf
  rw [hMod]
  omega

/-- The main probability cohort of a repeated visit, from the stage publications and the main
credits of the visit. -/
theorem mainCohortOfOutputs {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (frame : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {cta batch : Nat} (hc : cta < l.grid) (hb : batch < p.batch)
    (lo : tilePrefix p batch*p.heads ≤ cta) (hi : cta < tilePrefix p (batch+1)*p.heads)
    {stage : Fin 2} {biased visit : Nat} (hVisit : 1 ≤ visit)
    (active : visit < tileTrips p batch cta)
    (zero : SoftmaxStagePublishedThrough l X cta 0 visit)
    (one : SoftmaxStagePublishedThrough l X cta 1 (visit-1+stage.val))
    (out : StageVisitOutputs l X cta stage biased visit) :
    Protocol.Scores.ProbabilityCohort l X cta stage 0 visit := by
  have hv := Nat.sub_add_cancel hVisit
  have h := repeatedMainProbabilityCohortOfPublications hp hMax frame hc hb lo hi (visit-1)
    (by rw [hv]; exact active) stage (by rw [Nat.sub_add_cancel hVisit]; exact zero) one (by
      intro g hg hCta hw hs
      have hPos := out.main g ⟨hg,hCta,hw,hs⟩
      obtain ⟨i,hCredit,hOrd⟩ := Protocol.Scores.probabilityCreditOfExtent hp hMax.1
        (gen := visit-1+1) stage 0 (by unfold arrivals at hPos; rw [hv]; exact hPos)
      exact ⟨i,hCredit,hOrd⟩)
  rwa [hv] at h

/-- The tail probability cohort of a repeated visit: in each warp of the stage the elected
leader has issued one tail credit per visit. -/
theorem tailCohortOfOutputs {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {cta batch : Nat}
    (hc : cta < l.grid) {stage : Fin 2} {visit : Nat}
    (heads : StageHeads p l X batch cta stage visit)
    (out : StageVisitOutputs l X cta stage (stageBiased p batch cta stage) visit) :
    Protocol.Scores.ProbabilityCohort l X cta stage 1 visit := by
  obtain ⟨barsW,electsW,H⟩ := heads
  apply Protocol.Scores.tailProbabilityCohortOfWarps
  intro a
  obtain ⟨hmLead,hLaneLead,hWarpLead⟩ := stageLaneMember hp hc stage a (lane := 0) (by decide)
  obtain ⟨_,_,_,⟨leader,⟨i,pc,inst,hE⟩,_⟩,_⟩ := H _ hmLead
  have hLeader : leader < 32 := (hX.elect.1 _ _ _ _ _ hE).2.2.1
  obtain ⟨hm,hLane,hWarp⟩ := stageLaneMember hp hc stage a hLeader
  obtain ⟨_,_,_,⟨leader',⟨i',pc',inst',hE'⟩,_⟩,_⟩ := H _ hm
  have hSame : SameWarp l (cta*l.block+(32*(4*stage.val+a.val)+0))
      (cta*l.block+(32*(4*stage.val+a.val)+leader)) :=
    ⟨⟨hmLead.1,hm.1,hmLead.2.1.trans hm.2.1.symm⟩,
      (show warpIndex l _ = warpIndex l _ from hWarpLead.trans hWarp.symm)⟩
  have e : leader = leader' := hX.elect.2.2 _ _ _ _ _ _ _ _ _ hE hE' hSame
  have hPos := out.tail _ hm leader' ⟨i',pc',inst',hE'⟩ (hLane.trans e)
  obtain ⟨j,hCredit,hOrd⟩ := Protocol.Scores.probabilityCreditOfExtent hp hX (gen := visit)
    stage 1 (by unfold arrivals at hPos; exact hPos)
  refine ⟨_,hCredit,hOrd,?_⟩
  rw [hWarp]
  omega

/-- A stage that released its Bias storage in a biased visit has completed one more
Bias-empty phase. -/
theorem biasReleasedOfOutputs {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) {cta : Nat}
    (hc : cta < l.grid) {stage : Fin 2} {biased visit : Nat} (hB : visit < biased)
    (out : StageVisitOutputs l X cta stage biased visit) :
    BiasEmptyReleased l X cta stage (visit+1) := by
  apply Protocol.Bias.biasEmptyReleasedOfArrivals hp hX stage (Nat.succ_pos _)
  intro w
  obtain ⟨hm,hLane,hWarp⟩ := stageLaneMember hp hc stage w (lane := 0) (by decide)
  exact ⟨_,hWarp,by have := out.bias hB _ hm hLane; unfold arrivals at this; exact this⟩

end PTX.Kernels.TmlFa4Fwd.Progress
