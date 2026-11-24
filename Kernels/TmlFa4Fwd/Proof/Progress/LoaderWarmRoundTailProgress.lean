-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.LoaderWarmRoundBiasDelivery
public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderWarmRoundTailReady
import all Kernels.TmlFa4Fwd.Proof.LoaderWarmBiasOrdinal
import Kernels.TmlFa4Fwd.Proof.LoaderTailBiasOrdinal
import Kernels.TmlFa4Fwd.Proof.LoaderBiasGuard
import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Lemmas.Flow.CountTake
import Lemmas.Flow.Polls

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Flow PTX.Proof PTX.MBarrier PTX.AsyncCopy Prologue Epilogue Thread.Loader
open Protocol.Bias
open PTX.Kernels.TmlFa4Fwd.Loader

set_option maxRecDepth 4096 in
/-- Both loader warps pass the warm tail. Warp 14 runs the tail Bias block when the tile has
more than ten trips and an odd residual Bias half; it then delivers stage-zero Bias generation
`warmRounds+1` (generation ten). The hypotheses are facts about `X`: the MMA's release of the
warm K/V uses and softmax's release of each earlier stage-zero and stage-one Bias generation,
including generation `warmRounds` of stage zero before the tail. -/
theorem warmTailDoneOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTrips : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (hReleased : CacheUsesReleased l X g (2+2*warmRounds p l g batch))
    (hBias : warpIndex l g = 14 → ∀ round < warmRounds p l g batch, ∀ stage,
      BiasEmptyReleased l X (g/l.block) stage (round+1))
    (hTail : warpIndex l g = 14 → warmTailSkips p l g batch = false →
      BiasEmptyReleased l X (g/l.block) 0 (warmRounds p l g batch+1)) :
    Nonempty (WarmTailDone p l X g batch) ∧
      (warpIndex l g = 14 → warmTailSkips p l g batch = false →
        BiasGenerationDelivered l X (g/l.block) 0 (warmRounds p l g batch+1)) := by
  have hReady : warpIndex l g = 14 → ∀ round < warmRounds p l g batch,
      WarmBiasEmptyReady l X g batch round := fun h14 round hr =>
    warmBiasEmptyReadyOfReleases hp hMax.1 hFrame hg h14 hb hLo hHi hTrips hr (hBias h14 round hr)
  obtain ⟨⟨d⟩,hRounds⟩ := warmRoundsDoneOfMaximal hp hMax hFrame hg hw hb hLo hHi hTrips
    hReleased hReady
  cases hSkip : warmTailSkips p l g batch with
  | true =>
    exact ⟨d.tailSkipOfMaximal hp hw hb hLo hHi hSkip,fun _ h => by cases h⟩
  | false =>
    have h14 : warpIndex l g = 14 := by
      by_contra hNot
      unfold warmTailSkips at hSkip
      simp [hNot] at hSkip
    obtain ⟨hDone,issued⟩ := d.tailBiasOfMaximal hp hMax hg h14 hb hLo hHi hSkip
      (warmTailBiasReadyOfReleases hp hMax.1 hFrame hg h14 hb hLo hHi (hTail h14 hSkip))
    refine ⟨hDone,fun _ _ => ?_⟩
    have hLong : 10 < Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1 := by
      unfold warmTailSkips at hSkip
      simp only [h14,ne_eq,not_true_eq_false,decide_false,Bool.false_or,Bool.not_eq_eq_eq_not,
        Bool.not_false,Bool.and_eq_true,decide_eq_true_eq] at hSkip
      exact hSkip.1
    have hW9 : warmRounds p l g batch = 9 := by unfold warmRounds; omega
    -- The tail expectation follows the last warm expectation of stage zero.
    obtain ⟨o,hO⟩ := openingBiasExpectationsOfMaximal hp hMax hFrame hg h14 hb hLo hHi 0
    obtain ⟨⟨g',j'⟩,_,he',hRank'⟩ := ((hRounds 8 (by omega)).2.2 h14).expectation 0
    have hPrev := warmBiasExpectationOrdinal hp hMax.1 (base := primingSearchShuffleCount batch+96)
      (bound := warmRounds p l g batch) 0 (by decide) hO (fun x hx => by
        obtain ⟨e,_,he,hR⟩ := ((hRounds x hx).2.2 h14).expectation 0
        exact ⟨e,he,hR⟩) 8 (by omega) he' hRank'
    obtain ⟨⟨g₁,j⟩,he⟩ := issued.expectation
    let loc := biasReadyObject l (g/l.block) 0
    have hSame := biasExpectationSameIssuer hp hMax.1 (⟨_,he'⟩ :
      X.Arrive (g',j') loc 32768 1 true .cta) (⟨_,he⟩ : X.Arrive (g₁,j) loc 32768 1 true .cta)
    subst g₁
    have hOrder := biasTailFloor hMax.1 he' he
      (by change warmBiasSite (warmBiasExpectSite 0)+4 < 1353; decide)
      (by change 1353 ≤ 1368; decide)
    have hOn : arrivesOn loc ⟨warmBiasSite (warmBiasExpectSite 0)+4,
        .arrive loc 32768 1 true .cta⟩ = true := by
      rw [arrivesOn_arrive rfl]
      exact decide_eq_true rfl
    have hSucc := countP_take_succ (p := arrivesOn loc) he' hOn
    have hMono := countP_take_mono (arrivesOn loc) (X.tr g') (show j'+1 ≤ j by omega)
    have hOrd : warmRounds p l g batch+1 ≤ biasArrivalOrdinal X loc (g',j) := by
      change 8+1 ≤ arrivals loc ((X.tr g').take j') at hPrev
      change _ ≤ arrivals loc ((X.tr g').take j)
      unfold arrivals at hPrev ⊢
      omega
    apply biasAdvancedOfIssuedHalves hp hMax hFrame ⟨(g',j),⟨_,he⟩,hOrd⟩
    intro half
    obtain ⟨issue,hCta,hGet⟩ := issued.boxes half
    let spec := inputSiteSpec p l issue.1 (inputSite (tailBiasInputSite half)) (64*half.val)
      (warmBiasRow p l g batch) (warmBiasHead p l g batch) (l.sharedBase+320)
    have hBox : BiasSubbox p l X issue 0 half spec := by
      refine ⟨⟨_,hGet⟩,?_⟩
      fin_cases half <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
    refine ⟨issue,spec,hCta,hBox,?_⟩
    obtain ⟨actor,i⟩ := issue
    rw [tailBiasOrdinalExact hp hMax.1 hFrame (hFrame.metadataProtected hp).1 half hBox hGet,hW9]

end PTX.Kernels.TmlFa4Fwd.Progress
