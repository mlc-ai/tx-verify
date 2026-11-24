-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.LoaderWarmRoundProgress
public import Kernels.TmlFa4Fwd.Proof.Progress.RecurringBiasAcquire
public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderWarmRoundBiasReady
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderWarmRoundBiasOpening
import all Kernels.TmlFa4Fwd.Proof.LoaderWarmBiasOrdinal
import Kernels.TmlFa4Fwd.Proof.Progress.FirstQueryReadyPhase
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSecondQueryProgress
import Kernels.TmlFa4Fwd.Proof.Protocol.OpeningBiasGuard
import Kernels.TmlFa4Fwd.Proof.LoaderBiasGuard
import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Lemmas.Flow.CountTake
import Lemmas.Flow.Polls

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Flow PTX.Proof PTX.MBarrier PTX.AsyncCopy Prologue Epilogue Thread.Loader
open Protocol.Bias
open PTX.Kernels.TmlFa4Fwd.Loader

/-- The decoded site of a stage's opening Bias expectation. -/
def openingBiasExpectSite : Fin 2 → Nat
  | 0 => 711
  | 1 => 763

/-- Warp 14 records the opening transaction expectation of each Bias stage. -/
theorem openingBiasExpectationsOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 14) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) (stage : Fin 2) :
    ∃ e, X.get e = some ⟨openingBiasExpectSite stage,
      .arrive (biasReadyObject l (g/l.block) stage) 32768 1 true .cta⟩ := by
  have writes : ∀ w a bytes loc, X.MemWrites w a bytes → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc :=
    fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame
  obtain ⟨_,_,hQ1,⟨issue0,hOpen0⟩,_⟩ :=
    selectedOpeningBiasPacketWithRankOfMaximal hp hMax hFrame hg hw hb hLo hHi
  fin_cases stage
  · exact ⟨issue0,hOpen0⟩
  · have hRank : 10+7*(batch/31)+(if 31*(batch/31)<batch then 1 else 0)+1 <
        Loader.primingSearchShuffleCount batch+32 := by
      unfold Loader.primingSearchShuffleCount
      omega
    have hBlock : l.block%32 = 0 := by rw [hp.block]
    obtain ⟨hQ1Entry,_,_⟩ :=
      Loader.openingSecondQueryExpectedFromCursorOfMaximal hp hMax hg hQ1
        (fun lane hl hBlocked => by
          have hSame := (Step.sameWarp_lane hBlock hg hl).1
          have hWarp : warpIndex l (warpLane l g lane) = 14 := hSame.2.symm.trans hw
          rw [hSame.1.2.2]
          exact Protocol.Loader.openingSecondQueryEmptyPhaseForBlockedLane
            hp hMax hSame.1.2.1 hWarp hBlocked)
    obtain ⟨hBias1,_⟩ :=
      Loader.selectedSecondBiasEntryOfMaximal hp hMax writes hg hw hb hLo hHi hRank hQ1Entry
    obtain ⟨_,issue,he⟩ := Loader.openingSecondBiasExpectedAtOfMaximal hp hMax hg hBias1
      (fun lane hl hBlocked => by
        have hSame := (Step.sameWarp_lane hBlock hg hl).1
        have hWarp : warpIndex l (warpLane l g lane) = 14 := hSame.2.symm.trans hw
        rw [hSame.1.2.2]
        exact Protocol.Bias.openingSecondBiasEmptyPhase hp hMax hSame.1.2.1 hWarp hBlocked)
    exact ⟨issue,he⟩

private theorem arrivalsAfter {X : Execution} {loc : Loc} {g a b : Nat} {e : Event}
    (he : X.get (g,a) = some e) (hOn : arrivesOn loc e = true) (hab : a < b) :
    arrivals loc ((X.tr g).take a)+1 ≤ arrivals loc ((X.tr g).take b) := by
  have hSucc := countP_take_succ (p := arrivesOn loc) he hOn
  have hMono := countP_take_mono (arrivesOn loc) (X.tr g) (show a+1 ≤ b by omega)
  unfold arrivals
  omega

/-- The warm expectation of round `round` on a Bias stage is preceded, in its issuer's trace,
by the opening expectation and by one warm expectation per earlier round. -/
theorem warmBiasExpectationOrdinal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta base pcW bound : Nat} (stage : Fin 2) (hpcW : 780 ≤ pcW)
    {o : EvId} (hO : X.get o = some ⟨openingBiasExpectSite stage,
      .arrive (biasReadyObject l cta stage) 32768 1 true .cta⟩)
    (hE : ∀ round < bound, ∃ e, X.get e = some ⟨pcW,
      .arrive (biasReadyObject l cta stage) 32768 1 true .cta⟩ ∧
        ((X.tr e.1).take e.2).countP Execution.isShfl = base+64*round)
    (round : Nat) (hBound : round ≤ bound) {e : EvId}
    (he : X.get e = some ⟨pcW,.arrive (biasReadyObject l cta stage) 32768 1 true .cta⟩)
    (hRank : ((X.tr e.1).take e.2).countP Execution.isShfl = base+64*round) :
    round+1 ≤ biasArrivalOrdinal X (biasReadyObject l cta stage) e := by
  let loc := biasReadyObject l cta stage
  have hOn : arrivesOn loc ⟨pcW,.arrive loc 32768 1 true .cta⟩ = true := by
    rw [arrivesOn_arrive rfl]
    exact decide_eq_true rfl
  induction round generalizing e with
  | zero =>
    obtain ⟨g,j⟩ := e
    obtain ⟨g₀,i⟩ := o
    have hSame := biasExpectationSameIssuer hp hX (⟨_,hO⟩ :
      X.Arrive (g₀,i) loc 32768 1 true .cta) (⟨_,he⟩ : X.Arrive (g,j) loc 32768 1 true .cta)
    subst g₀
    have hBefore := biasPrimingFloor hX hO he
      (by change openingBiasExpectSite stage < 780; fin_cases stage <;> decide) hpcW
    have hOnO : arrivesOn loc ⟨openingBiasExpectSite stage,.arrive loc 32768 1 true .cta⟩ =
        true := by
      rw [arrivesOn_arrive rfl]
      exact decide_eq_true rfl
    have := arrivalsAfter hO hOnO hBefore
    change _ ≤ arrivals loc ((X.tr g).take j)
    omega
  | succ round ih =>
    obtain ⟨⟨g',j'⟩,he',hRank'⟩ := hE round (by omega)
    have hPrev := ih (by omega) he' hRank'
    obtain ⟨g,j⟩ := e
    have hSame := biasExpectationSameIssuer hp hX (⟨_,he'⟩ :
      X.Arrive (g',j') loc 32768 1 true .cta) (⟨_,he⟩ : X.Arrive (g,j) loc 32768 1 true .cta)
    subst g'
    have hOrder : j' < j := by
      by_contra! h
      have := countP_take_mono Execution.isShfl (X.tr g) h
      change ((X.tr g).take j').countP Execution.isShfl = _ at hRank'
      change ((X.tr g).take j).countP Execution.isShfl = _ at hRank
      omega
    have := arrivalsAfter he' hOn hOrder
    change round+1 ≤ arrivals loc ((X.tr g).take j') at hPrev
    change _ ≤ arrivals loc ((X.tr g).take j)
    omega

set_option maxRecDepth 4096 in
/-- Warp 14 delivers the warm Bias generations of both stages for every warm round before
`bound`: generation `round+1` of a stage is the round's expectation together with its two
tensor halves. The hypotheses are facts about `X`: the MMA's release of each K/V use of those
rounds and softmax's release of each earlier Bias generation. -/
theorem warmBiasGenerationsDelivered {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g batch : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 14) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hTrips : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    {bound : Nat} (hReleased : CacheUsesReleased l X g (2+2*bound))
    (hBias : ∀ round < warmRounds p l g batch, round < bound → ∀ stage,
      BiasEmptyReleased l X (g/l.block) stage (round+1)) :
    ∀ stage : Fin 2, ∀ round < warmRounds p l g batch, round < bound →
      BiasGenerationDelivered l X (g/l.block) stage (round+1) := by
  have hRole : 14 ≤ warpIndex l g := by omega
  have hReady : warpIndex l g = 14 → ∀ round < warmRounds p l g batch, round < bound →
      WarmBiasEmptyReady l X g batch round := fun _ round hr hBound =>
    warmBiasEmptyReadyOfReleases hp hMax.1 hFrame hg hw hb hLo hHi hTrips hr
      (hBias round hr hBound)
  have hRounds := warmRoundsPublishedThrough hp hMax hFrame hg hRole hb hLo hHi hTrips
    hReleased hReady
  intro stage round hr hBound
  have issued := (hRounds round hr hBound).2.2 hw
  obtain ⟨o,hO⟩ := openingBiasExpectationsOfMaximal hp hMax hFrame hg hw hb hLo hHi stage
  obtain ⟨e,_,he,hRankE⟩ := issued.expectation stage
  have hpcW : 780 ≤ warmBiasSite (warmBiasExpectSite stage)+4 := by fin_cases stage <;> decide
  have hOrd := warmBiasExpectationOrdinal hp hMax.1 (base := primingSearchShuffleCount batch+96)
    (bound := round) stage hpcW hO (fun x hx => by
      obtain ⟨e',_,he',hR'⟩ := ((hRounds x (by omega) (by omega)).2.2 hw).expectation stage
      exact ⟨e',he',hR'⟩) round le_rfl he hRankE
  have hCuQ := (hFrame.metadataProtected hp).1
  have hCTA : g/l.block < tilePrefix p p.batch*p.heads :=
    hHi.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p (by omega)))
  obtain ⟨_,_,uniq⟩ := tileBatch_existsUnique p hCTA
  apply biasAdvancedOfIssuedHalves hp hMax hFrame ⟨e,⟨_,he⟩,hOrd⟩
  intro half
  obtain ⟨issue,hCta,hGet,hRankB⟩ := issued.boxes stage half
  let spec := inputSiteSpec p l issue.1 (inputSite (warmBiasInputSite stage half))
    (warmBiasColumn stage half round (warmBiasBit p l g batch))
    (warmBiasStageRow (warmBiasRow p l g batch) stage) (warmBiasHead p l g batch)
    (warmBiasStageBarrier l stage)
  have hBox : BiasSubbox p l X issue stage half spec := by
    refine ⟨⟨_,hGet⟩,?_⟩
    fin_cases stage <;> fin_cases half <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
  refine ⟨issue,spec,hCta,hBox,?_⟩
  obtain ⟨actor,j⟩ := issue
  obtain ⟨b,hB,hL,hH,round',_,hRound',hOrdB⟩ :=
    warmBiasOrdinalExact hp hMax.1 hFrame hCuQ stage half hBox hGet
  change actor/l.block = g/l.block at hCta
  rw [hCta] at hL hH
  have hEq : b = batch := (uniq b ⟨hB,hL,hH⟩).trans (uniq batch ⟨hb,hLo,hHi⟩).symm
  subst b
  change ((X.tr actor).take j).countP Execution.isShfl = _ at hRankB
  have hZ : round' = round := by omega
  rw [hOrdB,hZ]

end PTX.Kernels.TmlFa4Fwd.Progress
