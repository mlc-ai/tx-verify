-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.AffineWarpRelease
public import Kernels.TmlFa4Fwd.Proof.Thread.PlainAffineProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedAffineOrdinals
import all Kernels.TmlFa4Fwd.Proof.Thread.Softmax
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Numeric Correction Thread.Scores

private theorem publicationNotCollective (e : Event) (h : publishesStats e = true) :
    isTcColl e = false := by
  obtain ⟨round,hr⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨_,_,_,hk⟩ := noticeSite hr
  cases e with
  | mk pc k =>
    change k = _ at hk
    subst k
    rfl

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFootprint : OutputFootprint p X)
    (hGuard : SyncGuarded l kernel X) (hLayout : TcMma.LayoutInjective X) {lead : Nat}
    (hLeadWarp : Prologue.warpIndex l lead < 8) (warp : Fin 8)
    (ordinal bars elects generation : Nat) (old : Nat → Option ℝ) (oldSum : Nat → ℝ)
    (phase : Nat → Nat) (scorePhase counter : Nat → Value) {F : Nat → List (Nat × Value)}
    (input : ∀ g, SameWarp l lead g → OpeningTripCursor l X g (scorePc .unbiased 0) (F g))
    (hWarp : ∀ g, SameWarp l lead g → warp.val = Prologue.warpIndex l g)
    (hAddress : ∀ g, SameWarp l lead g → ∀ q : Fin 4,
      (scoreReg .unbiased q,b32 (scoreAddress l g (stageOf warp) q)) ∈ F g)
    (hRank : ∀ g (hw : SameWarp l lead g),
      ((X.tr g).take (input g hw).pos).countP isTcColl = ordinal)
    (hBar : ∀ g (hw : SameWarp l lead g), warpBars X g (input g hw).pos = bars)
    (hElect : ∀ g (hw : SameWarp l lead g), elections X g (input g hw).pos = elects)
    (hGeneration : ∀ g (hw : SameWarp l lead g), (before X (g,(input g hw).pos)).notices =
      generation)
    (hWord : ∀ g, SameWarp l lead g → ∀ q : Fin 4, ∀ k < 32, ∀ value,
      TcMma.LastWrote l Assumptions.all X
        (tcDataCell l g .s32x32b (scoreAddress l g (stageOf warp) q) k) value →
          value.bytes = 4)
    (hPrior : ∀ g (hw : SameWarp l lead g), Holds (input g hw).ready.regs
      (plainAffineInputFrame p l g warp (old g) (oldSum g) (phase g) (scorePhase g) (counter g)))
    (hPhase : ∀ g, SameWarp l lead g → phase g < 2)
    (hScale : ∀ g (hw : SameWarp l lead g), readERealPair l g (input g hw).ready (.reg 8692) =
      some (.ok ((abiFloat p.scaleLog2Bits : EReal),(abiFloat p.scaleLog2Bits : EReal))))
    (hProbability : ∀ g (hw : SameWarp l lead g), ∀ q : Fin 4,
      (input g hw).ready.regs (probabilityReg .unbiased q) =
        some (b32 (probabilityAddress l g (stageOf warp) q)))
include hp hMax hFootprint hGuard hLayout hLeadWarp warp ordinal bars elects generation old oldSum
    phase scorePhase counter input hWarp hAddress hRank hBar hElect hGeneration hWord hPrior hPhase
    hScale hProbability

/-- A plain repeated score warp reads its four actual quarters, publishes the
rescale statistics, and reaches the affine cursor in a trace-equivalent maximal history. -/
theorem warpPlainAffineFromScoreWithObjectsOfMaximal :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧ Y.objects = X.objects ∧
      ∀ g (hw : SameWarp l lead g), ∃ scores : Nat → ℝ, ∃ candidate,
        ∃ u : OpeningTripCursor l Y g Repeated.unbiased.affineStart [],
          let scale := abiFloat p.scaleLog2Bits
          let chosen := chosenReference scale (old g) candidate
          let reference := chosen.map (scale * ·)
          u.pos = (input g hw).pos+10 ∧ u.ending = (input g hw).ending ∧
          ((Y.tr g).take u.pos).countP isTcColl = ordinal+8 ∧
          warpBars Y g u.pos = bars ∧ elections Y g u.pos = elects ∧
          StatisticsStore X (g,(input g hw).pos+8) (rescaleStore false) (statsAcc l g warp 1)
            (alphaWord scale (old g) candidate).toBytes ∧
          Publishes X (g,(input g hw).pos+9) .plain ∧
          Nonempty (RepeatedProbabilityShiftFrame p l .unbiased g (stageOf warp) u.ready
            (fun i => some (scores i)) (reference.getD 0)) ∧
          Nonempty (RepeatedTailOperands l .unbiased (stageOf warp) u.ready warp (oldSum g)
            (maskedRescale ((old g).map (scale * ·)) reference) (phase g)) ∧
          (u.ready.regs 7256 = some (scoreValue chosen) ∧
            u.ready.regs 7253 = some (scorePhase g) ∧ u.ready.regs 7254 = some (counter g)) ∧
          ((Y.tr g).take u.pos).countP publishesStats =
            ((X.tr g).take (input g hw).pos).countP publishesStats+1 ∧
          (∀ mark : Event → Bool, (∀ e, mark e = true → isTcColl e = false) →
            (∀ e, publishesStats e = true → mark e = false) →
            (∀ pc a bs, mark ⟨pc,.wr a bs⟩ = false) →
            ((Y.tr g).take u.pos).countP mark = ((X.tr g).take (input g hw).pos).countP mark) ∧
          (∀ v : EReal, scoreReal candidate ≤ v ↔
            scoreReal (old g) ≤ v ∧ ∀ i < 128, scoreReal (some (scores i)) ≤ v) := by
  classical
  let packed g hw := Classical.choice (warpRepeatedScoresOfFootprint hp hMax hFootprint hGuard
    hLayout lead ordinal .unbiased (stageOf warp) input hAddress hRank hWord g hw)
  have prepare (g : Nat) (hw : SameWarp l lead g) :=
    (packed g hw).plainAffineReachedOfFootprint hp hMax hFootprint hw.1.2.1 warp (hWarp g hw)
      (old g) (oldSum g) (phase g) (hPhase g hw) (scorePhase g) (counter g)
      (hPrior g hw) (hScale g hw) (hProbability g hw)
  choose scores candidate deferred hScores hBound hStore hNotice hPos hEnd hFrame hOperands hCont
    using prepare
  have hStart (g : Nat) (hw : SameWarp l lead g) :
      (packed g hw).cursor.pos = (input g hw).pos+8 := (packed g hw).position
  have hPosition (g : Nat) (hw : SameWarp l lead g) :
      (deferred g hw).pos = (input g hw).pos+10 := by rw [hPos g hw,hStart g hw]
  have hPub (g : Nat) (hw : SameWarp l lead g) :
      Publishes X (g,(deferred g hw).pos-1) .plain ∧
        (before X (g,(deferred g hw).pos-1)).notices = generation := by
    rw [hPos g hw,show ∀ n : Nat, n+2-1 = n+1 by omega]
    refine ⟨hNotice g hw,?_⟩
    rw [statisticsNoticeRankAfterStore .unbiased (hStore g hw)]
    have h := (packed g hw).keepsOtherCount publishesStats publicationNotCollective
    simp only [beforeNotices] at hGeneration ⊢
    exact h.trans (hGeneration g hw)
  obtain ⟨Y,hY,hTrace,hObjects,hResume⟩ :=
    resumeAffineWarpWithObjects hp hMax hFootprint hLeadWarp .unbiased generation deferred hPub
  refine ⟨Y,hY,hTrace,hObjects,?_⟩
  intro g hw
  obtain ⟨u,hUPos,hUReady,hUEnding⟩ := hResume g hw
  have hOrd := repeatedStatisticsKeepOrdinals .unbiased (hStore g hw) (hNotice g hw)
  have hBarKeep : ∀ e, Execution.isWarpBar e = true → isTcColl e = false := by
    intro e
    cases e with
    | mk pc kind => cases kind <;> simp [Execution.isWarpBar,isTcColl]
  have hElectKeep : ∀ e, isElectEv e = true → isTcColl e = false := by
    intro e
    cases e with
    | mk pc kind => cases kind <;> simp [isElectEv,isTcColl]
  refine ⟨scores g hw,candidate g hw,u,hUPos.trans (hPosition g hw),hUEnding.trans (hEnd g hw),
    ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hTrace,hUPos,hPos g hw,hOrd.1,(packed g hw).ordinal,hRank g hw]
    rfl
  · rw [warpBars,hTrace,hUPos,hPos g hw]
    have hr := (packed g hw).keepsOtherCount Execution.isWarpBar hBarKeep
    exact hOrd.2.1.trans (hr.trans (hBar g hw))
  · rw [elections,hTrace,hUPos,hPos g hw]
    have hr := (packed g hw).keepsOtherCount isElectEv hElectKeep
    exact hOrd.2.2.trans (hr.trans (hElect g hw))
  · simpa only [hStart g hw] using hStore g hw
  · simpa only [hStart g hw] using hNotice g hw
  · simpa only [hUReady] using hFrame g hw
  · simpa only [hUReady] using hOperands g hw
  · simpa only [hUReady] using hCont g hw
  · obtain ⟨nEv,hnGet,hnNotice⟩ := hNotice g hw
    rw [hTrace,hUPos,hPos g hw,show (packed g hw).cursor.pos+2 = (packed g hw).cursor.pos+1+1 by
      omega,countP_take_succ (p := publishesStats) hnGet (by simp [publishesStats,hnNotice]),
      countP_take_succ_false (hStore g hw) rfl,
      (packed g hw).keepsOtherCount publishesStats publicationNotCollective]
  · intro mark hTc hPubs hWr
    obtain ⟨nEv,hnGet,hnNotice⟩ := hNotice g hw
    rw [hTrace,hUPos,hPos g hw,show (packed g hw).cursor.pos+2 = (packed g hw).cursor.pos+1+1 by
      omega,countP_take_succ_false hnGet (hPubs _ (by simp [publishesStats,hnNotice])),
      countP_take_succ_false (hStore g hw) (hWr _ _ _),(packed g hw).keepsOtherCount mark hTc]
  · exact hBound g hw

end PTX.Kernels.TmlFa4Fwd.Softmax
