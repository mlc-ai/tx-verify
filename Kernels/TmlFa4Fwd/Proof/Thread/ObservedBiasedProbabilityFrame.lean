-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedProbabilityNumeric
public import Kernels.TmlFa4Fwd.Proof.Thread.RescaleReferenceInputs
public import Kernels.TmlFa4Fwd.Proof.Thread.ObservedBiasedRescaleInputs
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxPriorMaximum
import Kernels.TmlFa4Fwd.Proof.SoftmaxWeights
import Kernels.TmlFa4Fwd.Proof.Thread.BiasedRescaleWindowFinish

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.TmlFa4Fwd.Softmax

noncomputable section

/-- The physical Bias logits and the carried registers at the actual alpha site. -/
structure BiasedProbabilityInputs (p : Params) (l : Launch) (warp : Fin 8)
    (scores : Nat → Option ℝ) (t : TState) : Prop where
  warpWord : t.regs 1062 = some (b32 warp.val)
  sharedBase : t.regs 2535 = some (b32 l.sharedBase)
  statisticsBarrier : t.regs 5127 = some (b32 (3+warp.val))
  negativeScale : t.regs 1230 = some (fl (-abiFloat p.scaleLog2Bits))
  scaleBits : t.regs 7132 = some (b32 p.scaleLog2Bits)
  mixed : ∃ pred, t.regs 634 = some (.pred pred)
  oldMass : ∃ value, t.regs 7257 = some value
  statisticsPhase : ∃ value, t.regs 7258 = some value
  logits : ∀ i ∈ biasBodyItems true, t.regs i.result =
    some (.pair (scoreValue (scores (2*(i.qk-7367))))
      (scoreValue (scores (2*(i.qk-7367)+1))))

private theorem biasedAlphaKeepsLogits :
    (biasBodyItems true).all
      (fun i => !((oWrites (alphaSite true).items).contains i.result)) = true := by decide +kernel

/-- A biased alpha cursor with its real score pairs yields the exact probability
frame after the same coefficient publication, also for a finite prefix. -/
theorem biasedProbabilityAfterArithmetic {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (warp : Fin 8) {g pos : Nat}
    (hWarp : warp.val = Prologue.warpIndex l g) (scores : Nat → Option ℝ)
    (hArithmetic :
      RescaleArithmeticEntryWith p l X (g,pos) true (BiasedProbabilityInputs p l warp scores))
    (hPresent : pos+2 < (X.tr g).length) :
    RepeatedProbabilityAfterCoefficient p l X .biased g pos := by
  obtain ⟨t,ending,old,candidate,word,hAt,hWord,hInput,hRun,frame⟩ := hArithmetic
  have hMore := recordedProbabilitySuffixNonempty (g := g) (j := pos) hRun
    (Or.inr (by omega))
  obtain ⟨u,hu,hTail,hKeep⟩ := alphaTraceWithScaleWordInPrefix true (scalePositive hp).1
    old candidate hWord hAt hInput hRun hMore
  have hFacts : At u 5675 [(1062,b32 warp.val),(2535,b32 l.sharedBase),
      (5127,b32 (3+warp.val)),(1362,alphaWord (abiFloat p.scaleLog2Bits) old candidate)] :=
    hu.mono ⟨(hKeep _ (by decide +kernel)).trans frame.warpWord,
      (hKeep _ (by decide +kernel)).trans frame.sharedBase,
      (hKeep _ (by decide +kernel)).trans frame.statisticsBarrier,hu.2.2.2.2.2.2.1,trivial⟩
  obtain ⟨predicate,hPred⟩ := frame.mixed
  have hLive (r : Nat) (hr : r ∈ biasedExpFrame) (hStage : r ≠ 637) :
      ∃ value, u.regs r = some value := by
    simp only [biasedExpFrame,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_,hFacts.2.2.2.2.1⟩
    · exact ⟨_,hFacts.2.2.2.2.2.1⟩
    · exact (hStage rfl).elim
    · exact ⟨_,hu.2.2.2.2.2.2.1⟩
    · obtain ⟨v,hv⟩ := frame.oldMass
      exact ⟨v,(hKeep _ (by decide +kernel)).trans hv⟩
    · obtain ⟨v,hv⟩ := frame.statisticsPhase
      exact ⟨v,(hKeep _ (by decide +kernel)).trans hv⟩
  have hLogits : ∀ i ∈ biasBodyItems true, u.regs i.result =
      some (.pair (scoreValue (scores (2*(i.qk-7367))))
        (scoreValue (scores (2*(i.qk-7367)+1)))) := by
    intro i hi
    have h := List.all_eq_true.mp biasedAlphaKeepsLogits _ hi
    exact (hKeep _ (by simpa using h)).trans (frame.logits i hi)
  obtain ⟨v,hFrame,hSuffix⟩ :=
    biasedProbabilityFrameAfterAlpha hp warp hWarp old candidate scores hFacts hu.2.2.2.2.2.1
      ((hKeep _ (by decide +kernel)).trans frame.negativeScale)
      ((hKeep _ (by decide +kernel)).trans frame.scaleBits)
      predicate ((hKeep _ (by decide +kernel)).trans hPred) hLogits hLive hTail (.inr hPresent)
  exact ⟨stageOf warp,v,ending,scores,_,hFrame,hSuffix⟩


/-- Transfer the real affine inputs and their live registers to the same
biased coefficient's probability packing. -/
theorem biasedProbabilityFrameOfObservedInputs {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) {g pos : Nat}
    (entry : ObservedBiasedRescaleInputs p l X g pos)
    {a : Acc} {data : List Byte} (he : StatisticsStore X (g,pos) (rescaleStore true) a data)
    (hPrior : CanonicalMaximum entry.before 7251)
    (hPresent : pos+2 < (X.tr g).length) :
    RepeatedProbabilityAfterCoefficient p l X .biased g pos := by
  have hStart : entry.firstLoad ≤ entry.enter :=
    (Nat.le_add_right ..).trans (entry.firstBefore.trans entry.waitBefore.le)
  have hIndex := biasedAffineEntryIndex entry.checkpoint entry.continuation
    hStart entry.enterBefore entry.noneBefore he
  obtain ⟨old,hOld⟩ := hPrior
  let scores (col : Nat) := affineScore (abiFloat p.invScaleBits) (entry.dot col) (entry.bias col)
  have hEntry := rescaleBiasedArithmeticEntryOfAffineInputsWithPairs hp old entry.bias entry.dot
    entry.checkpoint entry.inverseScale entry.unpacked entry.packed (entry.prior.trans hOld)
    entry.scale (hIndex ▸ entry.continuation) he
  apply biasedProbabilityAfterArithmetic hp entry.warp entry.warpIndex scores _ hPresent
  refine hEntry.mono (fun t ⟨hPairs,hMixed,hKeep⟩ => ?_)
  obtain ⟨mass,hMass⟩ := entry.oldMass
  obtain ⟨phase,hPhase⟩ := entry.statisticsPhase
  exact ⟨(hKeep _ (by decide +kernel)).trans entry.geometry.1,
    (hKeep _ (by decide +kernel)).trans entry.geometry.2.1,
    (hKeep _ (by decide +kernel)).trans entry.geometry.2.2.1,
    (hKeep _ (by decide +kernel)).trans entry.negativeScale,
    (hKeep _ (by decide +kernel)).trans entry.scale,hMixed,
    ⟨mass,(hKeep _ (by decide +kernel)).trans hMass⟩,
    ⟨phase,(hKeep _ (by decide +kernel)).trans hPhase⟩,hPairs⟩


/-- The actual same-visit Bias reads and releases supply the biased probability
frame. The remaining historical input is the maximum carried into its Bias wait. -/
theorem biasedProbabilityFrameOfObservedCoefficient {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g pos : Nat} {a : Acc} {data : List Byte}
    (he : StatisticsStore X (g,pos) (rescaleStore true) a data)
    (hPresent : pos+2 < (X.tr g).length)
    (hPrior : ∀ entry : ObservedBiasedRescaleInputs p l X g pos,
      CanonicalMaximum entry.before 7251) :
    RepeatedProbabilityAfterCoefficient p l X .biased g pos := by
  obtain ⟨entry⟩ := observedBiasedRescaleInputs hp hX hFrame he
  exact biasedProbabilityFrameOfObservedInputs hp entry he (hPrior entry) hPresent

end
end PTX.Kernels.TmlFa4Fwd.Thread.Scores
