-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedStatisticsProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.AffineCursor
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedProbabilityDenominatorProgress
public import Lemmas.Real.MaskedSoftmaxUpdate
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLaterBiasFma
import all Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedRound
import all Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedRescale

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Numeric Prologue Correction Thread.Scores

/-- The scalar ABI and control used by the biased maximum and rescale path. -/
noncomputable def biasedAffineInputFrame (p : Params) (l : Launch) (warp : Fin 8)
    (old : Option ℝ) (oldSum : ℝ) (nextBlock floor phase : Nat)
    (biasPhase scorePhase counter : Value) : List (Nat × Value) :=
  [(7251,scoreValue old),(7257,fl oldSum),(7249,b32 nextBlock),(1361,b32 floor),
    (7258,b32 phase),(1062,b32 warp.val),(2535,b32 l.sharedBase),(5127,b32 (3+warp.val)),
    (1230,fl (-abiFloat p.scaleLog2Bits)),(7132,b32 p.scaleLog2Bits),
    (7250,biasPhase),(7253,scorePhase),(7248,counter)]

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads) (warp : Fin 8)
    (hw : warp.val = warpIndex l g) {F : List (Nat × Value)}
    (input : OpeningTripCursor l X g (biasBodyStart true+4*biasBodyPairs true) F)
    (score : Nat → Option ℝ) (old : Option ℝ) (oldSum : ℝ) (nextBlock floor phase : Nat)
    (hPhase : phase < 2) (biasPhase scorePhase counter : Value)
    (hLogits : ∀ i ∈ biasBodyItems true,
      input.ready.regs i.result = some (.pair (scoreValue (score (2*(i.qk-7367))))
        (scoreValue (score (2*(i.qk-7367)+1)))))
    (hPrior : Holds input.ready.regs
      (biasedAffineInputFrame p l warp old oldSum nextBlock floor phase biasPhase scorePhase
        counter))
include hp hMax hg warp hw input score old oldSum nextBlock floor phase hPhase biasPhase scorePhase
    counter hLogits hPrior

/-- Actual biased logits progress through the rescale store and statistics arrival
to the live affine state of the same maximal trace. -/
theorem biasedAffineReachedOfMaximal :
    ∃ candidate, ∃ u : AffineCursor l X g (Repeated.biased.affineStart),
      let scale := abiFloat p.scaleLog2Bits
      let chosen := chosenReference scale old candidate
      let ref := chosen.map (scale * ·)
      (∀ v : EReal, scoreReal candidate ≤ v ↔
        scoreReal old ≤ v ∧ ∀ i < 128, scoreReal (score i) ≤ v) ∧
      StatisticsStore X (g,input.pos) (rescaleStore true) (statsAcc l g warp 0)
        (alphaWord scale old candidate).toBytes ∧
      Publishes X (g,input.pos+1) .biased ∧
      u.pos = input.pos+2 ∧ u.ending = input.ending ∧
      Nonempty (RepeatedProbabilityShiftFrame p l .biased g (stageOf warp) u.ready
        score (ref.getD 0)) ∧
      Nonempty (RepeatedTailOperands l .biased (stageOf warp) u.ready warp oldSum
        (maskedRescale (old.map (scale * ·)) ref) phase) ∧
      (u.ready.regs 7256 = some (scoreValue chosen) ∧ u.ready.regs 7250 = some biasPhase ∧
        u.ready.regs 7253 = some scorePhase ∧ u.ready.regs 7248 = some counter ∧
        u.ready.regs 7249 = some (b32 nextBlock)) := by
  let t := input.ready
  let scale := abiFloat p.scaleLog2Bits
  have hBits : p.scaleLog2Bits < 2^32 := (hp.values (12,p.scaleLog2Bits) (by
    simp [Params.scalarWords])).1
  have hScaleValue : valFloat .f32 (b32 p.scaleLog2Bits) = .ok scale := by
    obtain ⟨q,_,hq,_,_,_⟩ := hp.scales
    simpa only [scale,abiFloat,hq,Option.getD_some] using
      valFloat_b32 (by omega : p.scaleLog2Bits < 2^64) hq
  obtain ⟨hOld,hOldSum,hBlock,hFloor,hPoll,hWarp,hBase,hBar,hNegative,hScale,
    hBiasPhase,hScorePhase,hCounter,_⟩ := hPrior
  obtain ⟨alpha,candidate,hAt,hAlphaLocal,hCandidate,hAlphaFrame,hMixed⟩ :=
    biasedReferenceLocal (l := l) (g := g) score old nextBlock floor scale (scalePositive hp).1
      (b32 p.scaleLog2Bits) (readEReal_of_valFloat hScaleValue)
      (input.checkpoint.mono trivial) hLogits
      hOld hBlock hFloor hScale
  have hStatsAt : At alpha 5675 [(1062,b32 warp.val),(2535,b32 l.sharedBase),
      (5127,b32 (3+warp.val)),(1362,alphaWord scale old candidate)] :=
    hAt.mono ⟨(hAlphaFrame _ (by decide) (by decide +kernel) (by decide) (by decide)).trans hWarp,
      (hAlphaFrame _ (by decide) (by decide +kernel) (by decide) (by decide)).trans hBase,
      (hAlphaFrame _ (by decide) (by decide +kernel) (by decide) (by decide)).trans hBar,
      hAt.2.2.2.2.2.2.1,trivial⟩
  obtain ⟨preStats,hLocal,hPreStats⟩ :=
    (StatisticsAddressWindow.replay hp g warp hw .biased).apply
      (hStatsAt.mono ⟨hStatsAt.2.2.2.2.1,hStatsAt.2.2.2.2.2.1,trivial⟩)
  have hStatsFrame (r : Nat) (hr : r ∉ biasedStatsWritten) : preStats.regs r = alpha.regs r :=
    biasedStatsAddressFrame (by decide) hStatsAt.1 (by decide) hLocal r (.inl hr)
  have hStage := biasedStatsStage warp (hStatsAt.mono ⟨hStatsAt.2.2.2.2.1,trivial⟩) hLocal
  let word := alphaWord scale old candidate
  let facts := [(4571,b32 (statsBase l g warp)),(1362,word),(5127,b32 (3+warp.val))]
  have hStatsReady : At preStats 5682 facts :=
    hPreStats.mono ⟨hPreStats.2.2.2.2.1,
      (hStatsFrame _ (by decide)).trans hAt.2.2.2.2.2.2.1,
      (hStatsFrame _ (by decide)).trans hStatsAt.2.2.2.2.2.2.1,trivial⟩
  let c : OpeningTripCursor l X g 5682 facts :=
    ⟨input.pos,input.before,preStats,input.ending,input.positive,input.bounded,input.released,
      hStatsReady,input.recorded,input.remaining,
      input.localSteps.trans (hAlphaLocal.trans (run_rtg hLocal))⟩
  have hWidth : word.bytes = 4 := by
    unfold word alphaWord
    split <;> rfl
  obtain ⟨hStore,hNotice,hAfter,hPast,hTail⟩ :=
    rescalePublicationStateOfMaximal hp hMax hg warp hw .biased word hWidth c
      (.head _) (.tail _ (.head _)) (.tail _ (.tail _ (.head _)))
  let stats := next (next preStats)
  have hStats : At stats 5684 [] := hAfter.mono trivial
  let chosen := chosenReference scale old candidate
  let ref := chosen.map (scale * ·)
  have hRef : stats.regs 4565 = some (finiteRefValue chosen) :=
    (hStatsFrame _ (by decide)).trans hAt.2.2.2.2.2.1
  have hNeg : stats.regs 1230 = some (fl (-scale)) :=
    (hStatsFrame _ (by decide)).trans
      ((hAlphaFrame _ (by decide) (by decide +kernel) (by decide) (by decide)).trans hNegative)
  have hAbi : stats.regs 7132 = some (b32 p.scaleLog2Bits) :=
    (hStatsFrame _ (by decide)).trans
      ((hAlphaFrame _ (by decide) (by decide +kernel) (by decide) (by decide)).trans hScale)
  obtain ⟨shift,hShift,hShiftLocal,hsScale,hsOffset,hShiftFrame⟩ :=
    biasedShiftScaleLocal hp (g := g) chosen hStats hRef hNeg hAbi
  have hKeep (n : Nat) (hn : biasedShiftSetupSafe n = true) : shift.regs n = t.regs n := by
    simp only [biasedShiftSetupSafe,Bool.and_eq_true,bne_iff_ne,Bool.not_eq_true',
      List.contains_eq_mem,decide_eq_false_iff_not] at hn
    obtain ⟨⟨⟨⟨⟨h1,h2⟩,h3⟩,h4⟩,h5⟩,h6⟩ := hn
    exact (hShiftFrame n h6).trans ((hStatsFrame n h5).trans (hAlphaFrame n h1 h2 h3 h4))
  let values (n : Nat) := (shift.regs n).getD (.pred false)
  let scores (i : FmaItem) := (score (i.x-1363),score (i.y-1363))
  have hScores (i : FmaItem) (hi : i ∈ shiftItems 1) :
      i.pk = none ∧ shift.regs i.a = some (.pair (scoreValue (scores i).1)
        (scoreValue (scores i).2)) := by
    have h := biasedLogitsForShift score hLogits i hi
    exact ⟨h.1,(hKeep _ (List.all_eq_true.mp biasedShiftSourcesSafe i hi)).trans h.2⟩
  have hRegs (n : Nat) (hn : n ∈ biasedExpFrame) : ∃ v, shift.regs n = some v := by
    change n ∈ [1062,2535,637,1362,7257,7258] at hn
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_,(hKeep _ (by decide +kernel)).trans hWarp⟩
    · exact ⟨_,(hKeep _ (by decide +kernel)).trans hBase⟩
    · exact ⟨_,(hShiftFrame _ (by decide)).trans hStage⟩
    · exact ⟨_,(hShiftFrame _ (by decide)).trans
        ((hStatsFrame _ (by decide)).trans hAt.2.2.2.2.2.2.1)⟩
    · exact ⟨_,(hKeep _ (by decide +kernel)).trans hOldSum⟩
    · exact ⟨_,(hKeep _ (by decide +kernel)).trans hPoll⟩
  let mixed := compare .lt .u 32
    (truncBits 32 (BitVec.ofNat 64 nextBlock)) (truncBits 32 (BitVec.ofNat 64 floor))
  have hOffset : readERealPair l g shift (.reg 8444) =
      some (.ok (((-ref.getD 0 : ℝ) : EReal), ((-ref.getD 0 : ℝ) : EReal))) := by
    have hGet : ref.getD 0 = scale*chosen.getD 0 := by
      unfold ref
      cases chosen <;> simp
    rw [hGet]
    exact hsOffset
  have hChosen : shift.regs 7256 = some (scoreValue chosen) :=
    (hShiftFrame _ (by decide)).trans ((hStatsFrame _ (by decide)).trans hAt.2.2.2.2.1)
  have hValue (n : Nat) {v : Value} (hv : shift.regs n = some v) : values n = v := by
    simp [values,hv]
  have hBound : input.pos+2 ≤ (X.tr g).length := by
    obtain ⟨e,he,_⟩ := hNotice
    exact len_of_get he
  let u : AffineCursor l X g (Repeated.biased.affineStart) :=
    ⟨input.pos+2,stats,shift,input.ending,by omega,hBound,hShift,hPast,hTail,
      hShiftLocal⟩
  have hAlpha : shift.regs 1362 = some word :=
    (hShiftFrame _ (by decide)).trans ((hStatsFrame _ (by decide)).trans hAt.2.2.2.2.2.2.1)
  refine ⟨candidate,u,hCandidate,hStore,hNotice,rfl,rfl,⟨{
    mixed := mixed
    words := values
    inputs := scores
    atShift := hShift
    reads := ?_
    source := ?_
    columns := fun _ _ => ⟨rfl,rfl⟩
    scale := hsScale
    offset := hOffset
    frame := ?_
    mixChoice := fun _ =>
      (hShiftFrame _ (by decide)).trans ((hStatsFrame _ (by decide)).trans hMixed)
    biasedStage := fun _ => hValue _ ((hShiftFrame _ (by decide)).trans hStage)
    biasedBase := fun _ => hValue _ ((hKeep _ (by decide +kernel)).trans hBase)
    plainAddresses := fun h => by cases h
    plainSignal := fun h => by cases h }⟩,?_,?_⟩
  · intro i hi n hn
    have h := hScores i hi
    have hN : n = i.a := by simpa only [FmaItem.reads,h.1,List.mem_singleton] using hn
    subst n
    exact h.2.trans (congrArg some (hValue _ h.2).symm)
  · intro i hi
    have h := hScores i hi
    simp [FmaItem.packOk,FmaItem.src,h.1,values,h.2,splitValue]
  · intro n hn
    obtain ⟨v,hv⟩ := hRegs n hn
    rw [hValue n hv]
    exact hv
  · refine ⟨⟨rfl,⟨(hKeep _ (by decide +kernel)).trans hWarp,
      (hKeep _ (by decide +kernel)).trans hBase,trivial⟩,
      (hKeep _ (by decide +kernel)).trans hOldSum,word,hAlpha,
      alphaWord_valFloat scale old candidate,(hKeep _ (by decide +kernel)).trans hPoll,
      hPhase,?_⟩⟩
    intro n hn
    simp only [Repeated.continuationRegs,List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_,hChosen⟩
    · exact ⟨_,(hKeep _ (by decide +kernel)).trans hBiasPhase⟩
    · exact ⟨_,(hKeep _ (by decide +kernel)).trans hScorePhase⟩
    · exact ⟨_,(hKeep _ (by decide +kernel)).trans hCounter⟩
    · exact ⟨_,(hKeep _ (by decide +kernel)).trans hBlock⟩
  · exact ⟨hChosen,(hKeep _ (by decide +kernel)).trans hBiasPhase,
      (hKeep _ (by decide +kernel)).trans hScorePhase,(hKeep _ (by decide +kernel)).trans hCounter,
      (hKeep _ (by decide +kernel)).trans hBlock⟩

end

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads) (warp : Fin 8)
    (hw : warp.val = warpIndex l g) {F : List (Nat × Value)}
    (input : OpeningTripCursor l X g (biasBodyStart true) F) (bias : Nat → Option ℝ) (dot : Nat → ℝ)
    (old : Option ℝ) (oldSum : ℝ) (nextBlock floor phase : Nat) (hPhase : phase < 2)
    (biasPhase scorePhase counter : Value)
    (hScale : readERealPair l g input.ready (.reg 7896) =
      some (.ok ((abiFloat p.invScaleBits : EReal),(abiFloat p.invScaleBits : EReal))))
    (hUnpacked : ∀ i : Fin 16, BiasUnpacked true i input.ready (fun k =>
      biasLoadWord (bias (8*i.val+2*k)) (bias (8*i.val+2*k+1))))
    (hDots : ∀ pair < 64, readERealPair l g input.ready (.reg (7367+pair)) =
      some (.ok ((dot (2*pair) : EReal),(dot (2*pair+1) : EReal))))
    (hPrior : Holds input.ready.regs
      (biasedAffineInputFrame p l warp old oldSum nextBlock floor phase biasPhase scorePhase
        counter))
include hp hMax hg warp hw input bias dot old oldSum nextBlock floor phase hPhase biasPhase
    scorePhase counter hScale hUnpacked hDots hPrior

/-- Canonical physical Bias and QK operands at the returned rendezvous provide
every biased affine score. This replay covers padding rows as well. -/
theorem biasedAffineReachedOfInputsOfMaximal :
    ∃ candidate, ∃ u : AffineCursor l X g (Repeated.biased.affineStart),
      let score := fun col => affineScore (abiFloat p.invScaleBits) (dot col) (bias col)
      let scale := abiFloat p.scaleLog2Bits
      let chosen := chosenReference scale old candidate
      let ref := chosen.map (scale * ·)
      (∀ v : EReal, scoreReal candidate ≤ v ↔
        scoreReal old ≤ v ∧ ∀ i < 128, scoreReal (score i) ≤ v) ∧
      StatisticsStore X (g,input.pos) (rescaleStore true) (statsAcc l g warp 0)
        (alphaWord scale old candidate).toBytes ∧
      Publishes X (g,input.pos+1) .biased ∧
      u.pos = input.pos+2 ∧ u.ending = input.ending ∧
      Nonempty (RepeatedProbabilityShiftFrame p l .biased g (stageOf warp) u.ready
        score (ref.getD 0)) ∧
      Nonempty (RepeatedTailOperands l .biased (stageOf warp) u.ready warp oldSum
        (maskedRescale (old.map (scale * ·)) ref) phase) ∧
      (u.ready.regs 7256 = some (scoreValue chosen) ∧ u.ready.regs 7250 = some biasPhase ∧
        u.ready.regs 7253 = some scorePhase ∧ u.ready.regs 7248 = some counter ∧
        u.ready.regs 7249 = some (b32 nextBlock)) := by
  obtain ⟨v,hv,hLocal,hKeep,hScore⟩ :=
    laterBiasBodyOfCanonicalInputs hp bias dot (input.checkpoint.mono trivial) hScale
      hUnpacked hDots
  let prior := biasedAffineInputFrame p l warp old oldSum nextBlock floor phase biasPhase
    scorePhase counter
  have hPrior' : Holds v.regs prior := by
    apply Epilogue.holdsSchedulerFrame (regs := prior.map Prod.fst) hPrior
    · intro reg hr
      obtain ⟨pair,hp,rfl⟩ := List.mem_map.mp hr
      apply hKeep
      simp only [prior,biasedAffineInputFrame,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals dsimp only; decide +kernel
    · exact fun _ hm => List.mem_map_of_mem hm
  let c : OpeningTripCursor l X g (biasBodyStart true+4*biasBodyPairs true) [] :=
    ⟨input.pos,input.before,v,input.ending,input.positive,input.bounded,input.released,hv,
      input.recorded,input.remaining,input.localSteps.trans hLocal⟩
  exact biasedAffineReachedOfMaximal hp hMax hg warp hw c
    (fun col => affineScore (abiFloat p.invScaleBits) (dot col) (bias col)) old oldSum
    nextBlock floor phase hPhase biasPhase scorePhase counter hScore hPrior'

end PTX.Kernels.TmlFa4Fwd.Softmax
