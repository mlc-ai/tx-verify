-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedStatisticsProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.AffineCursor
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedProbabilityDenominatorProgress
import all Kernels.TmlFa4Fwd.Proof.SoftmaxPlainRound
import all Kernels.TmlFa4Fwd.Proof.SoftmaxPlainRescale
public import Lemmas.Real.MaskedSoftmaxUpdate

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Numeric Prologue Correction Thread.Scores

/-- The scalar ABI and loop control that are live at the plain maximum entry. -/
noncomputable def plainAffineInputFrame (p : Params) (l : Launch) (g : Nat) (warp : Fin 8)
    (old : Option ℝ) (oldSum : ℝ) (phase : Nat) (scorePhase counter : Value) :
    List (Nat × Value) :=
  [(7255,scoreValue old),(7257,fl oldSum),(7258,b32 phase),
    (1062,b32 warp.val),(2535,b32 l.sharedBase),(5127,b32 (3+warp.val)),
    (5177,b32 (g%l.block)),(5176,b32 (128*(warp.val/4))),
    (1230,fl (-abiFloat p.scaleLog2Bits)),(7133,b32 p.scaleLog2Bits),
    (5187,b32 (l.sharedBase+8*(stageOf warp).val)),(7253,scorePhase),(7254,counter)]

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads) (warp : Fin 8)
    (hw : warp.val = warpIndex l g) {F : List (Nat × Value)}
    (input : OpeningTripCursor l X g (repeatedMaxStart false) F) (score : Nat → Option ℝ)
    (old : Option ℝ) (oldSum : ℝ) (phase : Nat) (hPhase : phase < 2) (scorePhase counter : Value)
    (hPacked : ∀ (q : Fin 4) (k : Fin 16),
      input.ready.regs (repeatedScorePairReg .unbiased q k.val) =
        some (.pair (scoreValue (score (32*q.val+2*k.val)))
          (scoreValue (score (32*q.val+(2*k.val+1))))))
    (hPrior : Holds input.ready.regs
      (plainAffineInputFrame p l g warp old oldSum phase scorePhase counter))
    (hPaired : readERealPair l g input.ready (.reg 8692) =
      some (.ok ((abiFloat p.scaleLog2Bits : EReal),(abiFloat p.scaleLog2Bits : EReal))))
include hp hMax hg warp hw input score old oldSum phase hPhase scorePhase counter hPacked hPrior
    hPaired

/-- Actual plain score packs progress to their affine state through the reachable
rescale store and statistics arrival, preserving the live repeated tail operands. -/
theorem plainAffineReachedOfMaximal
    (hProbability : ∀ q : Fin 4, input.ready.regs (probabilityReg .unbiased q) =
      some (b32 (probabilityAddress l g (stageOf warp) q))) :
    ∃ candidate, ∃ u : AffineCursor l X g (Repeated.unbiased.affineStart),
      let scale := abiFloat p.scaleLog2Bits
      let chosen := chosenReference scale old candidate
      let ref := chosen.map (scale * ·)
      (∀ v : EReal, scoreReal candidate ≤ v ↔
        scoreReal old ≤ v ∧ ∀ i < 128, scoreReal (score i) ≤ v) ∧
      StatisticsStore X (g,input.pos) (rescaleStore false) (statsAcc l g warp 1)
        (alphaWord scale old candidate).toBytes ∧
      Publishes X (g,input.pos+1) .plain ∧
      u.pos = input.pos+2 ∧ u.ending = input.ending ∧
      Nonempty (RepeatedProbabilityShiftFrame p l .unbiased g (stageOf warp) u.ready
        score (ref.getD 0)) ∧
      Nonempty (RepeatedTailOperands l .unbiased (stageOf warp) u.ready warp oldSum
        (maskedRescale (old.map (scale * ·)) ref) phase) ∧
      (u.ready.regs 7256 = some (scoreValue chosen) ∧ u.ready.regs 7253 = some scorePhase ∧
        u.ready.regs 7254 = some counter) := by
  let t := input.ready
  let scale := abiFloat p.scaleLog2Bits
  have hBits : p.scaleLog2Bits < 2^32 := (hp.values (12,p.scaleLog2Bits) (by
    simp [Params.scalarWords])).1
  have hScaleValue : valFloat .f32 (b32 p.scaleLog2Bits) = .ok scale := by
    obtain ⟨q,_,hq,_,_,_⟩ := hp.scales
    simpa only [scale,abiFloat,hq,Option.getD_some] using
      valFloat_b32 (by omega : p.scaleLog2Bits < 2^64) hq
  obtain ⟨hOld,hOldSum,hPoll,hWarp,hBase,hBar,hTid,hSelector,hNegative,hScale,hSignal,
    hScorePhase,hCounter,_⟩ := hPrior
  obtain ⟨alpha,candidate,hAt,hAlphaLocal,hCandidate,hAlphaFrame⟩ :=
    plainReferenceLocal (l := l) (g := g) score old scale (scalePositive hp).1 (b32 p.scaleLog2Bits)
      (readEReal_of_valFloat hScaleValue) (input.checkpoint.mono trivial) hPacked hOld hScale
  have hStatsAt : At alpha 6886 [(5177,b32 (g%l.block)),(5176,b32 (128*(warp.val/4))),
      (2535,b32 l.sharedBase),(5127,b32 (3+warp.val)),(1492,alphaWord scale old candidate)] :=
    hAt.mono ⟨(hAlphaFrame _ (by decide +kernel) (by decide) (by decide)).trans hTid,
      (hAlphaFrame _ (by decide +kernel) (by decide) (by decide)).trans hSelector,
      (hAlphaFrame _ (by decide +kernel) (by decide) (by decide)).trans hBase,
      (hAlphaFrame _ (by decide +kernel) (by decide) (by decide)).trans hBar,
      hAt.2.2.2.2.2.2.1,trivial⟩
  obtain ⟨preStats,hLocal,hPreStats⟩ :=
    (StatisticsAddressWindow.replay hp g warp hw .plain).apply
      (hStatsAt.mono ⟨hStatsAt.2.2.2.2.1,hStatsAt.2.2.2.2.2.1,
        hStatsAt.2.2.2.2.2.2.1,trivial⟩)
  have hStatsFrame := plainStatsFrame hStatsAt.1 hLocal
  let word := alphaWord scale old candidate
  let facts := [(5518,b32 (statsBase l g warp)),(1492,word),(5127,b32 (3+warp.val))]
  have hStatsReady : At preStats 6890 facts :=
    hPreStats.mono ⟨hPreStats.2.2.2.2.1,
      (hStatsFrame _ (by decide)).trans hAt.2.2.2.2.2.2.1,
      (hStatsFrame _ (by decide)).trans hStatsAt.2.2.2.2.2.2.2.1,trivial⟩
  let c : OpeningTripCursor l X g 6890 facts :=
    ⟨input.pos,input.before,preStats,input.ending,input.positive,input.bounded,input.released,
      hStatsReady,input.recorded,input.remaining,
      input.localSteps.trans (hAlphaLocal.trans (run_rtg hLocal))⟩
  have hWidth : word.bytes = 4 := by
    unfold word alphaWord
    split <;> rfl
  obtain ⟨hStore,hNotice,hAfter,hPast,hTail⟩ :=
    rescalePublicationStateOfMaximal hp hMax hg warp hw .unbiased word hWidth c
      (.head _) (.tail _ (.head _)) (.tail _ (.tail _ (.head _)))
  let stats := next (next preStats)
  have hStats : At stats 6892 [] := hAfter.mono trivial
  let chosen := chosenReference scale old candidate
  let ref := chosen.map (scale * ·)
  have hRef : stats.regs 5514 = some (finiteRefValue chosen) :=
    (hStatsFrame _ (by decide)).trans hAt.2.2.2.2.2.1
  have hNeg : stats.regs 1230 = some (fl (-scale)) :=
    (hStatsFrame _ (by decide)).trans
      ((hAlphaFrame _ (by decide +kernel) (by decide) (by decide)).trans hNegative)
  obtain ⟨shift,hShift,hShiftLocal,hsOffset,hShiftFrame⟩ :=
    plainShiftOffsetLocal (l := l) (g := g) chosen scale hStats hRef hNeg
  have hKeep (n : Nat) (hn : plainShiftSetupSafe n = true) : shift.regs n = t.regs n := by
    simp only [plainShiftSetupSafe,Bool.and_eq_true,Bool.not_eq_true',
      List.contains_eq_mem,decide_eq_false_iff_not] at hn
    obtain ⟨⟨⟨⟨h1,h2⟩,h3⟩,h4⟩,h5⟩ := hn
    exact (hShiftFrame n h5).trans ((hStatsFrame n h4).trans (hAlphaFrame n h1 h2 h3))
  let vals (n : Nat) := (shift.regs n).getD (.pred false)
  let scores (i : FmaItem) := (score (i.x-5520),score (i.y-5520))
  have hScores (i : FmaItem) (hi : i ∈ shiftItems 2) :
      i.pk = none ∧ shift.regs i.a = some (.pair (scoreValue (scores i).1)
        (scoreValue (scores i).2)) := by
    have h := plainLogitsForShift score hPacked i hi
    exact ⟨h.1,(hKeep _ (List.all_eq_true.mp plainShiftSourcesSafe i hi)).trans h.2⟩
  have hP (q : Fin 4) : shift.regs (probabilityReg .unbiased q) =
      some (b32 (probabilityAddress l g (stageOf warp) q)) := by
    exact (hKeep _ (by fin_cases q <;> decide +kernel)).trans (hProbability q)
  have hRescale : shift.regs 1492 = some (alphaWord scale old candidate) :=
    (hShiftFrame _ (by decide)).trans ((hStatsFrame _ (by decide)).trans hAt.2.2.2.2.2.2.1)
  have hRegs (n : Nat) (hn : n ∈ unbiasedExpFrame) : ∃ v, shift.regs n = some v := by
    change n ∈ [1062,2535,1492,7257,7258,5183,5185,5181,5184,5187] at hn
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_,(hKeep _ (by decide +kernel)).trans hWarp⟩
    · exact ⟨_,(hKeep _ (by decide +kernel)).trans hBase⟩
    · exact ⟨_,hRescale⟩
    · exact ⟨_,(hKeep _ (by decide +kernel)).trans hOldSum⟩
    · exact ⟨_,(hKeep _ (by decide +kernel)).trans hPoll⟩
    · exact ⟨_,hP 0⟩
    · exact ⟨_,hP 1⟩
    · exact ⟨_,hP 2⟩
    · exact ⟨_,hP 3⟩
    · exact ⟨_,(hKeep _ (by decide +kernel)).trans hSignal⟩
  have hOffset : readERealPair l g shift (.reg 8691) =
      some (.ok (((-ref.getD 0 : ℝ) : EReal), ((-ref.getD 0 : ℝ) : EReal))) := by
    have hGet : ref.getD 0 = scale*chosen.getD 0 := by
      unfold ref
      cases chosen <;> simp
    rw [hGet]
    exact hsOffset
  have hShiftScale : readERealPair l g shift (.reg 8692) =
      some (.ok ((scale : EReal),(scale : EReal))) := by
    unfold readERealPair
    rw [show readValue l g shift 64 (.reg 8692) = readValue l g t 64 (.reg 8692) by
      simp only [readValue,readReg,hKeep 8692 (by decide +kernel)]]
    exact hPaired
  have hChosen : shift.regs 7256 = some (scoreValue chosen) :=
    (hShiftFrame _ (by decide)).trans ((hStatsFrame _ (by decide)).trans hAt.2.2.2.2.1)
  have hValue (n : Nat) {v : Value} (hv : shift.regs n = some v) : vals n = v := by simp [vals,hv]
  have hBound : input.pos+2 ≤ (X.tr g).length := by
    obtain ⟨e,he,_⟩ := hNotice
    exact len_of_get he
  let u : AffineCursor l X g (Repeated.unbiased.affineStart) :=
    ⟨input.pos+2,stats,shift,input.ending,by omega,hBound,hShift,hPast,hTail,
      hShiftLocal⟩
  refine ⟨candidate,u,hCandidate,hStore,hNotice,rfl,rfl,⟨{
    mixed := false
    words := vals
    inputs := scores
    atShift := hShift
    reads := ?_
    source := ?_
    columns := fun _ _ => ⟨rfl,rfl⟩
    scale := hShiftScale
    offset := hOffset
    frame := ?_
    mixChoice := fun h => by cases h
    biasedStage := fun h => by cases h
    biasedBase := fun h => by cases h
    plainAddresses := fun _ q => hValue _ (hP q)
    plainSignal := fun _ => hValue _ ((hKeep _ (by decide +kernel)).trans hSignal) }⟩,?_,?_⟩
  · intro i hi n hn
    have h := hScores i hi
    have hN : n = i.a := by simpa only [FmaItem.reads,h.1,List.mem_singleton] using hn
    subst n
    exact h.2.trans (congrArg some (hValue _ h.2).symm)
  · intro i hi
    have h := hScores i hi
    simp [FmaItem.packOk,FmaItem.src,h.1,vals,h.2,splitValue]
  · intro n hn
    obtain ⟨v,hv⟩ := hRegs n hn
    rw [hValue n hv]
    exact hv
  · refine ⟨⟨rfl,⟨(hKeep _ (by decide +kernel)).trans hWarp,
      (hKeep _ (by decide +kernel)).trans hBase,trivial⟩,
      (hKeep _ (by decide +kernel)).trans hOldSum,word,hRescale,
      alphaWord_valFloat scale old candidate,(hKeep _ (by decide +kernel)).trans hPoll,
      hPhase,?_⟩⟩
    intro n hn
    simp only [Repeated.continuationRegs,List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl | rfl | rfl
    · exact ⟨_,hChosen⟩
    · exact ⟨_,(hKeep _ (by decide +kernel)).trans hScorePhase⟩
    · exact ⟨_,(hKeep _ (by decide +kernel)).trans hCounter⟩
  · exact ⟨hChosen,(hKeep _ (by decide +kernel)).trans hScorePhase,
      (hKeep _ (by decide +kernel)).trans hCounter⟩

end

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFootprint : OutputFootprint p X) {g : Nat}
    (hg : g < l.threads) (warp : Fin 8) (hw : warp.val = warpIndex l g) {F : List (Nat × Value)}
    {input : OpeningTripCursor l X g (scorePc .unbiased 0) F}
    (c : PackedScorePrefix l X g .unbiased (stageOf warp) 4 input) (old : Option ℝ) (oldSum : ℝ)
    (phase : Nat) (hPhase : phase < 2) (scorePhase counter : Value)
    (hPrior : Holds input.ready.regs
      (plainAffineInputFrame p l g warp old oldSum phase scorePhase counter))
    (hPaired : readERealPair l g input.ready (.reg 8692) =
      some (.ok ((abiFloat p.scaleLog2Bits : EReal),(abiFloat p.scaleLog2Bits : EReal))))
include hp hMax hFootprint hg warp hw c old oldSum phase hPhase scorePhase counter hPrior hPaired

/-- The actual returned plain score words supply the exponent operand frame,
while the live control and ABI facts pass through the four score packs unchanged. -/
theorem PackedScorePrefix.plainAffineReachedOfFootprint
    (hProbability : ∀ q : Fin 4, input.ready.regs (probabilityReg .unbiased q) =
      some (b32 (probabilityAddress l g (stageOf warp) q))) :
    ∃ scores : Nat → ℝ,
      ∃ candidate, ∃ u : AffineCursor l X g (Repeated.unbiased.affineStart),
        let scale := abiFloat p.scaleLog2Bits
        let chosen := chosenReference scale old candidate
        let ref := chosen.map (scale * ·)
        (∀ (q : Fin 4) (k : Fin 32), (c.words q)[k.val]? =
          some (.float .f32 (scores (32*q.val+k.val)))) ∧
        (∀ v : EReal, scoreReal candidate ≤ v ↔
          scoreReal old ≤ v ∧ ∀ i < 128, scoreReal (some (scores i)) ≤ v) ∧
        StatisticsStore X (g,c.cursor.pos) (rescaleStore false) (statsAcc l g warp 1)
          (alphaWord scale old candidate).toBytes ∧
        Publishes X (g,c.cursor.pos+1) .plain ∧
        u.pos = c.cursor.pos+2 ∧ u.ending = input.ending ∧
        Nonempty (RepeatedProbabilityShiftFrame p l .unbiased g (stageOf warp) u.ready
          (fun i => some (scores i)) (ref.getD 0)) ∧
        Nonempty (RepeatedTailOperands l .unbiased (stageOf warp) u.ready warp oldSum
          (maskedRescale (old.map (scale * ·)) ref) phase) ∧
        (u.ready.regs 7256 = some (scoreValue chosen) ∧ u.ready.regs 7253 = some scorePhase ∧
          u.ready.regs 7254 = some counter) := by
  obtain ⟨scores,hScores⟩ := c.scoreColumnsOfFootprint hp hMax.1 hFootprint
  have hPair (q : Fin 4) (k : Fin 16) : c.cursor.ready.regs
      (repeatedScorePairReg .unbiased q k.val) =
        some (.pair (scoreValue (some (scores (32*q.val+2*k.val))))
          (scoreValue (some (scores (32*q.val+(2*k.val+1)))))) := by
    have hk := k.isLt
    have h := c.packed q q.isLt k.val k.isLt
    have hLow := hScores q ⟨2*k.val,by omega⟩
    have hHigh := hScores q ⟨2*k.val+1,by omega⟩
    simp only [List.getD_eq_getElem?_getD,hLow,hHigh,Option.getD_some] at h
    exact h
  let kept := [7255,7257,7258,1062,2535,5127,5177,5176,1230,7133,5187,7253,7254,
    8692,5183,5185,5181,5184]
  have hKeep (n : Nat) (hn : n ∈ kept) : c.cursor.ready.regs n = input.ready.regs n := by
    apply c.preserved
    intro q _
    simp only [kept,List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      unfold RepeatedScorePreserved <;> fin_cases q <;> decide
  have hPrior' : Holds c.cursor.ready.regs
      (plainAffineInputFrame p l g warp old oldSum phase scorePhase counter) :=
    Epilogue.holdsSchedulerFrame (regs := kept) hPrior hKeep fun pair hp => by
      simp only [plainAffineInputFrame,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> decide
  have hPaired' : readERealPair l g c.cursor.ready (.reg 8692) =
      some (.ok ((abiFloat p.scaleLog2Bits : EReal),(abiFloat p.scaleLog2Bits : EReal))) := by
    unfold readERealPair
    rw [show readValue l g c.cursor.ready 64 (.reg 8692) =
        readValue l g input.ready 64 (.reg 8692) by
      simp only [readValue,readReg,hKeep 8692 (by decide)]]
    exact hPaired
  have hAddress (q : Fin 4) : c.cursor.ready.regs (probabilityReg .unbiased q) =
      some (b32 (probabilityAddress l g (stageOf warp) q)) :=
    (hKeep _ (by fin_cases q <;> decide)).trans (hProbability q)
  obtain ⟨candidate,u,hMaxBound,hStore,hNotice,hPos,hEnding,hFrame,hOperands,hCont⟩ :=
    plainAffineReachedOfMaximal hp hMax hg warp hw c.cursor (fun i => some (scores i))
      old oldSum phase
      hPhase scorePhase counter hPair hPrior' hPaired' hAddress
  exact ⟨scores,candidate,u,hScores,hMaxBound,hStore,hNotice,hPos,hEnding.trans c.ending,
    hFrame,hOperands,hCont⟩

end PTX.Kernels.TmlFa4Fwd.Softmax
