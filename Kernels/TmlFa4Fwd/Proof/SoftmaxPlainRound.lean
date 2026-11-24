-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxPlainRescale
public import Kernels.TmlFa4Fwd.Proof.SoftmaxAffineRound

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Numeric Prologue

noncomputable section

private def plainShiftSetupSafe (n : Nat) : Bool :=
  !((rWrites (repeatedMaxItems false)).contains n) &&
    !([5510,645].contains n) && !((oWrites (alphaSite false).items).contains n) &&
    !(plainStatsWritten.contains n) && !([5519,8691].contains n)

private theorem plainShiftSourcesSafe :
    (shiftItems 2).all (fun i => plainShiftSetupSafe i.a) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

/-- Replay the plain maximum and correction publication to the actual affine shift. -/
private theorem plainAffineFromLogits {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (warp : Fin 8) {g j b h row blocks visit : Nat}
    (hw : warp.val = warpIndex l g) {t : TState}
    (old : Option ℝ) (oldSum : ℝ) (phase : Nat)
    (ht : At t (repeatedMaxStart false) [])
    (hPacked : ∀ (q : Fin 4) (k : Fin 16),
      let score := fun c => maskedLogit p b h row (visitKey blocks visit c)
      t.regs (repeatedScorePairReg .unbiased q k.val) =
        some (.pair (scoreValue (score (32*q.val+2*k.val)))
          (scoreValue (score (32*q.val+(2*k.val+1))))))
    (hPrior : Holds t.regs
      [(7255,scoreValue old),(7257,fl oldSum),(7258,b32 phase),
        (1062,b32 warp.val),(2535,b32 l.sharedBase),(5127,b32 (3+warp.val)),
        (5177,b32 (g%l.block)),(5176,b32 (128*(warp.val/4))),
        (1230,fl (-abiFloat p.scaleLog2Bits)),(7133,b32 p.scaleLog2Bits),
        (5187,b32 (l.sharedBase+8*(stageOf warp).val))])
    (hPaired : readERealPair l g t (.reg 8692) =
      some (.ok ((abiFloat p.scaleLog2Bits : EReal),(abiFloat p.scaleLog2Bits : EReal))))
    (hProbability : ∀ q : Fin 4, t.regs (probabilityReg .unbiased q) =
      some (b32 (probabilityAddress l g (stageOf warp) q)))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    let scale := abiFloat p.scaleLog2Bits
    ∃ candidate,
      let chosen := chosenReference scale old candidate
      (∀ v : EReal, scoreReal candidate ≤ v ↔ scoreReal old ≤ v ∧
        ∀ i < 128, scoreReal (maskedLogit p b h row (visitKey blocks visit i)) ≤ v) ∧
      X.get (g,j) = some ⟨6890,.wr (statsAcc l g warp 1)
        (alphaWord scale old candidate).toBytes⟩ ∧
      X.get (g,j+1) = some ⟨6891,.bar (3+warp.val) (some 64) .arrive⟩ ∧
      ∃ a : AffineRound p l X .unbiased warp g (j+2) b h row blocks visit old oldSum chosen
        phase t plainShiftSetupSafe,
        TraceReach kernel Assumptions.all l g t (((X.tr g).drop j).take 2) a.state := by
  let score := fun c => maskedLogit p b h row (visitKey blocks visit c)
  let scale := abiFloat p.scaleLog2Bits
  have hBits : p.scaleLog2Bits < 2^32 := (hp.values (12,p.scaleLog2Bits) (by
    simp [Params.scalarWords])).1
  have hScaleValue : valFloat .f32 (b32 p.scaleLog2Bits) = .ok scale := by
    obtain ⟨q,_,hq,_,_,_⟩ := hp.scales
    simpa only [scale,abiFloat,hq,Option.getD_some] using
      valFloat_b32 (by omega : p.scaleLog2Bits < 2^64) hq
  obtain ⟨hOld,hOldSum,hPoll,hWarp,hBase,hBar,hTid,hSelector,hNegative,hScale,hSignal,_⟩ := hPrior
  obtain ⟨alpha,candidate,hAt,hAlphaLocal,hCandidate,hAlphaFrame⟩ :=
    plainReferenceLocal (l := l) (g := g) score old scale (scalePositive hp).1 (b32 p.scaleLog2Bits)
      (readEReal_of_valFloat hScaleValue) ht hPacked hOld hScale
  have hStatsAt : At alpha 6886 [(5177,b32 (g%l.block)),(5176,b32 (128*(warp.val/4))),
      (2535,b32 l.sharedBase),(5127,b32 (3+warp.val)),(1492,alphaWord scale old candidate)] :=
    hAt.mono ⟨(hAlphaFrame _ (by decide +kernel) (by decide) (by decide)).trans hTid,
      (hAlphaFrame _ (by decide +kernel) (by decide) (by decide)).trans hSelector,
      (hAlphaFrame _ (by decide +kernel) (by decide) (by decide)).trans hBase,
      (hAlphaFrame _ (by decide +kernel) (by decide) (by decide)).trans hBar,
      hAt.2.2.2.2.2.2.1,trivial⟩
  obtain ⟨stats,hStats,hStore,hNotice,hStatsRun,hStatsFrame,hStatisticsPath⟩ :=
    plainRescalePublicationPathInPrefix hp warp hw hStatsAt
      (hRun.after_local hAlphaLocal) (.inl rfl)
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
  refine ⟨candidate,hCandidate,hStore,hNotice,{
    state := shift
    mixed := false
    words := vals
    scores := scores
    atShift := hShift
    reads := ?_
    source := ?_
    logits := fun _ _ => ⟨rfl,rfl⟩
    scale := hShiftScale
    offset := hOffset
    frame := ?_
    stage := ?_
    mode := ?_
    warpWord := hValue _ ((hKeep _ (by decide +kernel)).trans hWarp)
    base := hValue _ ((hKeep _ (by decide +kernel)).trans hBase)
    addresses := ?_
    signal := ?_
    oldMass := hValue _ ((hKeep _ (by decide +kernel)).trans hOldSum)
    alpha := ?_
    phaseWord := hValue _ ((hKeep _ (by decide +kernel)).trans hPoll)
    maximum := hChosen
    keeps := hKeep
    suffix := hStatsRun.after_local hShiftLocal },?_⟩
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
  · intro h; cases h
  · intro h; cases h
  · exact fun _ q => hValue _ (hP q)
  · exact fun _ => hValue _ ((hKeep _ (by decide +kernel)).trans hSignal)
  · change valFloat .f32 (vals 1492) = _
    rw [hValue _ hRescale]
    exact alphaWord_valFloat scale old candidate

  · have hPath := (TraceReach.of_local hAlphaLocal).append
      (hStatisticsPath.append (TraceReach.of_local hShiftLocal))
    simpa only [List.nil_append,List.append_nil] using hPath

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m) (warp : Fin 8)
    {g j b h row blocks visit : Nat} (hw : warp.val = warpIndex l g) {t : TState} (old : Option ℝ)
    (oldSum : ℝ) (phase scorePhase : Bool) (ht : At t (repeatedMaxStart false) [])
    (hPacked : ∀ (q : Fin 4) (k : Fin 16),
      let score := fun c => maskedLogit p b h row (visitKey blocks visit c)
      t.regs (repeatedScorePairReg .unbiased q k.val) =
        some (.pair (scoreValue (score (32*q.val+2*k.val)))
          (scoreValue (score (32*q.val+(2*k.val+1))))))
    (hPrior : Holds t.regs
      [(7255,scoreValue old),(7257,fl oldSum),(7258,b32 phase.toNat),
        (1062,b32 warp.val),(2535,b32 l.sharedBase),(5127,b32 (3+warp.val)),
        (5177,b32 (g%l.block)),(5176,b32 (128*(warp.val/4))),
        (1230,fl (-abiFloat p.scaleLog2Bits)),(7133,b32 p.scaleLog2Bits),
        (5187,b32 (l.sharedBase+8*(stageOf warp).val))])
    (hPaired : readERealPair l g t (.reg 8692) =
      some (.ok ((abiFloat p.scaleLog2Bits : EReal),(abiFloat p.scaleLog2Bits : EReal))))
    (hProbability : ∀ q : Fin 4, t.regs (probabilityReg .unbiased q) =
      some (b32 (probabilityAddress l g (stageOf warp) q))) (word : Nat) (hWord : word < 2^32)
    (hControl : Holds t.regs [(7253,b32 scorePhase.toNat),(7254,b32 word)])
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none)
include hp warp hw old oldSum phase scorePhase ht hPacked hPrior hPaired hProbability word hWord
    hControl hRun

/-- Execute the repeated iteration from its actual packed logits to its next head
or fallthrough, preserving the updated reference, mass, and barrier phases. -/
theorem plainRoundFromLogitsWithPath :
    let scale := abiFloat p.scaleLog2Bits
    ∃ candidate u endPos barInst,
      let chosen := chosenReference scale old candidate
      let ref := chosen.map (scale * ·)
      let weights := fun col => shiftedWeight p b h row (visitKey blocks visit col) (ref.getD 0)
      let events := Repeated.probabilityEvents .unbiased l g (stageOf warp) weights
      let mass := oldSum*maskedRescale (old.map (scale * ·)) ref +
        (2 : ℝ)^(-ref.getD 0)*maskedBlockSum (p.keyCount b row) blocks visit (weight p b h row)
      (∀ v : EReal, scoreReal candidate ≤ v ↔ scoreReal old ≤ v ∧
        ∀ i < 128, scoreReal (maskedLogit p b h row (visitKey blocks visit i)) ≤ v) ∧
      X.get (g,j) = some ⟨6890,.wr (statsAcc l g warp 1)
        (alphaWord scale old candidate).toBytes⟩ ∧
      X.get (g,j+1) = some ⟨6891,.bar (3+warp.val) (some 64) .arrive⟩ ∧
      (∀ k : Fin events.length, X.get (g,j+2+k.val) = events[k.val]?) ∧
      X.get (g,j+2+events.length+1) =
        some ⟨probabilityWaitPc (Repeated.round .unbiased) true+1,.warpBar (2^32-1) barInst⟩ ∧
      j+2+events.length < endPos ∧
      let loop := Repeated.loop .unbiased
      let site := scoreLoopSite loop
      let nextWord := (word+1)%2^32
      At u (if nextWord ≠ site.sentinel then site.head else site.increment+4)
        ([(site.word,b32 nextWord),(roundPriorMaxReg loop,scoreValue chosen),
          (7256,scoreValue chosen),(7257,fl mass),(7258,b32 (!phase).toNat)] ++
          tailPhaseWords true (!scorePhase) loop) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop endPos) none ∧
      TraceReach kernel Assumptions.all l g t (((X.tr g).drop j).take (endPos-j)) u ∧
      ((X.tr g).take endPos).countP earlyProbabilityMark =
        ((X.tr g).take j).countP earlyProbabilityMark + 1 := by
  obtain ⟨candidate,hCandidate,hStore,hNotice,a,hFirst⟩ :=
    plainAffineFromLogits hp warp hw old oldSum phase.toNat ht hPacked hPrior
      hPaired hProbability hRun
  let scale := abiFloat p.scaleLog2Bits
  let chosen := chosenReference scale old candidate
  let ref := chosen.map (scale * ·)
  let continued (n : Nat) := (a.state.regs n).getD (.pred false)
  have hChosen : a.state.regs 7256 = some (scoreValue chosen) := a.maximum
  have hCounter := (a.keeps 7254 (by decide +kernel)).trans hControl.2.1
  have hScore := (a.keeps 7253 (by decide +kernel)).trans hControl.1
  have hContinued (n : Nat) (hn : n ∈ Repeated.unbiased.continuationRegs) :
      a.state.regs n = some (continued n) := by
    simp only [Repeated.continuationRegs,List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl | rfl | rfl <;> simp [continued,hChosen,hScore,hCounter]
  obtain ⟨u,endPos,barInst,hEvents,hBar,hBefore,hEnd,hTail,hPath,hEarly,_⟩ :=
    repeatedNumericRoundPublishingPath
    hp .unbiased warp a.mixed oldSum (old.map (scale * ·)) ref chosen word hWord phase
    false scorePhase a.words a.scores a.atShift a.reads a.source a.logits a.scale a.offset
    a.frame a.stage a.mode a.base a.addresses a.signal a.warpWord a.oldMass a.alpha a.phaseWord
    continued hContinued (by simp [continued,hChosen])
    (by simp [continued,Repeated.loop,scoreLoopSite,hCounter])
    (by intro h; cases h)
    (by simp [continued,hScore]) a.suffix
  refine ⟨candidate,u,endPos,barInst,hCandidate,hStore,hNotice,hEvents,hBar,hBefore,hEnd,hTail,?_,
    ?_⟩
  · rw [show endPos-j = 2+(endPos-(j+2)) by omega,List.take_add,List.drop_drop]
    exact hFirst.append hPath
  · exact repeatedEarlyCountOfStatistics hStore hNotice rfl rfl (by omega) hEarly

end
end PTX.Kernels.TmlFa4Fwd.Softmax
