-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasedRescale
public import Kernels.TmlFa4Fwd.Proof.SoftmaxAffineRound

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Numeric Prologue

noncomputable section

private def biasedShiftSetupSafe (n : Nat) : Bool :=
  n != 634 && !((rWrites (repeatedMaxItems true)).contains n) &&
    !([4561,635].contains n) && !((oWrites (alphaSite true).items).contains n) &&
    !(biasedStatsWritten.contains n) && !([4572,8444,8445].contains n)

private theorem biasedShiftSourcesSafe :
    (shiftItems 1).all (fun i => biasedShiftSetupSafe i.a) = true := by
  set_option maxRecDepth 100000 in kernel_rfl

/-- Replay the biased maximum and correction publication to the actual affine shift. -/
private theorem biasedAffineFromLogits {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (warp : Fin 8) {g j b h row blocks visit : Nat}
    (hw : warp.val = warpIndex l g) {t : TState}
    (old : Option ℝ) (oldSum : ℝ) (nextBlock floor phase : Nat)
    (ht : At t (biasBodyStart true+4*biasBodyPairs true) [])
    (hLogits : ∀ i ∈ biasBodyItems true,
      let score := fun c => maskedLogit p b h row (visitKey blocks visit c)
      t.regs i.result = some (.pair (scoreValue (score (2*(i.qk-7367))))
        (scoreValue (score (2*(i.qk-7367)+1)))))
    (hPrior : Holds t.regs
      [(7251,scoreValue old),(7257,fl oldSum),(7249,b32 nextBlock),(1361,b32 floor),
        (7258,b32 phase),(1062,b32 warp.val),(2535,b32 l.sharedBase),(5127,b32 (3+warp.val)),
        (1230,fl (-abiFloat p.scaleLog2Bits)),(7132,b32 p.scaleLog2Bits)])
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    let scale := abiFloat p.scaleLog2Bits
    ∃ candidate,
      let chosen := chosenReference scale old candidate
      (∀ v : EReal, scoreReal candidate ≤ v ↔ scoreReal old ≤ v ∧
        ∀ i < 128, scoreReal (maskedLogit p b h row (visitKey blocks visit i)) ≤ v) ∧
      X.get (g,j) = some ⟨5682,.wr (statsAcc l g warp 0)
        (alphaWord scale old candidate).toBytes⟩ ∧
      X.get (g,j+1) = some ⟨5683,.bar (3+warp.val) (some 64) .arrive⟩ ∧
      ∃ a : AffineRound p l X .biased warp g (j+2) b h row blocks visit old oldSum chosen
        phase t biasedShiftSetupSafe,
        TraceReach kernel Assumptions.all l g t (((X.tr g).drop j).take 2) a.state := by
  let score := fun c => maskedLogit p b h row (visitKey blocks visit c)
  let scale := abiFloat p.scaleLog2Bits
  have hBits : p.scaleLog2Bits < 2^32 := (hp.values (12,p.scaleLog2Bits) (by
    simp [Params.scalarWords])).1
  have hScaleValue : valFloat .f32 (b32 p.scaleLog2Bits) = .ok scale := by
    obtain ⟨q,_,hq,_,_,_⟩ := hp.scales
    simpa only [scale,abiFloat,hq,Option.getD_some] using
      valFloat_b32 (by omega : p.scaleLog2Bits < 2^64) hq
  obtain ⟨hOld,hOldSum,hBlock,hFloor,hPoll,hWarp,hBase,hBar,hNegative,hScale,_⟩ := hPrior
  obtain ⟨alpha,candidate,hAt,hAlphaLocal,hCandidate,hAlphaFrame,hMixed⟩ :=
    biasedReferenceLocal (l := l) (g := g) score old nextBlock floor scale (scalePositive hp).1
      (b32 p.scaleLog2Bits) (readEReal_of_valFloat hScaleValue) ht hLogits
      hOld hBlock hFloor hScale
  have hStatsAt : At alpha 5675 [(1062,b32 warp.val),(2535,b32 l.sharedBase),
      (5127,b32 (3+warp.val)),(1362,alphaWord scale old candidate)] :=
    hAt.mono ⟨(hAlphaFrame _ (by decide) (by decide +kernel) (by decide) (by decide)).trans hWarp,
      (hAlphaFrame _ (by decide) (by decide +kernel) (by decide) (by decide)).trans hBase,
      (hAlphaFrame _ (by decide) (by decide +kernel) (by decide) (by decide)).trans hBar,
      hAt.2.2.2.2.2.2.1,trivial⟩
  obtain ⟨stats,hStats,hStore,hNotice,hStatsRun,hStage,hStatsFrame,hStatisticsPath⟩ :=
    biasedRescalePublicationPathInPrefix hp warp hw hStatsAt
      (hRun.after_local hAlphaLocal) (.inl rfl)
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
  refine ⟨candidate,hCandidate,hStore,hNotice,{
    state := shift
    mixed := mixed
    words := values
    scores := scores
    atShift := hShift
    reads := ?_
    source := ?_
    logits := fun _ _ => ⟨rfl,rfl⟩
    scale := hsScale
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
    simp [FmaItem.packOk,FmaItem.src,h.1,values,h.2,splitValue]
  · intro n hn
    obtain ⟨v,hv⟩ := hRegs n hn
    rw [hValue n hv]
    exact hv
  · exact fun _ => hValue _ ((hShiftFrame _ (by decide)).trans hStage)
  · exact fun _ => (hShiftFrame _ (by decide)).trans ((hStatsFrame _ (by decide)).trans hMixed)
  · intro h; cases h
  · intro h; cases h
  · change valFloat .f32 (values 1362) = _
    rw [hValue _ ((hShiftFrame _ (by decide)).trans
      ((hStatsFrame _ (by decide)).trans hAt.2.2.2.2.2.2.1))]
    exact alphaWord_valFloat scale old candidate

  · have hPath := (TraceReach.of_local hAlphaLocal).append
      (hStatisticsPath.append (TraceReach.of_local hShiftLocal))
    simpa only [List.nil_append,List.append_nil] using hPath

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m) (warp : Fin 8)
    {g j b h row blocks visit : Nat} (hw : warp.val = warpIndex l g) {t : TState} (old : Option ℝ)
    (oldSum : ℝ) (nextBlock floor : Nat) (phase biasPhase scorePhase : Bool)
    (ht : At t (biasBodyStart true+4*biasBodyPairs true) [])
    (hLogits : ∀ i ∈ biasBodyItems true,
      let score := fun c => maskedLogit p b h row (visitKey blocks visit c)
      t.regs i.result = some (.pair (scoreValue (score (2*(i.qk-7367))))
        (scoreValue (score (2*(i.qk-7367)+1)))))
    (hPrior : Holds t.regs
      [(7251,scoreValue old),(7257,fl oldSum),(7249,b32 nextBlock),(1361,b32 floor),
        (7258,b32 phase.toNat),(1062,b32 warp.val),(2535,b32 l.sharedBase),(5127,b32 (3+warp.val)),
        (1230,fl (-abiFloat p.scaleLog2Bits)),(7132,b32 p.scaleLog2Bits)]) (word : Nat)
    (hWord : word < 2^32)
    (hControl : Holds t.regs
      [(7250,b32 biasPhase.toNat),(7253,b32 scorePhase.toNat),(7248,b32 word)])
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none)
include hp warp hw old oldSum nextBlock floor phase biasPhase scorePhase ht hLogits hPrior word
    hWord hControl hRun

/-- Execute the repeated iteration from its actual packed logits to its next head
or fallthrough, preserving the updated reference, mass, and barrier phases. -/
theorem biasedRoundFromLogitsWithPath :
    let scale := abiFloat p.scaleLog2Bits
    ∃ candidate u endPos barInst,
      let chosen := chosenReference scale old candidate
      let ref := chosen.map (scale * ·)
      let weights := fun col => shiftedWeight p b h row (visitKey blocks visit col) (ref.getD 0)
      let events := Repeated.probabilityEvents .biased l g (stageOf warp) weights
      let mass := oldSum*maskedRescale (old.map (scale * ·)) ref +
        (2 : ℝ)^(-ref.getD 0)*maskedBlockSum (p.keyCount b row) blocks visit (weight p b h row)
      (∀ v : EReal, scoreReal candidate ≤ v ↔ scoreReal old ≤ v ∧
        ∀ i < 128, scoreReal (maskedLogit p b h row (visitKey blocks visit i)) ≤ v) ∧
      X.get (g,j) = some ⟨5682,.wr (statsAcc l g warp 0)
        (alphaWord scale old candidate).toBytes⟩ ∧
      X.get (g,j+1) = some ⟨5683,.bar (3+warp.val) (some 64) .arrive⟩ ∧
      (∀ k : Fin events.length, X.get (g,j+2+k.val) = events[k.val]?) ∧
      X.get (g,j+2+events.length+1) =
        some ⟨probabilityWaitPc (Repeated.round .biased) true+1,.warpBar (2^32-1) barInst⟩ ∧
      j+2+events.length < endPos ∧
      let loop := Repeated.loop .biased
      let site := scoreLoopSite loop
      let nextWord := (word+1)%2^32
      At u (if nextWord ≠ site.sentinel then site.head else site.increment+4)
        ([(site.word,b32 nextWord),(roundPriorMaxReg loop,scoreValue chosen),
          (7256,scoreValue chosen),(7257,fl mass),(7258,b32 (!phase).toNat)] ++
          tailPhaseWords (!biasPhase) (!scorePhase) loop) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop endPos) none ∧
      TraceReach kernel Assumptions.all l g t (((X.tr g).drop j).take (endPos-j)) u ∧
      ((X.tr g).take endPos).countP earlyProbabilityMark =
        ((X.tr g).take j).countP earlyProbabilityMark + 1 ∧
      u.regs 7249 = some (b32 nextBlock) := by
  obtain ⟨candidate,hCandidate,hStore,hNotice,a,hFirst⟩ :=
    biasedAffineFromLogits hp warp hw old oldSum nextBlock floor phase.toNat ht hLogits hPrior hRun
  let scale := abiFloat p.scaleLog2Bits
  let chosen := chosenReference scale old candidate
  let ref := chosen.map (scale * ·)
  let continued (n : Nat) := (a.state.regs n).getD (.pred false)
  have hChosen : a.state.regs 7256 = some (scoreValue chosen) := a.maximum
  have hCounter := (a.keeps 7248 (by decide +kernel)).trans hControl.2.2.1
  have hScore := (a.keeps 7253 (by decide +kernel)).trans hControl.2.1
  have hBias := (a.keeps 7250 (by decide +kernel)).trans hControl.1
  have hBlock := (a.keeps 7249 (by decide +kernel)).trans hPrior.2.2.1
  have hContinued (n : Nat) (hn : n ∈ Repeated.biased.continuationRegs) :
      a.state.regs n = some (continued n) := by
    simp only [Repeated.continuationRegs,List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl <;> simp [continued,hChosen,hBias,hScore,hCounter,
      hBlock]
  obtain ⟨u,endPos,barInst,hEvents,hBar,hBefore,hEnd,hTail,hPath,hEarly,hBlockOut⟩ :=
    repeatedNumericRoundPublishingPath
    hp .biased warp a.mixed oldSum (old.map (scale * ·)) ref chosen word hWord phase
    biasPhase scorePhase a.words a.scores a.atShift a.reads a.source a.logits a.scale a.offset
    a.frame a.stage a.mode a.base a.addresses a.signal a.warpWord a.oldMass a.alpha a.phaseWord
    continued hContinued (by simp [continued,hChosen])
    (by simp [continued,Repeated.loop,scoreLoopSite,hCounter])
    (fun _ => by simp [continued,hBias])
    (by simp [continued,hScore]) a.suffix
  refine ⟨candidate,u,endPos,barInst,hCandidate,hStore,hNotice,hEvents,hBar,hBefore,hEnd,hTail,?_,
    ?_,?_⟩
  · rw [show endPos-j = 2+(endPos-(j+2)) by omega,List.take_add,List.drop_drop]
    exact hFirst.append hPath
  · exact repeatedEarlyCountOfStatistics hStore hNotice rfl rfl (by omega) hEarly
  · simpa only [continued,hBlock,Option.getD_some] using hBlockOut rfl

end
end PTX.Kernels.TmlFa4Fwd.Softmax
