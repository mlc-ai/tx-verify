-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedSum
public import Kernels.TmlFa4Fwd.Proof.SoftmaxBiasReadyOrder

public import Kernels.TmlFa4Fwd.Proof.SoftmaxPublishTail
import Kernels.TmlFa4Fwd.Proof.SoftmaxWaits

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.Numeric

noncomputable section

namespace Repeated

def round : Repeated → Round
  | .biased => .biased
  | .unbiased => .unbiased

def correctionSite : Repeated → Fin 10
  | .biased => 6
  | .unbiased => 8

def tailSignal : Repeated → Fin 8
  | .biased => 5
  | .unbiased => 7

private def offsetReg : Repeated → Nat
  | .biased => 5120
  | .unbiased => 5803

end Repeated

private def AckStage (r : Repeated) (l : Launch) (g : Nat) (warp : Fin 8)
    (values : Nat → Value) (keep : Bool) : Prop :=
  let joinPC := (signalSite r.tailSignal).pc + 1
  Seg kernel Assumptions.all l g 3 joinPC (tailCarryWith l warp r.round (some values) keep)
    (joinPC + 3) ((r.offsetReg, b32 (8 * (stageOf warp).val)) ::
      tailCarryWith l warp r.round (some values) keep)

private theorem biasedAckStageFalse (l : Launch) (g : Nat) (warp : Fin 8)
    (values : Nat → Value) : AckStage .biased l g warp values false := by
  unfold AckStage
  dsimp only
  fin_cases warp <;> intro t ht <;>
    simp only [Repeated.round, Repeated.tailSignal, Repeated.offsetReg, signalSite,
      tailCarryWith, tailLiveWith, Bool.false_eq_true, ↓reduceIte]
      at ht ⊢ <;>
    seg_fp ht using decide

private theorem biasedAckStageTrue (l : Launch) (g : Nat) (warp : Fin 8)
    (values : Nat → Value) : AckStage .biased l g warp values true := by
  unfold AckStage
  dsimp only
  fin_cases warp <;> intro t ht <;>
    simp only [Repeated.round, Repeated.tailSignal, Repeated.offsetReg, signalSite,
      tailCarryWith, tailLiveWith, tailContinuationRegs, Repeated.continuationRegs, ↓reduceIte]
      at ht ⊢ <;>
    seg_fp ht using decide

private theorem unbiasedAckStageFalse (l : Launch) (g : Nat) (warp : Fin 8)
    (values : Nat → Value) : AckStage .unbiased l g warp values false := by
  unfold AckStage
  dsimp only
  fin_cases warp <;> intro t ht <;>
    simp only [Repeated.round, Repeated.tailSignal, Repeated.offsetReg, signalSite,
      tailCarryWith, tailLiveWith, Bool.false_eq_true, ↓reduceIte]
      at ht ⊢ <;>
    seg_fp ht using decide

private theorem unbiasedAckStageTrue (l : Launch) (g : Nat) (warp : Fin 8)
    (values : Nat → Value) : AckStage .unbiased l g warp values true := by
  unfold AckStage
  dsimp only
  fin_cases warp <;> intro t ht <;>
    simp only [Repeated.round, Repeated.tailSignal, Repeated.offsetReg, signalSite,
      tailCarryWith, tailLiveWith, tailContinuationRegs, Repeated.continuationRegs, ↓reduceIte]
      at ht ⊢ <;>
    seg_fp ht using decide

private theorem ackStage (r : Repeated) (l : Launch) (g : Nat) (warp : Fin 8)
    (values : Nat → Value) (keep : Bool) : AckStage r l g warp values keep :=
  match r, keep with
  | .biased, false => biasedAckStageFalse l g warp values
  | .biased, true => biasedAckStageTrue l g warp values
  | .unbiased, false => unbiasedAckStageFalse l g warp values
  | .unbiased, true => unbiasedAckStageTrue l g warp values

private def ackFacts (r : Repeated) (l : Launch) (warp : Fin 8) (offset : Nat)
    (values : Nat → Value) (keep : Bool) : List (Nat × Value) :=
  ((waitSite r.correctionSite).base, b32 (l.sharedBase + (192 + offset))) ::
    tailCarryWith l warp r.round (some values) keep

private theorem ackAddress {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (r : Repeated) (g : Nat) (warp : Fin 8) (offset : Nat) (ho : offset ≤ 8)
    (values : Nat → Value) (keep : Bool) :
    Seg kernel Assumptions.all l g 2 ((signalSite r.tailSignal).pc + 1 + 3)
      ((r.offsetReg, b32 offset) :: tailCarryWith l warp r.round (some values) keep)
      (waitSite r.correctionSite).pc (ackFacts r l warp offset values keep) := by
  have hShared := hp.shared.2.1
  have hBase : l.sharedBase < 2 ^ 32 := by omega
  have hOff : offset < 2 ^ 32 := by omega
  have hSum : l.sharedBase + offset < 2 ^ 32 := by omega
  have hTotal : l.sharedBase + offset + 192 < 2 ^ 32 := by omega
  have hAddress :
      Value.bits 32
        (truncBits 32
          (truncBits 32 (truncBits 32 (truncBits 32 (BitVec.ofNat 64 l.sharedBase) +
            truncBits 32 (BitVec.ofNat 64 offset))) + truncBits 32 (BitVec.ofInt 64 192))) =
        b32 (l.sharedBase + (192 + offset)) := by
    rw [show BitVec.ofInt 64 192 = BitVec.ofNat 64 192 by decide,
      truncBits_ofNat hBase (by decide), truncBits_ofNat hOff (by decide),
      truncBits_ofNat (n := 192) (by decide) (by decide), ← BitVec.ofNat_add,
      truncBits_ofNat hSum (by decide), truncBits_ofNat hSum (by decide), ← BitVec.ofNat_add,
      truncBits_ofNat hTotal (by decide), show l.sharedBase + offset + 192 =
        l.sharedBase + (192 + offset) by omega]
    rfl
  cases r <;> cases keep <;> intro t ht <;>
    simp only [Repeated.round, Repeated.tailSignal, Repeated.offsetReg, Repeated.correctionSite,
      signalSite, waitSite, ackFacts, tailCarryWith, tailLiveWith,
      tailContinuationRegs, Repeated.continuationRegs,
      Bool.false_eq_true, ↓reduceIte] at ht ⊢ <;>
    seg_fp ht using exact hAddress

private theorem phaseLive (r : Repeated) (keep : Bool) :
    7258 ∈ tailLiveWith r.round keep := by
  cases r <;> cases keep <;> decide +kernel

set_option maxRecDepth 100000 in
private theorem ackFresh (r : Repeated) (keep : Bool) :
    (tailLiveWith r.round keep).all (fun n => n != (waitSite r.correctionSite).result) = true := by
  cases r <;> cases keep <;> kernel_rfl

private theorem ackFactsFresh {l : Launch} {warp : Fin 8} {offset : Nat} {keep : Bool}
    {values : Nat → Value} (r : Repeated) (x : Nat × Value)
    (hx : x ∈ ackFacts r l warp offset values keep) : x.1 ≠ (waitSite r.correctionSite).result := by
  simp only [ackFacts, List.mem_cons] at hx
  rcases hx with rfl | hx
  · change (waitSite r.correctionSite).base ≠ (waitSite r.correctionSite).result
    cases r <;> decide
  · rcases tailCarryWith_member hx with h | h | h
    · rw [h]
      cases r <;> decide
    · rw [h]
      cases r <;> decide
    · simpa only [bne_iff_ne] using List.all_eq_true.mp (ackFresh r keep) x.1 h

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m) (r : Repeated)
    (warp : Fin 8) (phase : Nat) (hpPhase : phase < 2) {g j : Nat} {t : TState}
    (values : Nat → Value)
include hp r warp phase hpPhase values

/-- Both repeated correction acknowledgements use the preserved phase and keep every
probability weight through all failed polls and the one successful poll. -/
theorem repeatedAcknowledgementPath (hPhase : values 7258 = b32 phase) (keep : Bool)
    (ht : At t ((signalSite r.tailSignal).pc + 1) (tailCarryWith l warp r.round (some values) keep))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    let i := r.correctionSite
    let pc := (waitSite i).pc
    let loc := waitLoc l g (stageOf warp) i
    ∃ failed u, (X.tr g).drop j =
      List.replicate failed ⟨pc, .wait loc phase false true .cta⟩ ++
        ⟨pc, .wait loc phase true true .cta⟩ :: (X.tr g).drop (j + failed + 1) ∧
      At u r.sumStart (tailCarryWith l warp r.round (some values) keep) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j + failed + 1)) none ∧
      TraceReach kernel Assumptions.all l g t (((X.tr g).drop j).take (failed+1)) u := by
  have hS := (stageOf warp).isLt
  let offset := 8 * (stageOf warp).val
  have hLocal := Seg.comp (ackStage r l g warp values keep)
    (ackAddress hp r g warp offset (by omega) values keep)
  obtain ⟨v, hv, hV⟩ := hLocal.rtg ht
  have hBase : ((waitSite r.correctionSite).base,
      b32 (waitLoc l g (stageOf warp) r.correctionSite).addr) ∈
        ackFacts r l warp offset values keep := by
    cases r <;> exact List.Mem.head _
  have hReg : (waitSite r.correctionSite).phase = 7258 := by cases r <;> rfl
  have hPar : ((waitSite r.correctionSite).phase, b32 phase) ∈
      ackFacts r l warp offset values keep := by
    rw [hReg, ← hPhase]
    exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (mem_factsFrom (phaseLive r keep))))
  obtain ⟨failed, u, hPolls, hU, hTail,hPath⟩ :=
    waitTraceAtWithPath hp (stageOf warp) r.correctionSite g phase hpPhase hBase hPar
      (ackFactsFresh r)
      hV (hRun.after_local hv)
  have hPc : (waitSite r.correctionSite).pc + 3 = r.sumStart := by cases r <;> rfl
  refine ⟨failed,u,hPolls,hPc ▸ hU.mono hU.2.2.2.2.2,hTail,?_⟩
  exact (TraceReach.of_local hv).append hPath

/-- The actual completed P tail reaches the row sum after correction acknowledges the stage. -/
theorem repeatedTailAcknowledgedWithPath (keep : Bool) (hPhase : values 7258 = b32 phase)
    (ht : At t (probabilityWaitPc r.round true) (tailCarryWith l warp r.round (some values) keep))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    let pc := probabilityWaitPc r.round true
    let i := r.correctionSite
    let loc := waitLoc l g (stageOf warp) i
    ∃ u barInst electInst leader failed,
      let jAck := if laneOf l g = leader then j + 4 else j + 3
      X.get (g, j) = some ⟨pc, .tc .waitSt⟩ ∧
      X.get (g, j + 1) = some ⟨pc + 1, .warpBar (2 ^ 32 - 1) barInst⟩ ∧
      X.get (g, j + 2) = some ⟨pc + 2, .elect (2 ^ 32 - 1) electInst leader⟩ ∧
      (laneOf l g = leader → X.get (g, j + 3) = some
        ⟨(signalSite r.tailSignal).pc, .arrive (signalLoc l g (stageOf warp) r.tailSignal)
          0 1 true .cta⟩) ∧
      (X.tr g).drop jAck =
        List.replicate failed ⟨(waitSite i).pc, .wait loc phase false true .cta⟩ ++
        ⟨(waitSite i).pc, .wait loc phase true true .cta⟩ ::
          (X.tr g).drop (jAck + failed + 1) ∧
      At u r.sumStart (tailCarryWith l warp r.round (some values) keep) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (jAck + failed + 1)) none ∧
      TraceReach kernel Assumptions.all l g t (((X.tr g).drop j).take (jAck+failed+1-j)) u := by
  obtain ⟨v,bar,elect,leader,hWait,hBar,hElect,hSignal,hV,hRest,hFirst⟩ :=
    tailPublicationPath hp r.round warp (some values) keep ht hRun
  have hV' : At v ((signalSite r.tailSignal).pc + 1)
      (tailCarryWith l warp r.round (some values) keep) := by cases r <;> exact hV
  obtain ⟨failed,u,hPolls,hU,hTail,hPath⟩ :=
    repeatedAcknowledgementPath hp r warp phase hpPhase values hPhase keep hV' hRest
  refine ⟨u,bar,elect,leader,failed,hWait,hBar,hElect,(by cases r <;> exact hSignal),
    (by simpa only [Nat.add_assoc] using hPolls),hU,(by simpa only [Nat.add_assoc] using hTail),?_⟩
  by_cases hLeader : laneOf l g = leader
  · simp only [ite_eq_left hLeader] at hFirst hPath ⊢
    rw [show j+4+failed+1-j = 4+(failed+1) by omega,List.take_add,List.drop_drop]
    exact hFirst.append hPath
  · simp only [ite_eq_right hLeader] at hFirst hPath ⊢
    rw [show j+3+failed+1-j = 3+(failed+1) by omega,List.take_add,List.drop_drop]
    exact hFirst.append hPath

end

private def sumValues (r : Repeated) (weights : Nat → ℝ) (old : ℝ) (word : Value)
    (phase : Nat) (n : Nat) : Value :=
  if n = 7257 then fl old else
  if n = r.alphaReg then word else
  if n = 7258 then b32 phase else
  if n ∈ r.scalarInputs then
    fl (weights (2 * r.packedInputs.length + r.scalarInputs.idxOf n))
  else
    .pair (fl (weights (2 * r.packedInputs.idxOf n)))
      (fl (weights (2 * r.packedInputs.idxOf n + 1)))

set_option maxRecDepth 100000 in
private theorem scalarFrameSafe (r : Repeated) :
    r.scalarInputs.all (fun n => n != 7257 && n != r.alphaReg && n != 7258) = true := by
  cases r <;> kernel_rfl

set_option maxRecDepth 100000 in
private theorem packedFrameSafe (r : Repeated) :
    r.packedInputs.all (fun n =>
      n != 7257 && n != r.alphaReg && n != 7258 && !(r.scalarInputs.contains n)) = true := by
  cases r <;> kernel_rfl

private theorem sumValuesScalar (r : Repeated) (weights : Nat → ℝ) (old : ℝ) (word : Value)
    (phase : Nat) {n : Nat} (hn : n ∈ r.scalarInputs) :
    sumValues r weights old word phase n =
      fl (weights (2 * r.packedInputs.length + r.scalarInputs.idxOf n)) := by
  have hc := List.all_eq_true.mp (scalarFrameSafe r) n hn
  simp only [Bool.and_eq_true, bne_iff_ne] at hc
  simp only [sumValues, ite_eq_right hc.1.1, ite_eq_right hc.1.2, ite_eq_right hc.2, ite_eq_left hn]

private theorem sumValuesPacked (r : Repeated) (weights : Nat → ℝ) (old : ℝ) (word : Value)
    (phase : Nat) {n : Nat} (hn : n ∈ r.packedInputs) :
    sumValues r weights old word phase n =
      .pair (fl (weights (2 * r.packedInputs.idxOf n)))
        (fl (weights (2 * r.packedInputs.idxOf n + 1))) := by
  have hc := List.all_eq_true.mp (packedFrameSafe r) n hn
  simp only [Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at hc
  simp only [sumValues, ite_eq_right hc.1.1.1, ite_eq_right hc.1.1.2,
    ite_eq_right hc.1.2, ite_eq_right hc.2]

private theorem sumValuesAlpha (r : Repeated) (weights : Nat → ℝ) (old : ℝ) (word : Value)
    (phase : Nat) : sumValues r weights old word phase r.alphaReg = word := by
  have hn : r.alphaReg ≠ 7257 := by cases r <;> decide
  simp [sumValues, hn]

private theorem sumValuesPhase (r : Repeated) (weights : Nat → ℝ) (old : ℝ) (word : Value)
    (phase : Nat) : sumValues r weights old word phase 7258 = b32 phase := by
  have hn : 7258 ≠ r.alphaReg := by cases r <;> decide
  simp [sumValues, hn]

private theorem roundLive_eq (r : Repeated) : tailLive r.round = r.sumLive := by cases r <;> rfl

private theorem sumValuesHold {r : Repeated} {t : TState} {weights : Nat → ℝ}
    {old : ℝ} {word : Value} {phase : Nat} (hWeights : RepeatedWeights r t weights)
    (hOld : t.regs 7257 = some (fl old)) (hAlpha : t.regs r.alphaReg = some (word))
    (hPhase : t.regs 7258 = some (b32 phase)) :
    Holds t.regs (factsFrom (tailLive r.round) (sumValues r weights old word phase)) := by
  apply holds_of_pointwise
  intro n hn
  rw [roundLive_eq] at hn
  simp only [Repeated.sumLive, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with (h | h) | rfl | rfl | rfl
  · rw [sumValuesScalar r _ _ _ _ h]
    exact hWeights.scalar n h
  · rw [sumValuesPacked r _ _ _ _ h]
    exact hWeights.packed n h
  · simpa only [sumValuesAlpha] using hAlpha
  · exact hOld
  · simpa only [sumValuesPhase] using hPhase

private theorem readSumValues {r : Repeated} {t : TState} {weights : Nat → ℝ}
    {old : ℝ} {word : Value} {phase : Nat}
    (h : Holds t.regs (factsFrom (tailLive r.round) (sumValues r weights old word phase))) :
    RepeatedWeights r t weights ∧ t.regs 7257 = some (fl old) ∧
      t.regs r.alphaReg = some (word) := by
  have hr (n : Nat) (hn : n ∈ r.sumLive) :
      t.regs n = some (sumValues r weights old word phase n) :=
    holds_mem h (mem_factsFrom (roundLive_eq r ▸ hn))
  have ho : 7257 ∈ r.sumLive := by simp [Repeated.sumLive]
  have ha : r.alphaReg ∈ r.sumLive := by simp [Repeated.sumLive]
  refine ⟨⟨?_, ?_⟩, hr 7257 ho, (hr _ ha).trans (congrArg some (sumValuesAlpha r _ _ _ _))⟩
  · intro n hn
    exact (hr _ (by simp [Repeated.sumLive, hn])).trans
      (congrArg some (sumValuesScalar r _ _ _ _ hn))
  · intro n hn
    exact (hr _ (by simp [Repeated.sumLive, hn])).trans
      (congrArg some (sumValuesPacked r _ _ _ _ hn))

set_option maxRecDepth 100000 in
private theorem continuationDisjoint (r : Repeated) :
    r.continuationRegs.all (fun n => !((tailLive r.round).contains n)) = true := by
  cases r <;> kernel_rfl

private theorem continuationFresh (r : Repeated) {n : Nat} (hn : n ∈ tailLive r.round) :
    n ∉ r.continuationRegs := by
  intro h
  have hc := List.all_eq_true.mp (continuationDisjoint r) n h
  simp only [List.contains_eq_mem, decide_eq_true hn, Bool.not_true, Bool.false_eq_true] at hc

private theorem tailEarlyCount {l : Launch} {X : Execution} (r : Repeated) {g j : Nat}
    {bar elect leader failed phase : Nat} {warp : Fin 8}
    (hWait : X.get (g,j) = some ⟨probabilityWaitPc r.round true,.tc .waitSt⟩)
    (hBar : X.get (g,j+1) =
      some ⟨probabilityWaitPc r.round true+1,.warpBar (2^32-1) bar⟩)
    (hElect : X.get (g,j+2) =
      some ⟨probabilityWaitPc r.round true+2,.elect (2^32-1) elect leader⟩)
    (hSignal : laneOf l g = leader → X.get (g,j+3) =
      some ⟨(signalSite r.tailSignal).pc,
        .arrive (signalLoc l g (stageOf warp) r.tailSignal) 0 1 true .cta⟩)
    (hPolls : let n := if laneOf l g = leader then 4 else 3
      let loc := waitLoc l g (stageOf warp) r.correctionSite
      let pc := (waitSite r.correctionSite).pc
      (X.tr g).drop (j+n) = List.replicate failed ⟨pc,.wait loc phase false true .cta⟩ ++
        ⟨pc,.wait loc phase true true .cta⟩ :: (X.tr g).drop (j+n+failed+1)) :
    let n := if laneOf l g = leader then 4 else 3
    (((X.tr g).drop j).take (j+n+failed+1-j)).countP earlyProbabilityMark = 0 := by
  let n := if laneOf l g = leader then 4 else 3
  let loc := waitLoc l g (stageOf warp) r.correctionSite
  let pc := (waitSite r.correctionSite).pc
  change (X.tr g).drop (j+n) = List.replicate failed ⟨pc,.wait loc phase false true .cta⟩ ++
    ⟨pc,.wait loc phase true true .cta⟩ :: (X.tr g).drop (j+n+failed+1) at hPolls
  change (((X.tr g).drop j).take (j+n+failed+1-j)).countP earlyProbabilityMark = 0
  have hPrefix : (((X.tr g).drop j).take n).countP earlyProbabilityMark = 0 := by
    apply List.countP_eq_zero.mpr
    intro e he
    obtain ⟨k,hGet⟩ := List.mem_iff_getElem?.mp he
    have hk := (List.getElem?_eq_some_iff.mp hGet).1
    simp only [List.length_take] at hk
    have hIndex : k < n := by omega
    rw [List.getElem?_take_of_lt hIndex,List.getElem?_drop] at hGet
    change X.get (g,j+k) = some e at hGet
    by_cases hLeader : laneOf l g = leader
    · rw [show n = 4 from ite_eq_left hLeader] at hIndex
      interval_cases k
      · obtain rfl := Option.some.inj (hWait.symm.trans hGet)
        cases r <;> exact Bool.false_ne_true
      · obtain rfl := Option.some.inj (hBar.symm.trans hGet)
        cases r <;> exact Bool.false_ne_true
      · obtain rfl := Option.some.inj (hElect.symm.trans hGet)
        cases r <;> exact Bool.false_ne_true
      · obtain rfl := Option.some.inj ((hSignal hLeader).symm.trans hGet)
        cases r <;> exact Bool.false_ne_true
    · rw [show n = 3 from ite_eq_right hLeader] at hIndex
      interval_cases k
      · obtain rfl := Option.some.inj (hWait.symm.trans hGet)
        cases r <;> exact Bool.false_ne_true
      · obtain rfl := Option.some.inj (hBar.symm.trans hGet)
        cases r <;> exact Bool.false_ne_true
      · obtain rfl := Option.some.inj (hElect.symm.trans hGet)
        cases r <;> exact Bool.false_ne_true
  let polls : List Event := List.replicate failed ⟨pc,.wait loc phase false true .cta⟩ ++
    [⟨pc,.wait loc phase true true .cta⟩]
  have hPollTrace : (X.tr g).drop (j+n) = polls ++ (X.tr g).drop (j+n+failed+1) := by
    simpa only [polls,List.append_assoc,List.singleton_append] using hPolls
  have hLength : failed+1 = polls.length := by simp [polls]
  rw [show j+n+failed+1-j = n+(failed+1) by omega,List.take_add,List.drop_drop,
    List.countP_append,hPrefix,hPollTrace,hLength,List.take_left]
  change 0 + polls.countP earlyProbabilityMark = 0
  have hFalse : earlyProbabilityMark ⟨pc,.wait loc phase false true .cta⟩ = false := by
    cases r <;> rfl
  have hTrue : earlyProbabilityMark ⟨pc,.wait loc phase true true .cta⟩ = false := by
    cases r <;> rfl
  simp [polls,List.countP_replicate,hFalse,hTrue]

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m) (r : Repeated)
    (warp : Fin 8) (phase : Nat) (hpPhase : phase < 2) {g j : Nat} {t : TState} (weights : Nat → ℝ)
    (old : ℝ) (ht : At t (probabilityWaitPc r.round true) (tailFrame l warp))
    (hWeights : RepeatedWeights r t weights) (hOld : t.regs 7257 = some (fl old)) {word : Value}
    (hAlpha : t.regs r.alphaReg = some word) (hPhase : t.regs 7258 = some (b32 phase))
    (continued : Nat → Value) (hContinued : ∀ n ∈ r.continuationRegs, t.regs n = some (continued n))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none)
include hp r warp phase hpPhase weights old ht hWeights hOld hAlpha hPhase continued hContinued hRun

/-- The row-sum inputs still carry the chosen maximum and loop registers after the
actual tail publication and correction acknowledgement. -/
theorem repeatedTailSumEntryWithPath :
    ∃ u endPos barInst, j < endPos ∧
      X.get (g,j+1) = some ⟨probabilityWaitPc r.round true+1,.warpBar (2^32-1) barInst⟩ ∧
      At u r.sumStart [] ∧
      RepeatedWeights r u weights ∧ u.regs 7257 = some (fl old) ∧
      u.regs r.alphaReg = some word ∧ u.regs 7258 = some (b32 phase) ∧
      (∀ n ∈ r.continuationRegs, u.regs n = some (continued n)) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop endPos) none ∧
      TraceReach kernel Assumptions.all l g t (((X.tr g).drop j).take (endPos-j)) u ∧
      (((X.tr g).drop j).take (endPos-j)).countP earlyProbabilityMark = 0 := by
  let values := sumValues r weights old word phase
  let regs (n : Nat) := if n ∈ r.continuationRegs then continued n else values n
  have hData (n : Nat) (hn : n ∈ tailLive r.round) : regs n = values n :=
    ite_eq_right (continuationFresh r hn)
  have hActual := sumValuesHold hWeights hOld hAlpha hPhase
  have hLiveRegs : tailLiveWith r.round true = tailLive r.round ++ r.continuationRegs := by
    cases r <;> rfl
  have hFacts : Holds t.regs (factsFrom (tailLiveWith r.round true) regs) := by
    apply holds_of_pointwise
    intro n hn
    rw [hLiveRegs] at hn
    rcases List.mem_append.mp hn with h | h
    · rw [hData n h]
      exact holds_mem hActual (mem_factsFrom h)
    · simpa only [regs, ite_eq_left h] using hContinued n h
  have hReady : At t (probabilityWaitPc r.round true)
      (tailCarryWith l warp r.round (some regs) true) :=
    ht.mono ⟨ht.2.2.2.2.1,ht.2.2.2.2.2.1,hFacts⟩
  have hPhaseMem := phaseLive r false
  have hParity : regs 7258 = b32 phase := (hData _ hPhaseMem).trans (sumValuesPhase r _ _ _ _)
  obtain ⟨u,barInst,elect,leader,failed,hWait,hBar,hElect,hSignal,hPolls,hu,hTail,hPath⟩ :=
    repeatedTailAcknowledgedWithPath hp r warp phase hpPhase regs true hParity hReady hRun
  let jAck := if laneOf l g = leader then j + 4 else j + 3
  have hEnd : j < jAck + failed + 1 := by unfold jAck; split <;> omega
  have hLive (n : Nat) (hn : n ∈ tailLiveWith r.round true) : u.regs n = some (regs n) :=
    holds_mem hu.2.2.2.2.2.2 (mem_factsFrom hn)
  have hReduced : Holds u.regs (factsFrom (tailLive r.round) values) := by
    apply holds_of_pointwise
    intro n hn
    rw [← hData n hn]
    apply hLive n
    rw [hLiveRegs]
    exact List.mem_append_left _ hn
  obtain ⟨hWeightU,hOldU,hAlphaU⟩ := readSumValues hReduced
  refine ⟨u,jAck+failed+1,barInst,hEnd,hBar,hu.mono trivial,hWeightU,hOldU,hAlphaU,?_,?_,hTail,
    hPath,?_⟩
  · exact (hLive _ (phaseLive r true)).trans (congrArg some hParity)
  · intro n hn
    have h : n ∈ tailLiveWith r.round true := by
      rw [hLiveRegs]
      exact List.mem_append_right _ hn
    simpa only [regs, ite_eq_left hn] using hLive n h

  · have hIndex : j+(if laneOf l g = leader then 4 else 3) = jAck := by
      dsimp only [jAck]
      split <;> rfl
    obtain h := tailEarlyCount r (warp := warp) hWait hBar hElect hSignal
      (by dsimp only; rw [hIndex]; exact hPolls)
    dsimp only at h
    rwa [hIndex] at h

end

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m) (r : Repeated)
    (warp : Fin 8) (phase : Nat) (hpPhase : phase < 2)
include hp r warp phase hpPhase

end
end PTX.Kernels.TmlFa4Fwd.Softmax
