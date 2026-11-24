-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedExponent
public import Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedTail

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section

namespace Repeated

def shiftRound : Repeated → Fin 3
  | .biased => 1
  | .unbiased => 2

def rawBase : Repeated → Nat
  | .biased => 1363
  | .unbiased => 5520

def affineStart (r : Repeated) : Nat := shiftStart r.shiftRound

def affineEnd (r : Repeated) : Nat := shiftEnd r.shiftRound

end Repeated

set_option maxRecDepth 100000 in
private theorem shiftedWordTable (round : Repeated) :
    (List.range 64).all (fun i => (shiftItems round.shiftRound)[i]?.any fun it =>
      it.x == round.rawBase + 2 * i && it.y == round.rawBase + 2 * i + 1) = true := by
  cases round <;> kernel_rfl

private theorem shiftedWord (round : Repeated) {i : Nat} (hi : i < 64) :
    ∃ it ∈ shiftItems round.shiftRound, it.x = round.rawBase + 2 * i ∧
      it.y = round.rawBase + 2 * i + 1 := by
  have h := List.all_eq_true.mp (shiftedWordTable round) i (List.mem_range.mpr hi)
  cases hc : (shiftItems round.shiftRound)[i]? with
  | none => rw [hc] at h; cases h
  | some it =>
    rw [hc] at h
    have hv : it.x = round.rawBase + 2 * i ∧ it.y = round.rawBase + 2 * i + 1 := by
      simpa only [Option.any_some, Bool.and_eq_true, beq_iff_eq] using h
    exact ⟨it, List.mem_of_getElem? hc, hv⟩

/-- Replaying the shifted packed registers preserves their finite-or-masked form.
Only the physical score columns are needed, including the columns of a padding row. -/
theorem repeatedShiftedWordsLocal {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) (round : Repeated) {g : Nat} {t : TState}
    (tracked : Nat → Option ℝ)
    (reference : ℝ) (values : Nat → Value) (scores : FmaItem → Option ℝ × Option ℝ)
    (ht : At t round.affineStart [])
    (hRead : ∀ it ∈ shiftItems round.shiftRound, ∀ r ∈ it.reads, t.regs r = some (values r))
    (hSource : ∀ it ∈ shiftItems round.shiftRound, it.packOk values = true ∧
      splitValue 64 (it.src values) = (scoreValue (scores it).1, scoreValue (scores it).2))
    (hLogits : ∀ it ∈ shiftItems round.shiftRound,
      (scores it).1 = tracked (it.x - round.rawBase) ∧
      (scores it).2 = tracked (it.y - round.rawBase))
    (hScale : readERealPair l g t (.reg (shiftLayout round.shiftRound).scaleReg) =
      some (.ok ((abiFloat p.scaleLog2Bits : EReal), (abiFloat p.scaleLog2Bits : EReal))))
    (hOffset : readERealPair l g t (.reg (shiftLayout round.shiftRound).addReg) =
      some (.ok (((-reference : ℝ) : EReal), ((-reference : ℝ) : EReal)))) :
    let raw := fun col => affineScore (abiFloat p.scaleLog2Bits) (-reference)
      (tracked col)
    ∃ u, At u round.affineEnd [] ∧
      (∀ col < 128, u.regs (round.rawBase + col) = some (scoreValue (raw col))) ∧
      (∀ r ∉ (shiftItems round.shiftRound).flatMap FmaItem.writes, u.regs r = t.regs r) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u := by
  obtain ⟨u, hPc, hFault, hSub, hAcc, hTail, hFrame, hOut⟩ :=
    shiftTraceOfSplitLocal round.shiftRound (scalePositive hp).1 values scores ht.1 ht.2.2.2.1
      hRead hSource hScale hOffset
  refine ⟨u, ⟨hPc, hSub.trans ht.2.1, hAcc.trans ht.2.2.1, hFault, trivial⟩, ?_, hFrame, hTail⟩
  intro col hCol
  obtain ⟨it, hit, hx, hy⟩ := shiftedWord round (i := col / 2) (by omega)
  obtain ⟨hX, hY⟩ := hOut it hit
  obtain ⟨hL0, hL1⟩ := hLogits it hit
  dsimp
  by_cases hEven : col % 2 = 0
  · have hIndex : 2 * (col / 2) = col := by omega
    rw [hIndex] at hx
    rw [← hx, hX, hL0, hx, Nat.add_sub_cancel_left]
  · have hIndex : 2 * (col / 2) + 1 = col := by omega
    rw [Nat.add_assoc, hIndex] at hy
    rw [← hy, hY, hL1, hy, Nat.add_sub_cancel_left]

theorem repeatedShiftedWordsOfTrackedScores {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (round : Repeated) {g j : Nat} {t : TState}
    {ending : Option TState}
    (tracked : Nat → Option ℝ)
    (reference : ℝ) (values : Nat → Value) (scores : FmaItem → Option ℝ × Option ℝ)
    (ht : At t round.affineStart [])
    (hRead : ∀ it ∈ shiftItems round.shiftRound, ∀ r ∈ it.reads, t.regs r = some (values r))
    (hSource : ∀ it ∈ shiftItems round.shiftRound, it.packOk values = true ∧
      splitValue 64 (it.src values) = (scoreValue (scores it).1, scoreValue (scores it).2))
    (hLogits : ∀ it ∈ shiftItems round.shiftRound,
      (scores it).1 = tracked (it.x - round.rawBase) ∧
      (scores it).2 = tracked (it.y - round.rawBase))
    (hScale : readERealPair l g t (.reg (shiftLayout round.shiftRound).scaleReg) =
      some (.ok ((abiFloat p.scaleLog2Bits : EReal), (abiFloat p.scaleLog2Bits : EReal))))
    (hOffset : readERealPair l g t (.reg (shiftLayout round.shiftRound).addReg) =
      some (.ok (((-reference : ℝ) : EReal), ((-reference : ℝ) : EReal))))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) ending)
    (hPresent : (X.tr g).drop j ≠ []) :
    let raw := fun col => affineScore (abiFloat p.scaleLog2Bits) (-reference)
      (tracked col)
    ∃ u, At u round.affineEnd [] ∧
      (∀ col < 128, u.regs (round.rawBase + col) = some (scoreValue (raw col))) ∧
      (∀ r ∉ (shiftItems round.shiftRound).flatMap FmaItem.writes, u.regs r = t.regs r) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop j) ending := by
  obtain ⟨u,hu,hWords,hFrame,hPath⟩ := repeatedShiftedWordsLocal hp round
    tracked reference values scores ht hRead hSource hLogits hScale hOffset
  exact ⟨u,hu,hWords,hFrame,hRun.after_local_nonempty hPath hPresent⟩

set_option maxRecDepth 100000 in
private theorem continuationShiftSafe (r : Repeated) :
    roundContinuationRegs.all (fun n =>
      !((shiftItems r.shiftRound).flatMap FmaItem.writes).contains n) = true := by
  cases r <;> kernel_rfl

private theorem continuationShiftFresh (r : Repeated) {n : Nat}
    (hn : n ∈ roundContinuationRegs) : n ∉ (shiftItems r.shiftRound).flatMap FmaItem.writes := by
  have h := List.all_eq_true.mp (continuationShiftSafe r) n hn
  simpa only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] using h

set_option maxRecDepth 100000 in
private theorem unbiasedFrameShift :
    unbiasedExpFrame.all (fun r => !((shiftItems 2).flatMap FmaItem.writes).contains r) = true := by
  kernel_rfl

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m) (stage : Fin 2)
    {g j b h row blocks visit : Nat} {t : TState} (reference : ℝ) (values : Nat → Value)
    (scores : FmaItem → Option ℝ × Option ℝ) (ht : At t (shiftStart 2) [])
    (hRead : ∀ it ∈ shiftItems 2, ∀ r ∈ it.reads, t.regs r = some (values r))
    (hSource : ∀ it ∈ shiftItems 2, it.packOk values = true ∧
      splitValue 64 (it.src values) = (scoreValue (scores it).1, scoreValue (scores it).2))
    (hLogits : ∀ it ∈ shiftItems 2,
      (scores it).1 = maskedLogit p b h row (visitKey blocks visit (it.x - 5520)) ∧
      (scores it).2 = maskedLogit p b h row (visitKey blocks visit (it.y - 5520)))
    (hScale : readERealPair l g t (.reg (shiftLayout 2).scaleReg) =
      some (.ok ((abiFloat p.scaleLog2Bits : EReal), (abiFloat p.scaleLog2Bits : EReal))))
    (hOffset : readERealPair l g t (.reg (shiftLayout 2).addReg) =
      some (.ok (((-reference : ℝ) : EReal), ((-reference : ℝ) : EReal))))
    (hFrame : ∀ r ∈ unbiasedExpFrame, t.regs r = some (values r))
    (hAddr : ∀ q, values (probabilityReg .unbiased q) = b32 (probabilityAddress l g stage q))
    (hSignal : values 5187 = b32 (l.sharedBase + 8 * stage.val))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none)
include hp stage reference values scores ht hRead hSource hLogits hScale hOffset hFrame hAddr
    hSignal hRun

/-- The unbiased round reaches all four actual TMEM writes from the masked scores
at the affine shift, and retains the exact unrounded weights for the denominator. -/
theorem unbiasedNumericStoresOfSplitWithPath :
    let weights := fun col => shiftedWeight p b h row (visitKey blocks visit col) reference
    ∃ u, X.get (g, j) = some (unbiasedStoreEvent l g stage 0 weights) ∧
      X.get (g, j + 1) = some (unbiasedStoreEvent l g stage 1 weights) ∧
      X.get (g, j + 2) = some (unbiasedStoreEvent l g stage 2 weights) ∧
      X.get (g, j + 3) = some ⟨7435, .tc .waitSt⟩ ∧
      X.get (g, j + 4) = some ⟨7437, .arrive (signalLoc l g stage 6) 0 1 true .cta⟩ ∧
      X.get (g, j + 5) = some (unbiasedStoreEvent l g stage 3 weights) ∧
      At u 7447 [] ∧ RepeatedWeights .unbiased u weights ∧
      (∀ r ∈ unbiasedExpFrame, u.regs r = some (values r)) ∧
      (∀ n ∈ roundContinuationRegs, u.regs n = t.regs n) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j + 6)) none ∧
      TraceReach kernel Assumptions.all l g t (((X.tr g).drop j).take 6) u := by
  obtain ⟨u, hU, hRaw, hKeep, hLocal⟩ := repeatedShiftedWordsLocal hp .unbiased
    (fun col => maskedLogit p b h row (visitKey blocks visit col))
    reference values scores ht hRead hSource hLogits hScale hOffset
  have hCarry (r : Nat) (hr : r ∈ unbiasedExpFrame) : u.regs r = some (values r) := by
    have he := List.all_eq_true.mp unbiasedFrameShift r hr
    simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at he
    exact (hKeep r he).trans (hFrame r hr)
  obtain ⟨v,h0,h1,h2,h3,h4,h5,hV,hWeights,hFacts,hSaved,hRest,hPath⟩ :=
    unbiasedProbabilityStoresWithPath hp stage _ _ values hU hRaw
    (fun col => hardwareShiftedWeight hp b h row (visitKey blocks visit col) reference)
    (fun col => softwareShiftedWeight hp b h row (visitKey blocks visit col) reference)
    hCarry hAddr hSignal (hRun.after_local hLocal)
  exact ⟨v,h0,h1,h2,h3,h4,h5,hV,hWeights,hFacts,
    fun n hn => (hSaved n hn).trans (hKeep n (continuationShiftFresh .unbiased hn)), hRest,
      (TraceReach.of_local hLocal).append hPath⟩

end

set_option maxRecDepth 100000 in
private theorem biasedFrameShift :
    (634 :: biasedExpFrame).all (fun r => !((shiftItems 1).flatMap FmaItem.writes).contains r) =
      true := by kernel_rfl

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m) (stage : Fin 2)
    (mixed : Bool) {g j b h row blocks visit : Nat} {t : TState} (reference : ℝ)
    (values : Nat → Value) (scores : FmaItem → Option ℝ × Option ℝ)
    (ht : At t (shiftStart 1) [(634, .pred mixed)])
    (hRead : ∀ it ∈ shiftItems 1, ∀ r ∈ it.reads, t.regs r = some (values r))
    (hSource : ∀ it ∈ shiftItems 1, it.packOk values = true ∧
      splitValue 64 (it.src values) = (scoreValue (scores it).1, scoreValue (scores it).2))
    (hLogits : ∀ it ∈ shiftItems 1,
      (scores it).1 = maskedLogit p b h row (visitKey blocks visit (it.x - 1363)) ∧
      (scores it).2 = maskedLogit p b h row (visitKey blocks visit (it.y - 1363)))
    (hScale : readERealPair l g t (.reg (shiftLayout 1).scaleReg) =
      some (.ok ((abiFloat p.scaleLog2Bits : EReal), (abiFloat p.scaleLog2Bits : EReal))))
    (hOffset : readERealPair l g t (.reg (shiftLayout 1).addReg) =
      some (.ok (((-reference : ℝ) : EReal), ((-reference : ℝ) : EReal))))
    (hFrame : ∀ r ∈ biasedExpFrame, t.regs r = some (values r))
    (hStage : values 637 = .pred (stage.val = 1)) (hBase : values 2535 = b32 l.sharedBase)
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none)
include hp stage mixed reference values scores ht hRead hSource hLogits hScale hOffset hFrame hStage
    hBase hRun

/-- Either biased exponent branch writes the masked, reference-shifted probabilities
from its decoded affine score shift and keeps the mixed-layout FP32 reduction operands. -/
theorem biasedNumericStoresOfSplitWithPath :
    let weights := fun col => shiftedWeight p b h row (visitKey blocks visit col) reference
    ∃ u, X.get (g, j) = some ⟨6508, .tc .waitLd⟩ ∧
      X.get (g, j + 1) = some (repeatedStoreEvent l g stage .biased 0 weights) ∧
      X.get (g, j + 2) = some (repeatedStoreEvent l g stage .biased 1 weights) ∧
      X.get (g, j + 3) = some (repeatedStoreEvent l g stage .biased 2 weights) ∧
      X.get (g, j + 4) = some ⟨6527, .tc .waitSt⟩ ∧
      X.get (g, j + 5) = some ⟨6532, .arrive (signalLoc l g stage 4) 0 1 true .cta⟩ ∧
      X.get (g, j + 6) = some (repeatedStoreEvent l g stage .biased 3 weights) ∧
      At u 6542 [] ∧ RepeatedWeights .biased u weights ∧
      (∀ r ∈ biasedExpFrame, u.regs r = some (values r)) ∧
      (∀ n ∈ roundContinuationRegs, u.regs n = t.regs n) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j + 7)) none ∧
      TraceReach kernel Assumptions.all l g t (((X.tr g).drop j).take 7) u := by
  obtain ⟨u, hU, hRaw, hKeep, hLocal⟩ := repeatedShiftedWordsLocal hp .biased
    (fun col => maskedLogit p b h row (visitKey blocks visit col))
    reference values scores (ht.mono trivial) hRead hSource hLogits hScale hOffset
  have hFrameReg (r : Nat) (hr : r ∈ 634 :: biasedExpFrame) : u.regs r = t.regs r := by
    have he := List.all_eq_true.mp biasedFrameShift r hr
    simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at he
    exact hKeep r he
  have hCarry (r : Nat) (hr : r ∈ biasedExpFrame) : u.regs r = some (values r) :=
    (hFrameReg r (List.mem_cons_of_mem _ hr)).trans (hFrame r hr)
  have hU' : At u 5815 [(634, .pred mixed)] := hU.mono
    ⟨(hFrameReg 634 (List.Mem.head _)).trans ht.2.2.2.2.1, trivial⟩
  obtain ⟨v,h0,h1,h2,h3,h4,h5,h6,hV,hWeights,hFacts,hSaved,hRest,hPath⟩ :=
    biasedProbabilityStoresWithPath hp stage mixed _ _ values hU' hRaw
    (fun col => hardwareShiftedWeight hp b h row (visitKey blocks visit col) reference)
    (fun col => softwareShiftedWeight hp b h row (visitKey blocks visit col) reference)
    hCarry hStage hBase (hRun.after_local hLocal)
  exact ⟨v,h0,h1,h2,h3,h4,h5,h6,hV,hWeights,hFacts,
    fun n hn => (hSaved n hn).trans (hKeep n (continuationShiftFresh .biased hn)), hRest,
      (TraceReach.of_local hLocal).append hPath⟩

end

end
/-- A shifted mask contributes zero and a finite shifted score contributes its exp2. -/
noncomputable def repeatedExpWeight (shifted : Option ℝ) : ℝ := shifted.elim 0 (fun x => (2 : ℝ)^x)

private theorem repeatedHardwareExp (shifted : Option ℝ) :
    ex2E true (scoreValue shifted) = .ok (fl (repeatedExpWeight shifted)) := by
  cases shifted with
  | none => exact hardwareExponentNegInf
  | some x =>
    exact ex2E_fin (x := x) (by simp [scoreValue,valFloat,pure,Except.pure])

private theorem repeatedSoftwareExp (shifted : Option ℝ) :
    Assumptions.swExp2Lane (scoreValue shifted) = .ok (repeatedExpWeight shifted) := by
  cases shifted with
  | none => exact Assumptions.swExp2Lane_negInf
  | some x => rfl

/-- The probability frame contains the actual shifted-score inputs and the
nonarithmetic operands retained by the selected exponent path. -/
structure RepeatedProbabilityShiftFrame (p : Params) (l : Launch) (mode : Repeated)
    (g : Nat) (stage : Fin 2) (t : TState)
    (shifted : Nat → Option ℝ) (reference : ℝ) where
  words : Nat → Value
  inputs : FmaItem → Option ℝ × Option ℝ
  mixed : Bool
  atShift : At t mode.affineStart []
  reads : ∀ it ∈ shiftItems mode.shiftRound, ∀ r ∈ it.reads, t.regs r = some (words r)
  source : ∀ it ∈ shiftItems mode.shiftRound, it.packOk words = true ∧
    splitValue 64 (it.src words) = (scoreValue (inputs it).1, scoreValue (inputs it).2)
  columns : ∀ it ∈ shiftItems mode.shiftRound,
    (inputs it).1 = shifted (it.x-mode.rawBase) ∧
    (inputs it).2 = shifted (it.y-mode.rawBase)
  scale : readERealPair l g t (.reg (shiftLayout mode.shiftRound).scaleReg) =
    some (.ok ((abiFloat p.scaleLog2Bits : EReal),(abiFloat p.scaleLog2Bits : EReal)))
  offset : readERealPair l g t (.reg (shiftLayout mode.shiftRound).addReg) =
    some (.ok (((-reference : ℝ) : EReal),((-reference : ℝ) : EReal)))
  frame : ∀ r ∈ (match mode with | .biased => biasedExpFrame | .unbiased => unbiasedExpFrame),
    t.regs r = some (words r)
  mixChoice : mode = .biased → t.regs 634 = some (.pred mixed)
  biasedStage : mode = .biased → words 637 = .pred (stage.val = 1)
  biasedBase : mode = .biased → words 2535 = b32 l.sharedBase
  plainAddresses : mode = .unbiased → ∀ q, words (probabilityReg .unbiased q) =
    b32 (probabilityAddress l g stage q)
  plainSignal : mode = .unbiased → words 5187 = b32 (l.sharedBase+8*stage.val)

/-- A present probability store replays to the exact finite pair sequence determined
by this round's packed scores. The shape works for every physical query row. -/
theorem RepeatedProbabilityShiftFrame.storeOfPrefix
    {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) {mode : Repeated} {g j : Nat} {stage : Fin 2} {t : TState}
    {ending : Option TState} {scores : Nat → Option ℝ} {reference : ℝ}
    (frame : RepeatedProbabilityShiftFrame p l mode g stage t scores reference)
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) ending)
    (q : Fin 4)
    (hAvail : ending = none ∨ j+mode.probabilityStoreOffset q < (X.tr g).length) :
    let weights := fun i =>
      repeatedExpWeight (affineScore (abiFloat p.scaleLog2Bits) (-reference) (scores i))
    X.get (g,j+mode.probabilityStoreOffset q) =
      some (repeatedStoreEvent l g stage mode.round q weights) := by
  have hPresent : (X.tr g).drop j ≠ [] := by
    intro hEmpty
    rcases hAvail with rfl | hLen
    · rw [hEmpty] at hRun
      cases hRun
    · have h := congrArg List.length hEmpty
      simp only [List.length_drop,List.length_nil] at h
      omega
  obtain ⟨u,hU,hWords,hKeep,hTail⟩ := repeatedShiftedWordsOfTrackedScores hp mode
    scores reference frame.words frame.inputs frame.atShift frame.reads frame.source frame.columns
    frame.scale frame.offset hRun hPresent
  cases mode with
  | biased =>
    have hFrameReg (r : Nat) (hr : r ∈ 634 :: biasedExpFrame) : u.regs r = t.regs r := by
      have he := List.all_eq_true.mp biasedFrameShift r hr
      simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at he
      exact hKeep r he
    have hCarry (r : Nat) (hr : r ∈ biasedExpFrame) : u.regs r = some (frame.words r) :=
      (hFrameReg r (List.mem_cons_of_mem _ hr)).trans (frame.frame r hr)
    have hU' : At u 5815 [(634, .pred frame.mixed)] := hU.mono
      ⟨(hFrameReg 634 (List.Mem.head _)).trans (frame.mixChoice rfl), trivial⟩
    exact biasedProbabilityStoreOfPrefix hp stage frame.mixed q _ _ frame.words hU' hWords
      (fun _ => repeatedHardwareExp _) (fun _ => repeatedSoftwareExp _) hCarry
      (frame.biasedStage rfl) (frame.biasedBase rfl) hTail hAvail
  | unbiased =>
    have hCarry (r : Nat) (hr : r ∈ unbiasedExpFrame) : u.regs r = some (frame.words r) := by
      have he := List.all_eq_true.mp unbiasedFrameShift r hr
      simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at he
      exact (hKeep r he).trans (frame.frame r hr)
    exact unbiasedProbabilityStoreOfPrefix hp stage q _ _ frame.words hU hWords
      (fun _ => repeatedHardwareExp _) (fun _ => repeatedSoftwareExp _) hCarry
      (frame.plainAddresses rfl) (frame.plainSignal rfl) hTail hAvail

end PTX.Kernels.TmlFa4Fwd.Softmax
