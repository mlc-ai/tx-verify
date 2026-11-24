-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedNumeric
public import Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedTail

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Numeric

noncomputable section

namespace Repeated

/-- The register conditions carried from the repeated round's affine shift through its stores. -/
def numericFrame : Repeated → List Nat
  | .biased => biasedExpFrame
  | .unbiased => unbiasedExpFrame

/-- The events before the last P store is drained. The first three stores precede the
main notification in both rounds. -/
def probabilityEvents (r : Repeated) (l : Launch) (g : Nat) (stage : Fin 2)
    (weights : Nat → ℝ) : List Event :=
  let event := fun q => repeatedStoreEvent l g stage r.round q weights
  match r with
  | .biased =>
    [⟨6508, .tc .waitLd⟩, event 0, event 1, event 2, ⟨6527, .tc .waitSt⟩,
      ⟨6532, .arrive (signalLoc l g stage 4) 0 1 true .cta⟩, event 3]
  | .unbiased =>
    [event 0, event 1, event 2, ⟨7435, .tc .waitSt⟩,
      ⟨7437, .arrive (signalLoc l g stage 6) 0 1 true .cta⟩, event 3]

/-- An observed probability-store batch completes exactly one early publication. -/
theorem earlyCountOfEvents {l : Launch} {X : Execution} (r : Repeated)
    {g j : Nat} {stage : Fin 2} {weights : Nat → ℝ}
    (hGet : let es := r.probabilityEvents l g stage weights
      ∀ k : Fin es.length, X.get (g,j+k.val) = es[k.val]?) :
    let es := r.probabilityEvents l g stage weights
    (((X.tr g).drop j).take es.length).countP earlyProbabilityMark = 1 := by
  let es := r.probabilityEvents l g stage weights
  have hEq : ((X.tr g).drop j).take es.length = es := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < es.length
    · rw [List.getElem?_take_of_lt hi,List.getElem?_drop]
      exact hGet ⟨i,hi⟩
    · rw [List.getElem?_eq_none (by simp [List.length_take]; omega),
        List.getElem?_eq_none (by omega)]
  change (((X.tr g).drop j).take es.length).countP earlyProbabilityMark = 1
  rw [hEq]
  cases r <;> rfl

end Repeated

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m) (r : Repeated)
    (stage : Fin 2) (mixed : Bool) {g j b h row blocks visit : Nat} {t : TState} (reference : ℝ)
    (values : Nat → Value) (scores : FmaItem → Option ℝ × Option ℝ) (ht : At t r.affineStart [])
    (hRead : ∀ it ∈ shiftItems r.shiftRound, ∀ n ∈ it.reads, t.regs n = some (values n))
    (hSource : ∀ it ∈ shiftItems r.shiftRound, it.packOk values = true ∧
      splitValue 64 (it.src values) = (scoreValue (scores it).1, scoreValue (scores it).2))
    (hLogits : ∀ it ∈ shiftItems r.shiftRound,
      (scores it).1 = maskedLogit p b h row (visitKey blocks visit (it.x - r.rawBase)) ∧
      (scores it).2 = maskedLogit p b h row (visitKey blocks visit (it.y - r.rawBase)))
    (hScale : readERealPair l g t (.reg (shiftLayout r.shiftRound).scaleReg) =
      some (.ok ((abiFloat p.scaleLog2Bits : EReal), (abiFloat p.scaleLog2Bits : EReal))))
    (hOffset : readERealPair l g t (.reg (shiftLayout r.shiftRound).addReg) =
      some (.ok (((-reference : ℝ) : EReal), ((-reference : ℝ) : EReal))))
    (hFrame : ∀ n ∈ r.numericFrame, t.regs n = some (values n))
    (hStage : r = .biased → values 637 = .pred (stage.val = 1))
    (hMode : r = .biased → t.regs 634 = some (.pred mixed)) (hBase : values 2535 = b32 l.sharedBase)
    (hAddr : r = .unbiased → ∀ q,
      values (probabilityReg .unbiased q) = b32 (probabilityAddress l g stage q))
    (hSignal : r = .unbiased → values 5187 = b32 (l.sharedBase + 8 * stage.val))
include hp r stage mixed reference values scores ht hRead hSource hLogits hScale hOffset hFrame
    hStage hMode hBase hAddr hSignal

/-- Both affine shifts and all decoded P writes retain the loop continuation registers. -/
theorem repeatedProbabilitiesWithPath
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    let weights := fun col => shiftedWeight p b h row (visitKey blocks visit col) reference
    let events := r.probabilityEvents l g stage weights
    ∃ u, (∀ i : Fin events.length, X.get (g, j + i.val) = events[i.val]?) ∧
      At u (probabilityWaitPc r.round true) [] ∧ RepeatedWeights r u weights ∧
      (∀ n ∈ r.numericFrame, u.regs n = some (values n)) ∧
      (∀ n ∈ roundContinuationRegs, u.regs n = t.regs n) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (j + events.length)) none ∧
      TraceReach kernel Assumptions.all l g t (((X.tr g).drop j).take events.length) u := by
  cases r
  · have hT : At t (shiftStart 1) [(634, .pred mixed)] := ht.mono ⟨hMode rfl, trivial⟩
    obtain ⟨u, hLd, h0, h1, h2, hWait, hArrive, h3, hU, hW, hF, hKeep,hTail,hPath⟩ :=
      biasedNumericStoresOfSplitWithPath hp stage mixed reference values scores hT hRead hSource
        hLogits
        hScale hOffset hFrame (hStage rfl) hBase hRun
    refine ⟨u, ?_, hU, hW, hF, hKeep,hTail,hPath⟩
    intro i
    change Fin 7 at i
    fin_cases i
    · exact hLd
    · exact h0
    · exact h1
    · exact h2
    · exact hWait
    · exact hArrive
    · exact h3
  · obtain ⟨u, h0, h1, h2, hWait, hArrive, h3, hU, hW, hF, hKeep,hTail,hPath⟩ :=
      unbiasedNumericStoresOfSplitWithPath hp stage reference values scores ht hRead hSource
        hLogits
        hScale hOffset hFrame (hAddr rfl) (hSignal rfl) hRun
    refine ⟨u, ?_, hU, hW, hF, hKeep,hTail,hPath⟩
    intro i
    change Fin 6 at i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact hWait
    · exact hArrive
    · exact h3

end

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m) (r : Repeated)
    (warp : Fin 8) (mixed : Bool) {g j b h row blocks visit : Nat} {t : TState} (old : ℝ)
    (oldRef newRef : Option ℝ) (phase : Nat) (hpPhase : phase < 2) (values : Nat → Value)
    (scores : FmaItem → Option ℝ × Option ℝ) (ht : At t r.affineStart [])
    (hRead : ∀ it ∈ shiftItems r.shiftRound, ∀ n ∈ it.reads, t.regs n = some (values n))
include hp r warp mixed old oldRef newRef phase hpPhase values scores ht hRead

end
end PTX.Kernels.TmlFa4Fwd.Softmax
