-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstPublication
public import Kernels.TmlFa4Fwd.Proof.SoftmaxWeights

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section

private theorem firstShiftWordTable :
    (List.range 64).all (fun i => (shiftItems 0)[i]?.any fun it =>
      it.x == 3687 + 2 * i && it.y == 3687 + 2 * i + 1) = true := by
  decide +kernel

private theorem firstShiftWord {i : Nat} (hi : i < 64) :
    ∃ it ∈ shiftItems 0, it.x = 3687 + 2 * i ∧ it.y = 3687 + 2 * i + 1 := by
  have h := List.all_eq_true.mp firstShiftWordTable i (List.mem_range.mpr hi)
  cases hc : (shiftItems 0)[i]? with
  | none => rw [hc] at h; cases h
  | some it =>
    rw [hc] at h
    have hv : it.x = 3687 + 2 * i ∧ it.y = 3687 + 2 * i + 1 := by
      simpa only [Option.any_some, Bool.and_eq_true, beq_iff_eq] using h
    exact ⟨it, List.mem_of_getElem? hc, hv⟩

variable {p : Params}

/-- The first-round affine shifts and exponent computation leave the target's four
groups of weights ready in the packing registers. -/
theorem firstShiftedPacksLocal {l : Launch} {m : Mem0} (hp : Pre p l m) {g : Nat} {t : TState}
    {F : List (Nat × Value)} (reference : ℝ) (columns : Nat → Option ℝ) (expected : Nat → ℝ)
    (hExponent : ∀ i, ex2E true (scoreValue
      (affineScore (abiFloat p.scaleLog2Bits) (-reference) (columns i))) =
        .ok (.float .f32 (expected i))) (values : Nat → Value)
    (scores : FmaItem → Option ℝ × Option ℝ) (ht : At t (shiftStart 0) F)
    (hRead : ∀ it ∈ shiftItems 0, ∀ r ∈ it.reads, t.regs r = some (values r))
    (hSource : ∀ it ∈ shiftItems 0, it.packOk values = true ∧
      it.src values = joinValue (scoreValue (scores it).1) (scoreValue (scores it).2))
    (hLogits : ∀ it ∈ shiftItems 0,
      (scores it).1 = columns (it.x - 3687) ∧
      (scores it).2 = columns (it.y - 3687))
    (hScale : readERealPair l g t (.reg (shiftLayout 0).scaleReg) =
      some (.ok ((abiFloat p.scaleLog2Bits : EReal), (abiFloat p.scaleLog2Bits : EReal))))
    (hOffset : readERealPair l g t (.reg (shiftLayout 0).addReg) =
      some (.ok (((-reference : ℝ) : EReal), ((-reference : ℝ) : EReal)))) :
    ∃ u, At u 4818 [] ∧
      (∀ q : Fin 4, ∀ i < 8, u.regs (firstPackedReg q + i) =
        some (probabilityDoubleWord (fun k => expected (32 * q.val + k)) i)) ∧
      (∀ i < 128, u.regs (1231 + i) = some (fl (expected i))) ∧
      (∀ r ∉ (shiftItems 0).flatMap FmaItem.writes,
        (r < 1231 ∨ 1359 ≤ r) → (r < 3815 ∨ 3879 ≤ r) →
        (r < 8154 ∨ 8186 ≤ r) → u.regs r = t.regs r) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u := by
  obtain ⟨v, hPc, hFault, hSub, hAcc, hTail, hFrame, hOut⟩ :=
    shiftTraceLocal 0 (scalePositive hp).1 values scores ht.1 ht.2.2.2.1
      hRead hSource hScale hOffset
  have hAt : At v 4594 [] := ⟨hPc, hSub.trans ht.2.1, hAcc.trans ht.2.2.1, hFault, trivial⟩
  let raw := fun (q : Fin 4) i => scoreValue (affineScore (abiFloat p.scaleLog2Bits) (-reference)
    (columns (32 * q.val + i)))
  let byQuarter (q : Fin 4) (i : Nat) := expected (32 * q.val + i)
  have hWords (q : Fin 4) (i : Nat) (hi : i < 32) :
      v.regs (firstHardwareInput q + i) = some (raw q i) := by
    let col := 32 * q.val + i
    have hQ := q.isLt
    have hBound : col / 2 < 64 := by unfold col; omega
    obtain ⟨it, hIt, hx, hy⟩ := firstShiftWord hBound
    obtain ⟨hX, hY⟩ := hOut it hIt
    obtain ⟨hL0, hL1⟩ := hLogits it hIt
    have hInput : firstHardwareInput q + i = 3687 + col := by
      simp only [firstHardwareInput, col, Nat.add_assoc]
    by_cases hEven : col % 2 = 0
    · have hCol : 2 * (col / 2) = col := by omega
      rw [hCol] at hx
      rw [hInput, ← hx, hX, hL0, hx, Nat.add_sub_cancel_left]
    · have hCol : 2 * (col / 2) + 1 = col := by omega
      rw [Nat.add_assoc, hCol] at hy
      rw [hInput, ← hy, hY, hL1, hy, Nat.add_sub_cancel_left]
  have hEval (q : Fin 4) (i : Nat) (_ : i < 32) :
      ex2E true (raw q i) = .ok (.float .f32 (byQuarter q i)) := hExponent _
  obtain ⟨u, hU, hP, hExps, hKeep, hAfter⟩ :=
    firstPackExponentLocal raw byQuarter hEval hAt hWords
  refine ⟨u,hU,hP,?_,fun r hS hE hC hP =>
    (hKeep r hE hC hP).trans (hFrame r hS),hTail.trans hAfter⟩
  intro i hi
  let q : Fin 4 := ⟨i / 32, by omega⟩
  have hI : 32 * q.val + i % 32 = i := by dsimp [q]; omega
  have hReg := hExps q (i % 32) (Nat.mod_lt _ (by decide))
  simpa only [firstHardwareOutput, Nat.add_assoc, hI, byQuarter] using hReg

theorem firstShiftedPacksInPrefix {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    {g j : Nat} {t : TState} {F : List (Nat × Value)} {ending : Option TState} (reference : ℝ)
    (columns : Nat → Option ℝ) (expected : Nat → ℝ)
    (hExponent : ∀ i, ex2E true (scoreValue
      (affineScore (abiFloat p.scaleLog2Bits) (-reference) (columns i))) =
        .ok (.float .f32 (expected i))) (values : Nat → Value)
    (scores : FmaItem → Option ℝ × Option ℝ) (ht : At t (shiftStart 0) F)
    (hRead : ∀ it ∈ shiftItems 0, ∀ r ∈ it.reads, t.regs r = some (values r))
    (hSource : ∀ it ∈ shiftItems 0, it.packOk values = true ∧
      it.src values = joinValue (scoreValue (scores it).1) (scoreValue (scores it).2))
    (hLogits : ∀ it ∈ shiftItems 0,
      (scores it).1 = columns (it.x - 3687) ∧
      (scores it).2 = columns (it.y - 3687))
    (hScale : readERealPair l g t (.reg (shiftLayout 0).scaleReg) =
      some (.ok ((abiFloat p.scaleLog2Bits : EReal), (abiFloat p.scaleLog2Bits : EReal))))
    (hOffset : readERealPair l g t (.reg (shiftLayout 0).addReg) =
      some (.ok (((-reference : ℝ) : EReal), ((-reference : ℝ) : EReal))))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) ending)
    (hNonempty : (X.tr g).drop j ≠ []) :
    ∃ u, At u 4818 [] ∧
      (∀ q : Fin 4, ∀ i < 8, u.regs (firstPackedReg q + i) =
        some (probabilityDoubleWord (fun k => expected (32 * q.val + k)) i)) ∧
      (∀ i < 128, u.regs (1231 + i) = some (fl (expected i))) ∧
      (∀ r ∉ (shiftItems 0).flatMap FmaItem.writes,
        (r < 1231 ∨ 1359 ≤ r) → (r < 3815 ∨ 3879 ≤ r) →
        (r < 8154 ∨ 8186 ≤ r) → u.regs r = t.regs r) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop j) ending := by
  obtain ⟨u,hU,hP,hE,hFrame,hLocal⟩ := firstShiftedPacksLocal hp reference columns expected
    hExponent values scores ht hRead hSource hLogits hScale hOffset
  exact ⟨u,hU,hP,hE,hFrame,hRun.after_local_nonempty hLocal hNonempty⟩

/-- The first-round affine shifts and exponent computation leave the target's four
groups of weights ready in the packing registers. -/
theorem firstShiftedPacks {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    {g j b h row blocks : Nat} {t : TState} {F : List (Nat × Value)} (reference : ℝ)
    (values : Nat → Value) (scores : FmaItem → Option ℝ × Option ℝ) (ht : At t (shiftStart 0) F)
    (hRead : ∀ it ∈ shiftItems 0, ∀ r ∈ it.reads, t.regs r = some (values r))
    (hSource : ∀ it ∈ shiftItems 0, it.packOk values = true ∧
      it.src values = joinValue (scoreValue (scores it).1) (scoreValue (scores it).2))
    (hLogits : ∀ it ∈ shiftItems 0,
      (scores it).1 = maskedLogit p b h row (visitKey blocks 0 (it.x - 3687)) ∧
      (scores it).2 = maskedLogit p b h row (visitKey blocks 0 (it.y - 3687)))
    (hScale : readERealPair l g t (.reg (shiftLayout 0).scaleReg) =
      some (.ok ((abiFloat p.scaleLog2Bits : EReal), (abiFloat p.scaleLog2Bits : EReal))))
    (hOffset : readERealPair l g t (.reg (shiftLayout 0).addReg) =
      some (.ok (((-reference : ℝ) : EReal), ((-reference : ℝ) : EReal))))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    let expected := fun i => shiftedWeight p b h row (visitKey blocks 0 i) reference
    ∃ u, At u 4818 [] ∧
      (∀ q : Fin 4, ∀ i < 8, u.regs (firstPackedReg q + i) =
        some (probabilityDoubleWord (fun k => expected (32 * q.val + k)) i)) ∧
      (∀ i < 128, u.regs (1231 + i) = some (fl (expected i))) ∧
      (∀ r ∉ (shiftItems 0).flatMap FmaItem.writes,
        (r < 1231 ∨ 1359 ≤ r) → (r < 3815 ∨ 3879 ≤ r) →
        (r < 8154 ∨ 8186 ≤ r) → u.regs r = t.regs r) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop j) none := by
  have hNonempty : (X.tr g).drop j ≠ [] := by
    intro hEmpty
    rw [hEmpty] at hRun
    cases hRun
  exact firstShiftedPacksInPrefix hp reference
    (fun c => maskedLogit p b h row (visitKey blocks 0 c))
    (fun c => shiftedWeight p b h row (visitKey blocks 0 c) reference)
    (fun c => hardwareShiftedWeight hp b h row (visitKey blocks 0 c) reference)
    values scores ht hRead hSource hLogits hScale hOffset hRun hNonempty

private def publicationRegs : List Nat :=
  [1062, 2535, 3217, 3223, 3226, 3225, 3224] ++ firstTransitionRegs

private theorem publicationRegsAudit :
    publicationRegs.all (fun r => !((shiftItems 0).flatMap FmaItem.writes).contains r &&
      (decide (r < 1231 ∨ 1359 ≤ r)) && (decide (r < 3815 ∨ 3879 ≤ r)) &&
      (decide (r < 8154 ∨ 8186 ≤ r))) = true := by
  decide +kernel

private theorem publicationFrame {t u : TState}
    (hFrame : ∀ r ∉ (shiftItems 0).flatMap FmaItem.writes,
      (r < 1231 ∨ 1359 ≤ r) → (r < 3815 ∨ 3879 ≤ r) →
      (r < 8154 ∨ 8186 ≤ r) → u.regs r = t.regs r) :
    ∀ r ∈ publicationRegs, u.regs r = t.regs r := by
  intro r hr
  have h := List.all_eq_true.mp publicationRegsAudit r hr
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not, decide_eq_true_eq] at h
  exact hFrame r h.1.1.1 h.1.1.2 h.1.2 h.2

/-- The first round publishes all 128 shifted probabilities to the two P slots and observes
the correction acknowledgement on its actual trace. This connects the numeric profile to the
TMEM and barrier protocol for both softmax groups. -/
theorem firstRoundNumericPublication {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (warp : Fin 8) {g j b h row blocks : Nat} {t : TState} (reference : ℝ) (values : Nat → Value)
    (scores : FmaItem → Option ℝ × Option ℝ) (keep : Nat → Value)
    (hTransition : Holds t.regs (factsFrom firstTransitionRegs keep))
    (ht : At t (shiftStart 0) (tailFrame l warp))
    (hRead : ∀ it ∈ shiftItems 0, ∀ r ∈ it.reads, t.regs r = some (values r))
    (hSource : ∀ it ∈ shiftItems 0, it.packOk values = true ∧
      it.src values = joinValue (scoreValue (scores it).1) (scoreValue (scores it).2))
    (hLogits : ∀ it ∈ shiftItems 0,
      (scores it).1 = maskedLogit p b h row (visitKey blocks 0 (it.x - 3687)) ∧
      (scores it).2 = maskedLogit p b h row (visitKey blocks 0 (it.y - 3687)))
    (hScale : readERealPair l g t (.reg (shiftLayout 0).scaleReg) =
      some (.ok ((abiFloat p.scaleLog2Bits : EReal), (abiFloat p.scaleLog2Bits : EReal))))
    (hOffset : readERealPair l g t (.reg (shiftLayout 0).addReg) =
      some (.ok (((-reference : ℝ) : EReal), ((-reference : ℝ) : EReal))))
    (hAddr : ∀ q : Fin 4, t.regs (probabilityReg .first q) =
      some (b32 (probabilityAddress l g (stageOf warp) q)))
    (hSignalBase : t.regs 3217 = some (b32 (l.sharedBase + 8 * (stageOf warp).val)))
    (hRun : Run kernel Assumptions.all l g t ((X.tr g).drop j) none) :
    let weights := fun (q : Fin 4) i =>
      shiftedWeight p b h row (visitKey blocks 0 (32 * q.val + i)) reference
    let weights32 := fun i => shiftedWeight p b h row (visitKey blocks 0 i) reference
    let ack := waitLoc l g (stageOf warp) 3
    ∃ u barInst electInst leader failed,
      let post := if laneOf l g = leader then j + 11 else j + 10
      (∀ i : Fin 10, X.get (g, j + i.val) =
        (firstPublicationEvents l g (stageOf warp) weights barInst electInst leader)[i.val]?) ∧
      (laneOf l g = leader → X.get (g, j + 10) = some
        ⟨4867, .arrive (signalLoc l g (stageOf warp) 2) 0 1 true .cta⟩) ∧
      (X.tr g).drop post = List.replicate failed ⟨4874, .wait ack 0 false true .cta⟩ ++
        ⟨4874, .wait ack 0 true true .cta⟩ :: (X.tr g).drop (post + failed + 1) ∧
      At u 4877 (factsFrom firstTransitionRegs keep) ∧
      (∀ i < 128, u.regs (1231 + i) = some (fl (weights32 i))) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (post + failed + 1)) none := by
  obtain ⟨v, hV, hWords, hExps, hFrame, hTail⟩ := firstShiftedPacks (blocks := blocks) hp reference
    values scores ht hRead hSource hLogits hScale hOffset hRun
  have hKeep := publicationFrame hFrame
  have hVaddr (q : Fin 4) : v.regs (probabilityReg .first q) =
      some (b32 (probabilityAddress l g (stageOf warp) q)) := by
    exact (hKeep _ (by fin_cases q <;> decide)).trans (hAddr q)
  let regValue := fun r =>
    if r ∈ firstTransitionRegs then keep r
    else fl (shiftedWeight p b h row (visitKey blocks 0 (r - 1231)) reference)
  have hDis {r : Nat} (hr : r ∈ exponentLive) : r ∉ firstTransitionRegs := by
    have hb := mem_exponentLive.mp hr
    simp only [firstTransitionRegs, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hAt := hV.mono
    (G := tailCarry l warp .first (some regValue))
    ⟨(hKeep 1062 (by decide)).trans ht.2.2.2.2.1,
      (hKeep 2535 (by decide)).trans ht.2.2.2.2.2.1, holds_of_pointwise fun r hr => by
        rcases List.mem_append.mp hr with h | h
        · simpa only [regValue, ite_eq_left h] using
            (hKeep r (List.mem_append_right _ h)).trans
              (holds_mem hTransition (mem_factsFrom h))
        · have hRange := mem_exponentLive.mp h
          have he : 1231 + (r - 1231) = r := by omega
          rw [← he]
          have h' : 1231 + (r - 1231) ∉ firstTransitionRegs := he.symm ▸ hDis h
          simpa only [regValue, ite_eq_right h', Nat.add_sub_cancel_left] using
            hExps (r - 1231) (by omega)⟩
  obtain ⟨s, barInst, electInst, leader, hEvents, hElect, hS, hSTail⟩ :=
    firstPublicationProtocol hp warp (some regValue) _ hAt hWords hVaddr
      ((hKeep 3217 (by decide)).trans hSignalBase) hTail
  obtain ⟨failed, u, hAck, hU, hEnd⟩ := firstPublicationAck hp warp (some regValue) hS hSTail
  refine ⟨u, barInst, electInst, leader, failed, hEvents, hElect, hAck,
    hU.mono (holds_of_pointwise ?_), ?_, hEnd⟩
  · intro r hr
    have hMem : r ∈ tailLive .first := List.mem_append_left _ hr
    have h := holds_mem hU.2.2.2.2 (mem_factsFrom (val := regValue) hMem)
    simpa only [regValue, ite_eq_left hr] using h
  · intro i hi
    have hMem : 1231 + i ∈ exponentLive := mem_exponentLive.mpr (by omega)
    have hAll : 1231 + i ∈ tailLive .first := List.mem_append_right _ hMem
    have h := holds_mem hU.2.2.2.2 (mem_factsFrom (val := regValue) hAll)
    simpa only [regValue, ite_eq_right (hDis hMem), Nat.add_sub_cancel_left] using h

end
end PTX.Kernels.TmlFa4Fwd.Softmax
