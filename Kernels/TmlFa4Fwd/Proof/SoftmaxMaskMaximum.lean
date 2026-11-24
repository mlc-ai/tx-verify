-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxMaskTrace
public import Kernels.TmlFa4Fwd.Proof.SoftmaxRepeatedMax

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Flow PTX.Proof

noncomputable section

/-- Scalar register for a column in the first-round causal mask. -/
def firstMaskScalarReg (col : Nat) : Nat :=
  let pair := firstMaskPairRegs (col / 32) (col % 32 / 2)
  if col % 2 = 0 then pair.low else pair.high

theorem firstMaskScalarRegisters :
    (List.range 128).map firstMaskScalarReg = firstMaxInputs := by kernel_rfl

private theorem firstMaxInputsNodup : firstMaxInputs.Nodup := by decide +kernel

private theorem firstMaxGet {col : Nat} (hc : col < 128) :
    firstMaxInputs[col]? = some (firstMaskScalarReg col) := by
  rw [← firstMaskScalarRegisters, List.getElem?_map, List.getElem?_range hc]
  rfl

private theorem firstMaskScalar_mem {col : Nat} (hc : col < 128) :
    firstMaskScalarReg col ∈ firstMaxInputs := List.mem_of_getElem? (firstMaxGet hc)

private theorem firstMaskScalar_index {col : Nat} (hc : col < 128) :
    firstMaxInputs.idxOf (firstMaskScalarReg col) = col := by
  have hLength : firstMaxInputs.length = 128 := by
    rw [← firstMaskScalarRegisters, List.length_map, List.length_range]
  have hIdx : col < firstMaxInputs.length := hLength ▸ hc
  have hGet := firstMaxGet hc
  rw [List.getElem?_eq_getElem hIdx, Option.some.injEq] at hGet
  rw [← hGet, firstMaxInputsNodup.idxOf_getElem]

/-- The audited scalar register table connects the causal mask's two outputs per pair to
the column order consumed by both the first maximum and the following affine shift. -/
theorem firstMaskOutputColumn {t : TState} {score : Nat → Option ℝ}
    (hs : ∀ group : Fin 4, firstMaskOutputs t group score) {col : Nat} (hc : col < 128) :
    t.regs (firstMaskScalarReg col) = some (scoreValue (score col)) := by
  let group : Fin 4 := ⟨col / 32, by omega⟩
  let pair := col % 32 / 2
  have hPair : pair < 16 := by unfold pair; omega
  obtain ⟨hLo, hHi⟩ := hs group pair hPair
  unfold firstMaskScalarReg
  split
  · have he : 32 * group.val + 2 * pair = col := by dsimp [group, pair]; omega
    rw [he] at hLo
    exact hLo
  · have he : 32 * group.val + 2 * pair + 1 = col := by dsimp [group, pair]; omega
    rw [he] at hHi
    exact hHi

private theorem firstMaxScalarsKept :
    firstMaxInputs.all (fun r => !(rWrites (firstMaxItems.map MaxItem.item)).contains r) =
      true := by
  decide +kernel

private theorem scoreReal_injective : Function.Injective scoreReal := by
  intro a b hab
  cases a <;> cases b <;> simp_all [scoreReal]

/-- The 66 decoded reductions store the maximum of all masked logits and preserve the
scalar inputs needed by the subsequent affine shift. -/
theorem firstMaskedMaxLocal {l : Launch} {g : Nat} {t : TState}
    (score : Nat → Option ℝ)
    (ht : At t 4329 []) (hs : ∀ group : Fin 4, firstMaskOutputs t group score) :
    ∃ u, At u 4395 [(7256, scoreValue (scoreMax score (List.range 128)))] ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l g) t u ∧
      (∀ group : Fin 4, firstMaskOutputs u group score) ∧
      ∀ r ∉ rWrites (firstMaxItems.map MaxItem.item), u.regs r = t.regs r := by
  let stored : Nat → Option ℝ := fun r => score (firstMaxInputs.idxOf r)
  have input (r : Nat) (hm : r ∈ firstMaxInputs) : t.regs r = some (scoreValue (stored r)) := by
    rw [← firstMaskScalarRegisters, List.mem_map] at hm
    obtain ⟨col, hc, rfl⟩ := hm
    have hc' := List.mem_range.mp hc
    simpa only [stored, firstMaskScalar_index hc'] using firstMaskOutputColumn hs hc'
  obtain ⟨u, mx, hu, hur, hMax, hKeep⟩ := firstMaxLocal stored ht input
  have hSem (v : EReal) : scoreReal mx ≤ v ↔ ∀ col < 128, scoreReal (score col) ≤ v := by
    rw [hMax]
    constructor
    · intro h col hc
      simpa only [stored, firstMaskScalar_index hc] using h _ (firstMaskScalar_mem hc)
    · intro h r hr
      rw [← firstMaskScalarRegisters, List.mem_map] at hr
      obtain ⟨col, hc, rfl⟩ := hr
      have hc' := List.mem_range.mp hc
      simpa only [stored, firstMaskScalar_index hc'] using h col hc'
  have hSpec (v : EReal) : scoreReal (scoreMax score (List.range 128)) ≤ v ↔
      ∀ col < 128, scoreReal (score col) ≤ v := by
    simpa only [scoreMax, List.mem_range] using maxScore_mem (List.range 128) score v
  have he : mx = scoreMax score (List.range 128) := scoreReal_injective (le_antisymm
    ((hSem _).2 ((hSpec _).1 le_rfl)) ((hSpec _).2 ((hSem _).1 le_rfl)))
  refine ⟨u, he ▸ hu, hur, fun group pair hp => ?_, hKeep⟩
  obtain ⟨hLo, hHi⟩ := hs group pair hp
  have hg := group.isLt
  have hRegLo :
      firstMaskScalarReg (32 * group.val + 2 * pair) = (firstMaskPairRegs group pair).low := by
    have hGroup : (32 * group.val + 2 * pair) / 32 = group.val := by omega
    have hPair : (32 * group.val + 2 * pair) % 32 / 2 = pair := by omega
    have hEven : (32 * group.val + 2 * pair) % 2 = 0 := by omega
    simp only [firstMaskScalarReg, hGroup, hPair, ite_eq_left hEven]
  have hRegHi :
      firstMaskScalarReg (32 * group.val + 2 * pair + 1) =
        (firstMaskPairRegs group pair).high := by
    have hGroup : (32 * group.val + 2 * pair + 1) / 32 = group.val := by omega
    have hPair : (32 * group.val + 2 * pair + 1) % 32 / 2 = pair := by omega
    have hOdd : (32 * group.val + 2 * pair + 1) % 2 = 1 := by omega
    simp only [firstMaskScalarReg, hGroup, hPair, hOdd, Nat.one_ne_zero, ite_false]
  have hNot (r : Nat) (hm : r ∈ firstMaxInputs) :
      r ∉ rWrites (firstMaxItems.map MaxItem.item) := by
    simpa only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] using
      List.all_eq_true.mp firstMaxScalarsKept r hm
  refine ⟨(hKeep _ (hNot _ ?_)).trans hLo, (hKeep _ (hNot _ ?_)).trans hHi⟩
  · rw [← hRegLo]
    exact firstMaskScalar_mem (by omega)
  · rw [← hRegHi]
    exact firstMaskScalar_mem (by omega)

/-- The local replay continues a fully recorded lane trace. -/
theorem firstMaskedMaxInPrefix {l : Launch} {g : Nat} {t : TState} {es : List Event}
    {ending : Option TState}
    (score : Nat → Option ℝ)
    (ht : At t 4329 []) (hs : ∀ group : Fin 4, firstMaskOutputs t group score)
    (hr : Run kernel Assumptions.all l g t es ending) (hne : es ≠ []) :
    ∃ u, At u 4395 [(7256, scoreValue (scoreMax score (List.range 128)))] ∧
      Run kernel Assumptions.all l g u es ending ∧
      (∀ group : Fin 4, firstMaskOutputs u group score) ∧
      ∀ r ∉ rWrites (firstMaxItems.map MaxItem.item), u.regs r = t.regs r := by
  obtain ⟨u,hU,hLocal,hMax,hFrame⟩ := firstMaskedMaxLocal score ht hs
  exact ⟨u,hU,hr.after_local_nonempty hLocal hne,hMax,hFrame⟩

/-- The local replay continues a fully recorded lane trace. -/
theorem firstMaskedMaxTrace {l : Launch} {g : Nat} {t : TState} {es : List Event}
    (score : Nat → Option ℝ)
    (ht : At t 4329 []) (hs : ∀ group : Fin 4, firstMaskOutputs t group score)
    (hr : Run kernel Assumptions.all l g t es none) :
    ∃ u, At u 4395 [(7256, scoreValue (scoreMax score (List.range 128)))] ∧
      Run kernel Assumptions.all l g u es none ∧
      (∀ group : Fin 4, firstMaskOutputs u group score) ∧
      ∀ r ∉ rWrites (firstMaxItems.map MaxItem.item), u.regs r = t.regs r := by
  obtain ⟨u,hU,hLocal,hMax,hFrame⟩ := firstMaskedMaxLocal score ht hs
  exact ⟨u,hU,hr.after_local hLocal,hMax,hFrame⟩

end
end PTX.Kernels.TmlFa4Fwd.Softmax
