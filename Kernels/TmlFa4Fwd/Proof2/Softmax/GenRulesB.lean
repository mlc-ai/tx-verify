-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.GenRules

@[expose] public section

/-! # The bias round's widening reading with a cheap site check

`rule_widen` takes `Assumptions.biasWidenSites.contains pc = true`, which the elaborator decides by
walking the 256-entry list; at the bias round's sites (the list's second half) that walk exceeds
the default recursion depth of a generated file. `rule_widenB` takes instead the arithmetic test
`widenB pc` (the bias round's products, pcs 5279 to 5534, widen at the first two pcs of every
four), whose membership in the list is checked once here by the kernel. The three- and
two-operand `max.f32` of the round's maximum are read ideally (`rule_max2`, `rule_max3`, lane L's
`XItem.max2_rule`/`max3_rule` on the kernel's ideal reading of `.max .f32`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax.Gen
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.TmlFa4Fwd

noncomputable section

variable {l : Launch} {g : Nat}

/-- The bias round's widening pcs: the first two of every four from pc 5279 to 5534. -/
def widenB (pc : Nat) : Bool :=
  decide (5279 ≤ pc) && decide (pc < 5535) && decide ((pc - 5279) % 4 < 2)

theorem widenB_all :
    (List.range' 5279 256).all (fun pc => !widenB pc || Assumptions.biasWidenSites.contains pc) =
      true := by
  decide +kernel

theorem widenB_mem {pc : Nat} (h : widenB pc = true) :
    Assumptions.biasWidenSites.contains pc = true := by
  have hr : pc ∈ List.range' 5279 256 := by
    simp only [widenB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact List.mem_range'_1.mpr ⟨h.1.1, by omega⟩
  have := List.all_eq_true.mp widenB_all pc hr
  simpa [h] using this

/-- `rule_widen` at a bias-round widening site. -/
theorem rule_widenB {d a : Nat} (pc : Nat) (hp : widenB pc = true)
    (hs : Assumptions.swExp2Sites.contains pc = false) :
    ∀ s : TState, s.pc = pc → (XItem.fn (widenOp d [a]) d [a] widenE).Rule
      Assumptions.all l g s :=
  rule_widen pc (widenB_mem hp) hs

/-- The ideal reading of `max.f32` at a pc outside the software-exponent sites. -/
theorem formsMax {t : TState} (hp : t.pc ∉ Assumptions.swExp2Sites) :
    IdealAt Assumptions.all (.max .f32) l g t ∧ DeclineAt Assumptions.all (.max .f32) l g t := by
  have hSeg := (Assumptions.numeric_segSites.pc hp)
  have hArith : FloatForm.max .f32 ∈ Assumptions.arithScope.float := by decide
  refine ⟨?_, ?_⟩
  · intro op ho result hr
    rw [Assumptions.execLocalA_all_eq_numeric]
    exact (idealAt_head hArith hSeg.tail : IdealAt Assumptions.numeric _ l g t) op ho result hr
  · intro op ho hr
    rw [Assumptions.execLocalA_all_eq_numeric]
    apply declineAt_head _ hSeg.tail op ho hr
    intro a ha op ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · apply approxExact_localRule_none
      intro x hx
      rw [approxForm_none_of_float ho] at hx
      cases hx
    · have hLog : Assumptions.lg2Operands op = none := by
        cases op <;> try rfl
        rename_i i
        cases h : i.op <;> simp [Assumptions.lg2Operands, h]
        simp [FloatForm.ofOp, h] at ho
      simp [Assumptions.lg2, hLog]
    · cases op <;> try rfl
      simp only [FloatForm.ofOp] at ho
      split_ifs at ho <;> cases ho
    · rfl

theorem rule_max2 {d a b : Nat} (pc : Nat)
    (hp : Assumptions.swExp2Sites.contains pc = false) :
    ∀ s : TState, s.pc = pc → (XItem.fn (maxOp d [a, b]) d [a, b] maxE).Rule
      Assumptions.all l g s :=
  fun _ h => have hf := formsMax (off h hp); XItem.max2_rule hf.1 hf.2

theorem rule_max3 {d a b c : Nat} (pc : Nat)
    (hp : Assumptions.swExp2Sites.contains pc = false) :
    ∀ s : TState, s.pc = pc → (XItem.fn (maxOp d [a, b, c]) d [a, b, c] maxE).Rule
      Assumptions.all l g s :=
  fun _ h => have hf := formsMax (off h hp); XItem.max3_rule hf.1 hf.2

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax.Gen
