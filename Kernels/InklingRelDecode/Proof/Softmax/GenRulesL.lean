-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.GenRulesE

@[expose] public section

/-! # The epilogue's pack of the accumulator words, for generated runs

The lemmas `Tools/out_gen.py` names in `Gen/Out/epilogue_pack.json`, at the pcs 2609 to 2641 of
the epilogue (outside the software `exp2` sites): no assumption reads a move or a pack. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax
open PTX PTX.Flow PTX.Proof PTX.Assumption

noncomputable section
variable {L : Launch} {g : Nat}

/-- A pc of the epilogue's pack of the accumulator words. -/
def epPc (pc : Nat) : Bool := decide (2609 ≤ pc ∧ pc < 2642)

theorem ep_emu {pc : Nat} (h : epPc pc = true) : Assumptions.emuSites.contains pc = false := by
  simp only [epPc, decide_eq_true_eq] at h
  rw [Bool.eq_false_iff]
  intro h'
  simp only [Assumptions.emuSites, List.contains_iff_mem, List.mem_map, List.mem_range] at h'
  obtain ⟨i, hi, he⟩ := h'
  omega

theorem epSegFree {pc : Nat} (h : epPc pc = true) : SegFreePc Assumptions.all pc :=
  Kernels.InklingRelDecode.Proof.segFree (ep_emu h)

theorem ep_ne {pc : Nat} (h : epPc pc = true) : pc ≠ 600 ∧ pc ≠ 807 ∧ pc ≠ 2562 := by
  simp only [epPc, decide_eq_true_eq] at h
  omega

/-- No assumption reads a move or a pack of the run. -/
theorem rule_moveL {it : OItem} (pc : Nat) (hp : epPc pc = true)
    (hk : (match it with
      | .mov .. | .movImm .. | .pack .. | .unpack .. | .selp .. => true
      | _ => false) = true := by exact rfl) :
    ∀ t : TState, t.pc = pc → (XItem.base it).Rule Assumptions.all L g t := by
  intro t ht
  cases it <;> simp at hk <;> exact noRuleAt pc (ep_ne hp) rfl t ht

end
end PTX.Kernels.InklingRelDecode.Proof.Softmax
