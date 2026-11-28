-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Lib.FloatRules
public import Lemmas.Flow.OutFloatItems

@[expose] public section

/-! # The epilogue's products, for generated runs

The lemmas `Tools/out_gen.py` names in `Gen/Out/epilogue_out.json`, at the pcs 2642 to 2673: the
packed product `mul.f32x2` (no rounding modifier) is read as exact real arithmetic. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow PTX.Proof PTX.Assumption

noncomputable section
variable {L : Launch} {g : Nat}

/-- A pc of the epilogue's packed products. -/
def epmPc (pc : Nat) : Bool := decide (2642 ≤ pc ∧ pc < 2674)

theorem epm_emu {pc : Nat} (h : epmPc pc = true) : Assumptions.emuSites.contains pc = false := by
  simp only [epmPc, decide_eq_true_eq] at h
  rw [Bool.eq_false_iff]
  intro h'
  simp only [Assumptions.emuSites, List.contains_iff_mem, List.mem_map, List.mem_range] at h'
  obtain ⟨i, hi, he⟩ := h'
  omega

theorem epmSegFree {pc : Nat} (h : epmPc pc = true) : SegFreePc Assumptions.all pc :=
  Kernels.InklingRelDecode.Proof.segFree (epm_emu h)

theorem mul2_ideal {t : TState} (h : Assumptions.emuSites.contains t.pc = false) :
    IdealAt Assumptions.all .mulF32x2 L g t := by
  show IdealAt (Assumption.idealReal _ _ _ :: _) .mulF32x2 L g t
  exact idealAt_head (by decide) (Kernels.InklingRelDecode.Proof.segFree h).tail

theorem mul2_decline {t : TState} (h : Assumptions.emuSites.contains t.pc = false)
    (h1 : t.pc ≠ 2562) (h2 : t.pc ≠ 600) (h3 : t.pc ≠ 807) :
    DeclineAt Assumptions.all .mulF32x2 L g t := by
  intro op hf hn
  have hnc : ∀ c, op ≠ .cvt c := by
    intro c hc
    subst hc
    simp only [FloatForm.ofOp] at hf
    split_ifs at hf <;> simp at hf
  have hrest := other_rules_none (L := L) (g := g) h1 h2 h3 hnc
  rw [(Kernels.InklingRelDecode.Proof.segFree h).exec rfl, execLocalRule_of_none]
  intro a ha
  by_cases hd : a ∈ Assumptions.all.drop 2
  · exact hrest a hd
  · have hhead : a = Assumptions.idealArith ∨ a = Assumptions.approx := by
      simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false,
        List.drop_succ_cons, List.drop_zero] at ha hd
      tauto
    rcases hhead with rfl | rfl
    · simp only [Assumptions.idealArith, Assumption.idealReal, hf]
      split_ifs
      · exact hn
      · rfl
    · exact approxExact_localRule_none fun f' h' => by
        rw [Flow.approxForm_none_of_float hf] at h'; cases h'

/-- The packed product of a run's item is read as exact. -/
theorem rule_mul2N {d a b : Nat} (pc : Nat) (hp : epmPc pc = true) : ∀ t : TState, t.pc = pc →
    (XItem.fn (fOp mul2NI d [.reg a, .reg b]) d (regsOf [.reg a, .reg b])
      (fF mul2NL [.reg a, .reg b])).Rule Assumptions.all L g t := by
  intro t ht
  have hp' := hp
  simp only [epmPc, decide_eq_true_eq] at hp'
  have he : Assumptions.emuSites.contains t.pc = false := ht ▸ epm_emu hp
  exact XItem.mul2N_rule (mul2_ideal he) (mul2_decline he (by omega) (by omega) (by omega))

end
end PTX.Kernels.InklingRelDecode.Proof.Lib
