-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.Segments
public import Lemmas.Flow.MaxCore

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Proof PTX.Flow PTX.Assumption
variable {L : Launch} {g : Nat}

/-- The floating forms the kernel's local runs use that the ideal assumption reads as exact. -/
abbrev idealForms : List Assumption.FloatForm :=
  [.fma .f32, .min .f32, .setp .f32, .max .f32, .mul .f32, .subRn .f32, .setpInf .f32,
    .add .f32, .addRnF32x2]

/-- At a pc outside the software `exp2` instances `fma.f32`, `min.f32`, `setp.f32` and the other
`idealForms` are read as exact. -/
theorem ideal_at {f : Assumption.FloatForm} (hf : f ∈ idealForms)
    {t : TState} (h : Assumptions.emuSites.contains t.pc = false) :
    Assumption.IdealAt Assumptions.all f L g t := by
  show Assumption.IdealAt (Assumption.idealReal _ _ _ :: _) f L g t
  exact Assumption.idealAt_head (by
    simp only [idealForms,List.mem_cons,List.not_mem_nil,or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (segFree h).tail

/-- The assumptions after the first two have no local rule for an operation that is no conversion
at a pc that is none of the single-instruction readings' sites. -/
theorem other_rules_none {t : TState} {op : Op} (h1 : t.pc ≠ 2562) (h2 : t.pc ≠ 600)
    (h3 : t.pc ≠ 807) (hc : ∀ c, op ≠ .cvt c) :
    ∀ a ∈ Assumptions.all.drop 2, a.localRule L g t op = none := by
  have hl : Assumptions.lg2Sites.contains t.pc = false := by
    simp [Assumptions.lg2Sites]; omega
  have hd : Assumptions.divFullSites.contains t.pc = false := by
    simp [Assumptions.divFullSites]; omega
  have hn : Assumptions.negSites.contains t.pc = false := by
    simp [Assumptions.negSites]; omega
  intro a ha
  simp only [Assumptions.all, List.drop_succ_cons, List.drop_zero, List.mem_cons,
    List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  rotate_right
  · rfl
  · rfl
  · simp only [Assumptions.lg2Exact, hl]; simp
  · simp only [Assumptions.divFullExact, hd]; simp
  · simp only [Assumptions.negExact, hn]; simp
  · simp only [Assumptions.bf16Exact]
  · rfl
  · rfl
  · rfl

/-- An `fma.f32`, `min.f32` or `setp.f32` that the ideal rule declines takes the Core rule, at a
pc that is no software `exp2` instance and no single-instruction reading's site. -/
theorem decline_at {f : Assumption.FloatForm} (hfs : f ∈ idealForms) {t : TState}
    (h : Assumptions.emuSites.contains t.pc = false) (h1 : t.pc ≠ 2562) (h2 : t.pc ≠ 600)
    (h3 : t.pc ≠ 807) : DeclineAt Assumptions.all f L g t := by
  intro op hf hn
  rw [(segFree h).exec rfl, execLocalRule_of_none]
  intro a ha
  by_cases hd : a ∈ Assumptions.all.drop 2
  · refine other_rules_none h1 h2 h3 (fun c hc => ?_) a hd
    subst hc
    simp only [idealForms,List.mem_cons,List.not_mem_nil,or_false] at hfs
    rcases hfs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp only [Assumption.FloatForm.ofOp] at hf
      split_ifs at hf <;> simp at hf
  · simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false,
      List.drop_succ_cons, List.drop_zero] at ha hd
    rcases ha with rfl | rfl | ha'
    · simp only [Assumptions.idealArith, Assumption.idealReal, hf]
      split_ifs
      · exact hn
      · rfl
    · exact Assumption.approxExact_localRule_none fun f' h' => by
        rw [Flow.approxForm_none_of_float hf] at h'; cases h'
    · exact absurd ha' hd

end PTX.Kernels.InklingRelDecode.Proof.Lib
