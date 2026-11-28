-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.Alpha
import Kernels.InklingRelDecode.Proof.Lib.Segments
import Lemmas.Flow.RcpCore
import Lemmas.Flow.Ex2Core

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section
variable {L : Launch} {g : Nat}

theorem forms_at {f : FloatForm} (hf : f ∈ idealForms) {pc : Nat}
    (emu : Assumptions.emuSites.contains pc = false) (h1 : pc ≠ 2562) (h2 : pc ≠ 600)
    (h3 : pc ≠ 807) : ∀ s : TState, s.pc = pc →
      IdealAt Assumptions.all f L g s ∧ DeclineAt Assumptions.all f L g s := by
  intro s hs
  subst hs
  exact ⟨ideal_at hf emu, decline_at hf emu h1 h2 h3⟩

/-- `ex2.approx.f32` outside the software `exp2` sites is the exact power of two on a finite
operand and takes the Core rule on another. -/
theorem ex2_at {t : TState} (emu : Assumptions.emuSites.contains t.pc = false)
    (h1 : t.pc ≠ 2562) (h2 : t.pc ≠ 600) (h3 : t.pc ≠ 807) :
    ApproxAt Assumptions.all (.ex2 .f32) L g t ∧
      ApproxDeclineAt Assumptions.all (.ex2 .f32) L g t := by
  have key : ∀ op, ApproxForm.ofOp op = some (.ex2 .f32) →
      execLocalA Assumptions.all L g t op = (execApproxExact t op).getD (execLocal L g t op) := by
    intro op hf
    rw [(segFree emu).exec rfl]
    have hi : Assumptions.idealArith.localRule L g t op = none :=
      idealReal_localRule_none fun f' h' => by
        rw [floatForm_none_of_approx hf] at h'; cases h'
    have ha : Assumptions.approx.localRule L g t op = execApproxExact t op :=
      approxExact_localRule_of hf (by simp)
    have rest := other_rules_none (L := L) (g := g) (t := t) (op := op) h1 h2 h3
      (fun c hc => by subst hc; simp [ApproxForm.ofOp] at hf)
    have hrest : (Assumptions.all.drop 2).findSome? (fun a => a.localRule L g t op) = none :=
      List.findSome?_eq_none_iff.mpr fun a ha => rest a ha
    show execLocalRule (Assumptions.idealArith :: Assumptions.approx :: Assumptions.all.drop 2)
      L g t op = _
    simp only [execLocalRule, List.findSome?_cons, hi, ha, hrest]
    cases execApproxExact t op <;> rfl
  exact ⟨fun op hf e he => by rw [key op hf, he]; rfl, fun op hf he => by rw [key op hf, he]; rfl⟩

/-- A `selp` is read by no assumption. -/
theorem selp_none {t : TState} (h1 : t.pc ≠ 2562) (h2 : t.pc ≠ 600) (h3 : t.pc ≠ 807)
    (i : IntInstr) : ∀ a ∈ Assumptions.all, a.localRule L g t (.int i) = none := by
  intro a ha
  by_cases hd : a ∈ Assumptions.all.drop 2
  · exact other_rules_none h1 h2 h3 (t := t) (op := .int i) (fun c hc => nomatch hc) a hd
  · simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false, List.drop_succ_cons,
      List.drop_zero] at ha hd
    rcases ha with rfl | rfl | ha'
    · exact idealReal_localRule_none fun f hf => by simp [FloatForm.ofOp] at hf
    · exact approxExact_localRule_none fun f hf => by simp [ApproxForm.ofOp] at hf
    · exact absurd ha' hd

/-- Item by item: the instructions of pcs 1839 to 1846 and the readings of the assumptions. -/
theorem alpha_at : OAt kernel Assumptions.all L g 1839 alphaItems := by
  have chk : ∀ pc ∈ List.range' 1839 8, Assumptions.emuSites.contains pc = false ∧
      pc ≠ 2562 ∧ pc ≠ 600 ∧ pc ≠ 807 := by decide +kernel
  have fm : ∀ {f} (pc : Nat), f ∈ idealForms → pc ∈ List.range' 1839 8 →
      ∀ s : TState, s.pc = pc → IdealAt Assumptions.all f L g s ∧
        DeclineAt Assumptions.all f L g s := fun pc hf hp => by
    obtain ⟨h1, h2, h3, h4⟩ := chk pc hp
    exact forms_at hf h1 h2 h3 h4
  have sf : ∀ pc ∈ List.range' 1839 8, SegFreePc Assumptions.all pc := fun pc hp =>
    segFree (chk pc hp).1
  have sl : ∀ (pc d p : Nat) (x y : Opnd), pc ∈ List.range' 1839 8 → ∀ s : TState,
      s.pc = pc → (OItem.selp d x y p).Rule Assumptions.all L g s := fun pc d p x y hp s hs => by
    subst hs
    obtain ⟨-, h2, h3, h4⟩ := chk _ hp
    exact selp_none (L := L) (g := g) h2 h3 h4 _
  have ex : ∀ pc ∈ List.range' 1839 8, ∀ s : TState, s.pc = pc →
      ApproxAt Assumptions.all (.ex2 .f32) L g s ∧
        ApproxDeclineAt Assumptions.all (.ex2 .f32) L g s := fun pc hp s hs => by
    subst hs
    obtain ⟨h1, h2, h3, h4⟩ := chk _ hp
    exact ex2_at h1 h2 h3 h4
  simp only [alphaItems, alphaRest, OAt]
  refine ⟨⟨by decide +kernel, sf _ (by decide), fun s hs => XItem.max3_rule
    (fm 1839 (by simp [idealForms]) (by decide) s hs).1
    (fm 1839 (by simp [idealForms]) (by decide) s hs).2⟩,
    ⟨by decide +kernel, sf _ (by decide), fm _ (by decide) (by decide)⟩,
    ⟨by decide +kernel, sf _ (by decide), sl _ _ _ _ _ (by decide)⟩,
    ⟨by decide +kernel, sf _ (by decide), fm _ (by decide) (by decide)⟩,
    ⟨by decide +kernel, sf _ (by decide), fm _ (by decide) (by decide)⟩,
    ⟨by decide +kernel, sf _ (by decide), fm _ (by decide) (by decide)⟩,
    ⟨by decide +kernel, sf _ (by decide), ex _ (by decide)⟩,
    ⟨by decide +kernel, sf _ (by decide), sl _ _ _ _ _ (by decide)⟩, trivial⟩

/-- The update of the running maximum at pc 949. -/
theorem upd_at : OAt kernel Assumptions.all L g 949 [.base updItem] :=
  ⟨⟨by decide +kernel, segFree (by decide +kernel), fun s hs =>
    selp_none (L := L) (g := g) (t := s) (by omega) (by omega) (by omega) _⟩, trivial⟩

/-- The scale word at pc 601. -/
theorem scale_at : OAt kernel Assumptions.all L g 601 [scaleItem] :=
  ⟨⟨by decide +kernel, segFree (by decide +kernel), fun s hs =>
    XItem.mul_rule (forms_at (f := .mul .f32) (by simp [idealForms]) (pc := 601)
      (by decide +kernel) (by omega) (by omega) (by omega) s hs).1
      (forms_at (f := .mul .f32) (by simp [idealForms]) (pc := 601)
      (by decide +kernel) (by omega) (by omega) (by omega) s hs).2 (by decide)⟩, trivial⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Lib
