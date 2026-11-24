-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EpiBase
public import Lemmas.Assumption.Facts
public import Lemmas.Flow.SegDead
public import Lemmas.Flow.EventCont

@[expose] public section

/-! # The kernel's assumptions at the epilogue's code

At the epilogue (from pc 2563, after the single `lg2` of pc 2562) no assumption takes a segment,
and the only assumptions with a local rule are the readings of floating forms:

* integer, move, branch and other non-floating operations take the Core rule (`asms_none`);
* `mul.f32x2` and `setp.f32` are read as exact real arithmetic (`idealAt`), a form the ideal rule
  declines takes the Core rule (`declineAt`);
* `rcp.approx.f32` is the exact reciprocal (`approxAt_rcp`, ASM-APPROX). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epi
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- An operation that is neither a floating instruction nor a conversion takes the Core rule: no
assumption of the kernel has a local rule for it. -/
theorem asms_none {L : Launch} {g : Nat} {t : TState} {op : Op}
    (hf : ∀ f, op ≠ .float f) (hc : ∀ c, op ≠ .cvt c) :
    ∀ a ∈ asms, a.localRule L g t op = none := by
  have h1 : Assumption.FloatForm.ofOp op = none := by
    cases op <;> first | rfl | exact absurd rfl (hf _) | exact absurd rfl (hc _)
  have h2 : Assumption.ApproxForm.ofOp op = none := by
    cases op <;> first | rfl | exact absurd rfl (hf _)
  intro a ha
  simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  rotate_right
  · rfl
  · exact Assumption.idealReal_localRule_none fun f h => by rw [h1] at h; cases h
  · exact Assumption.approxExact_localRule_none fun f h => by rw [h2] at h; cases h
  · rfl
  all_goals first | rfl | simp only [Assumptions.lg2Exact, Assumptions.divFullExact,
    Assumptions.negExact, Assumptions.bf16Exact]
  all_goals cases op <;> first | exact absurd rfl (hf _) | exact absurd rfl (hc _) | simp

/-- No assumption of the kernel has a local rule for a move. -/
theorem asms_moves : CoreMoves asms := fun m _ _ _ => asms_none (by simp) (by simp)

/-- No assumption of the kernel names the pack of two words. -/
theorem asms_pack : NoPack asms := fun _ _ _ _ _ _ => asms_none (by simp) (by simp)

/-- Past the `lg2` of pc 2562 the single-instruction readings and the software `exp2` have no
local rule for an operation that is no conversion. -/
theorem asms_tail_none {L : Launch} {g : Nat} {t : TState} {op : Op} (h : 2563 ≤ t.pc)
    (hc : ∀ c, op ≠ .cvt c) :
    ∀ a ∈ asms.drop 2, a.localRule L g t op = none := by
  have hl : Assumptions.lg2Sites.contains t.pc = false := by
    simp [Assumptions.lg2Sites]; omega
  have hd : Assumptions.divFullSites.contains t.pc = false := by
    simp [Assumptions.divFullSites]; omega
  have hn : Assumptions.negSites.contains t.pc = false := by
    simp [Assumptions.negSites]; omega
  intro a ha
  simp only [asms, Assumptions.all, List.drop_succ_cons, List.drop_zero, List.mem_cons,
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

/-- `mul.f32x2` and `setp.f32` are exact at the epilogue's code. -/
theorem idealAt {f : Assumption.FloatForm} (hf : f = .mulF32x2 ∨ f = .setp .f32)
    {L : Launch} {g : Nat} {t : TState} (h : 2563 ≤ t.pc) : Assumption.IdealAt asms f L g t := by
  show Assumption.IdealAt (Assumption.idealReal _ _ _ :: _) f L g t
  exact Assumption.idealAt_head (by rcases hf with rfl | rfl <;> decide)
    (segFree (by omega)).tail

/-- At the epilogue's code a `mul.f32x2` or `setp.f32` the ideal rule declines takes the Core
rule. -/
theorem declineAt {f : Assumption.FloatForm} (hfs : f = .mulF32x2 ∨ f = .setp .f32)
    {L : Launch} {g : Nat} {t : TState} (h : 2563 ≤ t.pc) : DeclineAt asms f L g t := by
  intro op hf hn
  rw [(segFree (by omega)).exec rfl, execLocalRule_of_none]
  intro a ha
  by_cases hd : a ∈ asms.drop 2
  · refine asms_tail_none h (fun c hc => ?_) a hd
    subst hc
    rcases hfs with rfl | rfl <;>
    · simp only [Assumption.FloatForm.ofOp] at hf
      split_ifs at hf <;> simp at hf
  · simp only [asms, Assumptions.all, List.mem_cons, List.not_mem_nil, or_false,
      List.drop_succ_cons, List.drop_zero] at ha hd
    rcases ha with rfl | rfl | ha'
    · simp only [Assumptions.idealArith, Assumption.idealReal, hf]
      split_ifs
      · exact hn
      · rfl
    · exact Assumption.approxExact_localRule_none fun f' h' => by
        rw [Flow.approxForm_none_of_float hf] at h'; cases h'
    · exact absurd ha' hd

/-- At the epilogue's code `rcp.approx.f32` is the exact reciprocal (ASM-APPROX) on a finite
operand and takes the Core rule on another. -/
theorem approxAt_rcp {L : Launch} {g : Nat} {t : TState} (h : 2563 ≤ t.pc) :
    ApproxAt asms (.rcp .f32) L g t ∧ ApproxDeclineAt asms (.rcp .f32) L g t := by
  have key : ∀ op, Assumption.ApproxForm.ofOp op = some (.rcp .f32) →
      execLocalA asms L g t op = match Assumption.execApproxExact t op with
        | some r => r
        | none => execLocal L g t op := by
    intro op hf
    rw [(segFree (by omega)).exec rfl]
    have h1 : Assumptions.idealArith.localRule L g t op = none :=
      Assumption.idealReal_localRule_none fun f' h' => by
        rw [Flow.floatForm_none_of_approx hf] at h'; cases h'
    have h3 : Assumptions.approx.localRule L g t op = Assumption.execApproxExact t op :=
      Assumption.approxExact_localRule_of hf (by simp)
    have h4 := asms_tail_none (L := L) (g := g) (t := t) (op := op) h (fun c hc => by
      subst hc
      simp [Assumption.ApproxForm.ofOp] at hf)
    have h4a := h4 _ (show Assumptions.swExp2 kernel ∈ asms.drop 2 by simp [asms, Assumptions.all])
    have h4b := h4 _ (show Assumptions.lg2Exact ∈ asms.drop 2 by simp [asms, Assumptions.all])
    have h4c := h4 _ (show Assumptions.divFullExact ∈ asms.drop 2 by simp [asms, Assumptions.all])
    have h4d := h4 _ (show Assumptions.negExact ∈ asms.drop 2 by simp [asms, Assumptions.all])
    have h4e := h4 _ (show Assumptions.bf16Exact ∈ asms.drop 2 by simp [asms, Assumptions.all])
    simp only [execLocalRule, asms, Assumptions.all, List.findSome?, h1, h3, h4a, h4b, h4c,
      h4d, h4e]
    rcases hE : Assumption.execApproxExact t op with _ | r <;> rfl
  exact ⟨fun op hf e he => by rw [key op hf, he], fun op hf he => by rw [key op hf, he]⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Epi
