-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.AlphaAt
public import Lemmas.Flow.SegQFJ

@[expose] public section

/-! # What the typed float windows of the data lanes need of the assumptions

`FloatPlain3 Assumptions.all L g a b` (`Lemmas/Flow/SegQFJ.lean`) for a stretch of pcs outside the
software `exp2` blocks and the single-instruction readings (pcs 600, 807, 2562). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Proof PTX.Flow PTX.Flow.TyG PTX.Assumption

variable {L : Launch} {g : Nat}

/-- The pc is none of the software `exp2` sites and none of the single-instruction readings'. -/
structure PlainPc (pc : Nat) : Prop where
  emu : Assumptions.emuSites.contains pc = false
  lg2 : pc ≠ 2562
  div : pc ≠ 600
  neg : pc ≠ 807

theorem plain_shape {t : TState} (h : PlainPc t.pc) {op : Op} (hop : PlainOp op) :
    ∀ x ∈ Assumptions.all, x.localRule L g t op = none := by
  obtain ⟨he, h1, h2, h3⟩ := h
  intro x hx
  by_cases hd : x ∈ Assumptions.all.drop 2
  · by_cases hc : ∃ c, op = .cvt c
    · obtain ⟨c, rfl⟩ := hc
      obtain ⟨c', k, w, h', hd'⟩ := hop.resolve_left (by simp) |>.resolve_left (by simp)
      obtain rfl : c = c' := by simpa using h'
      simp only [Assumptions.all, List.drop_succ_cons, List.drop_zero, List.mem_cons,
        List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | rfl | simp [Assumptions.lg2Exact, Assumptions.divFullExact,
          Assumptions.negExact, Assumptions.bf16Exact, hd']
    · exact other_rules_none h1 h2 h3 (fun c hc' => hc ⟨c, hc'⟩) x hd
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false, List.drop_succ_cons,
    List.drop_zero] at hx hd
  rcases hx with rfl | rfl | hx'
  · refine idealReal_localRule_none fun f hf => ?_
    rcases hop with ⟨i, rfl⟩ | ⟨m, rfl⟩ | ⟨c, k, w, rfl, hd'⟩
    · simp [FloatForm.ofOp] at hf
    · simp [FloatForm.ofOp] at hf
    · simp [FloatForm.ofOp, CvtInstr.widenF16?, CvtInstr.packF16?, hd'] at hf
  · refine approxExact_localRule_none fun f hf => ?_
    rcases hop with ⟨i, rfl⟩ | ⟨m, rfl⟩ | ⟨c, k, w, rfl, _⟩ <;> simp [ApproxForm.ofOp] at hf
  · exact absurd hx' hd

theorem decline_fma2_at {t : TState} (h : PlainPc t.pc) :
    DeclineAt Assumptions.all .fmaRnF32x2 L g t := by
  obtain ⟨he, h1, h2, h3⟩ := h
  intro op hf hn
  rw [(segFree he).exec rfl, execLocalRule_of_none]
  intro a ha
  by_cases hd : a ∈ Assumptions.all.drop 2
  · refine other_rules_none h1 h2 h3 (fun c hc => ?_) a hd
    subst hc
    simp only [FloatForm.ofOp] at hf
    split_ifs at hf <;> simp at hf
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false, List.drop_succ_cons,
    List.drop_zero] at ha hd
  rcases ha with rfl | rfl | ha'
  · simp only [Assumptions.idealArith, Assumption.idealReal, hf]
    split_ifs
    · exact hn
    · rfl
  · exact approxExact_localRule_none fun f' h' => by
      rw [approxForm_none_of_float hf] at h'; cases h'
  · exact absurd ha' hd

/-- The first assumption that takes `cvt.f32.bf16` is the exact reading of `bf16Exact`. -/
theorem widen_find {t : TState} {d r : Nat} :
    Assumptions.all.findSome? (fun x => x.localRule L g t (.cvt (widenBfC d (.reg r)))) =
      execWidenBf t d (.reg r) := by
  have h4 : Assumptions.lg2Exact.localRule L g t (.cvt (widenBfC d (.reg r))) = none := by
    simp [Assumptions.lg2Exact]
  have h5 : Assumptions.divFullExact.localRule L g t (.cvt (widenBfC d (.reg r))) = none := by
    simp [Assumptions.divFullExact]
  have h6 : Assumptions.negExact.localRule L g t (.cvt (widenBfC d (.reg r))) = none := by
    simp [Assumptions.negExact]
  have hb : Assumptions.bf16Exact.localRule L g t (.cvt (widenBfC d (.reg r))) =
      execWidenBf t d (.reg r) := by
    simp [Assumptions.bf16Exact, widenBfC, CvtInstr.plain, execWidenBf]
  have h1 : Assumptions.idealArith.localRule L g t (.cvt (widenBfC d (.reg r))) = none := by
    simp [Assumptions.idealArith, Assumption.idealReal, FloatForm.ofOp, widenBfC,
      CvtInstr.widenF16?, CvtInstr.packF16?]
  have h2 : Assumptions.approx.localRule L g t (.cvt (widenBfC d (.reg r))) = none := by
    simp [Assumptions.approx, Assumption.approxExact, ApproxForm.ofOp]
  have h3 : (Assumptions.swExp2 kernel).localRule L g t (.cvt (widenBfC d (.reg r))) = none :=
    rfl
  simp only [Assumptions.all, List.findSome?_cons, h1, h2, h3, h4, h5, h6, hb]
  cases execWidenBf t d (.reg r) <;> rfl

theorem widen_rules {a b : Nat} (h : ∀ pc, a ≤ pc → pc < b → PlainPc pc) :
    WidenRules Assumptions.all L g a b := by
  intro t ha hb d r
  have he := (h t.pc ha hb).emu
  exact ⟨fun e h' => by rw [(segFree he).exec rfl, execLocalRule, widen_find, h'],
    fun h' => by rw [(segFree he).exec rfl, execLocalRule, widen_find, h']⟩


theorem bra_none (t : TState) (x : Assumption) (target : Nat) (uni : Bool)
    (hx : x ∈ Assumptions.all) : x.localRule L g t (.bra target uni) = none := by
  simp only [Assumptions.all, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact idealReal_localRule_none fun f hf => by simp [FloatForm.ofOp] at hf
  · exact approxExact_localRule_none fun f hf => by simp [ApproxForm.ofOp] at hf
  all_goals first | rfl | simp [Assumptions.lg2Exact, Assumptions.divFullExact,
    Assumptions.negExact]

/-- **A stretch of the data lanes outside the software `exp2` blocks and the single-instruction
readings is plain for the typed float family with `ex2` and `setp`.** -/
theorem floatPlain3 {a b : Nat} (h : ∀ pc, a ≤ pc → pc < b → PlainPc pc) :
    FloatPlain3 Assumptions.all L g a b where
  plain :=
    { plain :=
        { shape := fun t h1 h2 _ hop x hx => plain_shape (h _ h1 h2) hop x hx
          segs := fun pc h1 h2 => segFree (h pc h1 h2).emu
          ideal := fun t h1 h2 =>
            have hp := h _ h1 h2
            ⟨⟨ideal_at (by simp) hp.emu, decline_at (by simp) hp.emu hp.lg2 hp.div hp.neg⟩,
              ⟨idealAt_head (by decide) (segFree hp.emu).tail, decline_fma2_at hp⟩⟩
          widen := widen_rules h
          bra := fun t x target uni hx => bra_none t x target uni hx }
      ideal2 := fun t h1 h2 =>
        have hp := h _ h1 h2
        ⟨forms_at (f := .min .f32) (by simp) hp.emu hp.lg2 hp.div hp.neg t rfl,
          forms_at (f := .fma .f32) (by simp) hp.emu hp.lg2 hp.div hp.neg t rfl⟩ }
  ideal3 := fun t h1 h2 =>
    have hp := h _ h1 h2
    ⟨ex2_at hp.emu hp.lg2 hp.div hp.neg,
      forms_at (f := .setp .f32) (by simp) hp.emu hp.lg2 hp.div hp.neg t rfl,
      forms_at (f := .setpInf .f32) (by simp) hp.emu hp.lg2 hp.div hp.neg t rfl⟩

end PTX.Kernels.InklingRelDecode.Proof.Lib
