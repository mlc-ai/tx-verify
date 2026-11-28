-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Lib.FloatRules
public import Lemmas.Flow.HavocTyped
public import Lemmas.Flow.TypedMoveF

@[expose] public section

/-! # No assumption touches the prologue's plain stretches

`Havoc.PlainRules` and `Havoc.PlainSegs` of `Assumptions.all` over the prologue's pcs 27 to 573: the
typed crossing (`Lemmas/Flow/HavocTyped.lean`) needs that no assumption's local rule takes an
integer, a move or an integer conversion there, and that no assumption takes a segment. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
open PTX PTX.Proof PTX.Flow PTX.Flow.Havoc PTX.Flow.Tagged PTX.Assumption
open PTX.Kernels.InklingRelDecode.Proof.Lib

variable {L : Launch} {g : Nat}

/-- An instruction the typed run accepts is an integer, a move or an integer conversion. -/
theorem absOp_shape {env : Env} {op : Op} (h : (absOp env op).isSome) : TyG.PlainOp op := by
  cases op <;> simp only [absOp, Option.isSome_none, Bool.false_eq_true] at h
  · exact .inl ⟨_, rfl⟩
  · exact .inr (.inl ⟨_, rfl⟩)
  · rename_i c
    obtain ⟨dst, src, rnd, ftz, sat, relu, satfinite, pzo, scaled, pack, d', ext, srcs⟩ := c
    unfold absCvt at h
    simp only at h
    split at h
    · rename_i k w _ _ _
      exact .inr (.inr ⟨_, k, w, rfl, rfl⟩)
    · simp at h

private theorem form_none {op : Op} (h : TyG.PlainOp op) :
    FloatForm.ofOp op = none ∧ ApproxForm.ofOp op = none := by
  rcases h with ⟨i, rfl⟩ | ⟨m, rfl⟩ | ⟨c, k, w, rfl, hd⟩
  · simp [FloatForm.ofOp, ApproxForm.ofOp]
  · simp [FloatForm.ofOp, ApproxForm.ofOp]
  · simp [FloatForm.ofOp, ApproxForm.ofOp, CvtInstr.widenF16?, CvtInstr.packF16?, hd]

private theorem emu_free {pc : Nat} (hb : pc < 574) : Assumptions.emuSites.contains pc = false := by
  rw [Bool.eq_false_iff]
  intro h
  simp only [Assumptions.emuSites, List.contains_iff_mem, List.mem_map, List.mem_range] at h
  obtain ⟨i, hi, he⟩ := h
  omega

/-- The other assumptions take no conversion to an integer. -/
private theorem cvt_none {t : TState} {c : CvtInstr} {k : IType} {w : Nat} (hd : c.dst = .int k w) :
    ∀ x ∈ Assumptions.all.drop 2, x.localRule L g t (.cvt c) = none := by
  intro x hx
  simp only [Assumptions.all, List.drop_succ_cons, List.drop_zero, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl := hx
  all_goals first | rfl | simp [Assumptions.lg2Exact, Assumptions.divFullExact,
    Assumptions.negExact, Assumptions.bf16Exact, hd]

/-- No assumption takes an operation of no float form when the last nine do not. -/
theorem rules_none {t : TState} {op : Op} (hf : FloatForm.ofOp op = none)
    (hap : ApproxForm.ofOp op = none)
    (h3 : ∀ x ∈ Assumptions.all.drop 2, x.localRule L g t op = none) :
    ∀ x ∈ Assumptions.all, x.localRule L g t op = none := by
  intro x hx
  have hx2 : x = Assumptions.all[0] ∨ x = Assumptions.all[1] ∨ x ∈ Assumptions.all.drop 2 := by
    simpa [Assumptions.all] using hx
  rcases hx2 with rfl | rfl | hx
  · exact idealReal_localRule_none fun f hf' => by simp [hf] at hf'
  · exact approxExact_localRule_none fun f hf' => by simp [hap] at hf'
  · exact h3 x hx

/-- No assumption takes an integer, a move or an integer conversion at a pc below 574. -/
theorem plain_none {t : TState} (hb : t.pc < 574) {op : Op} (h : TyG.PlainOp op) :
    ∀ x ∈ Assumptions.all, x.localRule L g t op = none := by
  obtain ⟨hf, hap⟩ := form_none h
  refine rules_none hf hap ?_
  rcases h with ⟨i, rfl⟩ | ⟨m, rfl⟩ | ⟨c, k, w, rfl, hd⟩
  · exact other_rules_none (by omega) (by omega) (by omega) (by simp)
  · exact other_rules_none (by omega) (by omega) (by omega) (by simp)
  · exact cvt_none hd

/-- **The prologue's pcs are plain for the typed crossing.** -/
theorem plainRules_pro {a b : Nat} (hb : b ≤ 574) : PlainRules Assumptions.all L g a b := by
  intro t _ htb op ⟨env, hop⟩ x hx
  exact plain_none (by omega) (absOp_shape hop) x hx

theorem plainSegs_pro {a b : Nat} (hb : b ≤ 574) : PlainSegs Assumptions.all a b :=
  fun pc _ h => segFree (emu_free (pc := pc) (by omega))

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Strict
