-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionStepLoad

@[expose] public section

/-! # The Tensor Memory loads of the final normalization

As the rescale loads (`CorrectionStepLoad`): each final load loads the stage's columns and
reaches its implicit wait with the loaded values as the chunk `o`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

set_option maxHeartbeats 8000000 in
/-- The facts at the wait of a final load: its destinations hold the chunk, the other live
registers keep their values. -/
theorem fld_facts {L : Launch} {g : Nat} (st : Fin 2) (j : Fin 8) {i tt : Nat} {aw : Value}
    {a : ℝ} {o vals : List Value} {R R' : Nat → Option Value}
    (hS : Holds R (facts L g ⟨.fld st j, i, tt, aw, a, o⟩))
    (hframe : ∀ r, r ∉ fldRegs (8 * st.val + j.val) → R' r = R r)
    (hW : Holds R' (Flow.factsFrom (fldRegs (8 * st.val + j.val))
      (valueOf L g ⟨.fldW st j, i, tt, aw, a, vals⟩))) :
    Holds R' (facts L g ⟨.fldW st j, i, tt, aw, a, vals⟩) := by
  simp only [facts, factsFrom_append, holds_append, Site.extra] at hS ⊢
  refine ⟨?_, hW⟩
  have hS' := hS.1
  fin_cases st <;> fin_cases j
  all_goals (frame_fp hS', hframe; simp [Flow.factsFrom])

/-- **A final load**: it loads the stage's columns `256 + 128 st + 16 j …` and reaches its
implicit wait with the loaded values as the chunk. -/
theorem step_fld {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event} {ins : Instr}
    (st : Fin 2) (j : Fin 8) (hs : d.site = .fld st j) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    Ev L g d e ∧ Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans (code_fld st j))
  have hr := holds_mem h.2.2.2.2 (mem_factsFrom (List.mem_append_left _ (ldAddr_live st j).2))
  rw [ldAddr_val] at hr
  obtain ⟨vals, hl, rfl, hpc, hsub, hacc, hfl, hreg⟩ :=
    load_core (tcLdWait_fld st j) h hr (tmem_lt L g _ (by omega)) hf
  have hok := fldRegs_ok ⟨8 * st.val + j.val, by omega⟩
  refine ⟨⟨rfl, vals, rfl⟩, .inl (.inr ⟨⟨.fldW st j, i, tt, aw, a, vals⟩, u, by simp [next],
    .refl, ⟨hpc, hsub, hacc, hfl, ?_⟩, ⟨fun _ => hi.item rfl, fun h' => by simp [Site.inItem] at h',
      fun h' => by simp at h', fun h' => by simp [Site.inTrip] at h',
      fun h' => by simp [Site.rescale] at h'⟩⟩)⟩
  rw [hreg]
  exact fld_facts st j h.2.2.2.2 (setRegs_other t _ vals)
    (holds_setRegs t _ vals _ hok.2 (by rw [hl]) (fun p hp =>
      fld_value L g _ ⟨8 * st.val + j.val, by omega⟩ p (by have := hok.1; simp at this; omega)))

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
