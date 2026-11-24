-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionAll
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCounts
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionLoadValue

@[expose] public section

/-! # The Tensor Memory loads of the correction warps

Each load of the rescale (`rld`) and of the final normalization (`fld`) has the implicit
`tcgen05.wait::ld` (ASM-TCLD-DATAFLOW): its sub-step 0 loads the sixteen columns at the
address its register holds, writes them to its destinations and stays at the instruction; the
state at the wait (`rldW`, `fldW`) records the loaded values as the chunk `o`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- A load with the implicit wait from a state at its first sub-step: the event loads at the
address, and the state after it is at the same instruction, sub-step 1, with the
destinations holding the loaded values. -/
theorem load_core {L : Launch} {g pc ta a : Nat} {ds : List Nat} {t u : TState} {e : Event}
    {F : List (Nat × Value)} (hw : asms.any (·.tcLdWait pc) = true) (h : At t pc F)
    (hr : t.regs ta = some (b32 a)) (ha : a < 2 ^ 32)
    (hf : Fires pc (eventTmpl asms L g t (.tcLd ds ta)) e (some u)) :
    ∃ vals, vals.length = ds.length ∧ e = ⟨pc, .tc (.ld a vals .s32x32b)⟩ ∧ u.pc = pc ∧ u.sub = 1 ∧
      u.acc = [] ∧ u.fault = none ∧ u.regs = (setRegs t ds vals).regs := by
  obtain ⟨vals, hl, rfl, rfl⟩ := fires_tcLd_load (fun _ => by simp) (h.1 ▸ hw) h.2.1 hr ha hf
  obtain ⟨-, -, hacc, hfl⟩ := setRegs_skel (PTX.next t) ds vals
  exact ⟨vals, hl, rfl, h.1, rfl, hacc.trans h.2.2.1, hfl.trans h.2.2.2.1,
    setRegs_next_regs t ds vals⟩

/-- The address register of load `j` of stage `st` (rescale and final part alike). -/
def ldAddr (st : Fin 2) (j : Fin 8) : Nat :=
  if st.val = 0 then 630 + j.val else if j.val = 0 then 629 else 637 + j.val

/-- The instruction at `pc` is the load of `ds` from the address in `ta`. -/
def ldAt (pc : Nat) (ds : List Nat) (ta : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨none, .tcLd ds' ta'⟩ => ds' == ds && ta' == ta
  | _ => false

theorem ldAt_spec {pc ta : Nat} {ds : List Nat} (h : ldAt pc ds ta = true) :
    kernel.code[pc]? = some ⟨none, .tcLd ds ta⟩ := by
  unfold ldAt at h
  split at h
  · rename_i ds' ta' hc
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rw [hc, h.1, h.2]
  · cases h

set_option maxHeartbeats 4000000 in
theorem code_rld (st : Fin 2) (j : Fin 8) : kernel.code[(Site.rld st j).pc]? =
    some ⟨none, .tcLd (rldRegs (8 * st.val + j.val)) (ldAddr st j)⟩ := by
  apply ldAt_spec
  fin_cases st <;> fin_cases j <;> decide +kernel

set_option maxHeartbeats 4000000 in
theorem code_fld (st : Fin 2) (j : Fin 8) : kernel.code[(Site.fld st j).pc]? =
    some ⟨none, .tcLd (fldRegs (8 * st.val + j.val)) (ldAddr st j)⟩ := by
  apply ldAt_spec
  fin_cases st <;> fin_cases j <;> decide +kernel

set_option maxHeartbeats 4000000 in
theorem ldAddr_live (st : Fin 2) (j : Fin 8) : ldAddr st j ∈ Flow.live (Site.rld st j).pc ∧
    ldAddr st j ∈ Flow.live (Site.fld st j).pc := by
  fin_cases st <;> fin_cases j <;> exact ⟨by decide +kernel, by decide +kernel⟩

set_option maxHeartbeats 4000000 in
theorem ldAddr_val (L : Launch) (g : Nat) (d : D) (st : Fin 2) (j : Fin 8) :
    valueOf L g d (ldAddr st j) = b32 (tmem L g (256 + 128 * st.val + 16 * j.val)) := by
  fin_cases st <;> fin_cases j
  all_goals
    norm_num only [ldAddr]
    simp only [valueOf, values, chunkValues, loadValues, PTX.Flow.lookupLit, Option.getD_some]

theorem factsFrom_append (l l' : List Nat) (v : Nat → Value) :
    Flow.factsFrom (l ++ l') v = Flow.factsFrom l v ++ Flow.factsFrom l' v :=
  List.map_append ..

set_option maxHeartbeats 8000000 in
/-- The facts at the wait of a rescale load: its destinations hold the chunk, the other live
registers keep their values. -/
theorem rld_facts {L : Launch} {g : Nat} (st : Fin 2) (j : Fin 8) {i tt : Nat} {aw : Value}
    {a : ℝ} {o vals : List Value} {R R' : Nat → Option Value}
    (hS : Holds R (facts L g ⟨.rld st j, i, tt, aw, a, o⟩))
    (hframe : ∀ r, r ∉ rldRegs (8 * st.val + j.val) → R' r = R r)
    (hW : Holds R' (Flow.factsFrom (rldRegs (8 * st.val + j.val))
      (valueOf L g ⟨.rldW st j, i, tt, aw, a, vals⟩))) :
    Holds R' (facts L g ⟨.rldW st j, i, tt, aw, a, vals⟩) := by
  simp only [facts, factsFrom_append, holds_append, Site.extra] at hS ⊢
  refine ⟨?_, hW⟩
  have hS' := hS.1
  fin_cases st <;> fin_cases j
  all_goals (frame_fp hS', hframe; simp [Flow.factsFrom])

theorem rldRegs_ok (c : Fin 16) : (rldRegs c.val).length = 16 ∧ (rldRegs c.val).Nodup := by
  fin_cases c <;> decide

theorem fldRegs_ok (c : Fin 16) : (fldRegs c.val).length = 16 ∧ (fldRegs c.val).Nodup := by
  fin_cases c <;> decide

theorem tmem_lt (L : Launch) (g col : Nat) (h : col < 512) : tmem L g col < 2 ^ 32 := by
  have : kOf L g < 4 := Nat.mod_lt _ (by decide)
  simp only [tmem]
  omega

/-- **A rescale load**: it loads the stage's columns `256 + 128 st + 16 j …` and reaches its
implicit wait with the loaded values as the chunk. -/
theorem step_rld {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event} {ins : Instr}
    (st : Fin 2) (j : Fin 8) (hs : d.site = .rld st j) (hi : Inv L g d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    Ev L g d e ∧ Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans (code_rld st j))
  have hr := holds_mem h.2.2.2.2 (mem_factsFrom (List.mem_append_left _ (ldAddr_live st j).1))
  rw [ldAddr_val] at hr
  obtain ⟨vals, hl, rfl, hpc, hsub, hacc, hfl, hreg⟩ :=
    load_core (tcLdWait_rld st j) h hr (tmem_lt L g _ (by omega)) hf
  have hok := rldRegs_ok ⟨8 * st.val + j.val, by omega⟩
  refine ⟨⟨rfl, vals, rfl⟩, .inl (.inr ⟨⟨.rldW st j, i, tt, aw, a, vals⟩, u, by simp [next],
    .refl, ⟨hpc, hsub, hacc, hfl, ?_⟩, ⟨fun _ => hi.item rfl, fun h' => by simp [Site.inItem] at h',
      fun h' => by simp at h', fun _ => hi.trip rfl, fun _ => hi.alpha rfl⟩⟩)⟩
  rw [hreg]
  exact rld_facts st j h.2.2.2.2 (setRegs_other t _ vals)
    (holds_setRegs t _ vals _ hok.2 (by rw [hl]) (fun p hp =>
      rld_value L g _ ⟨8 * st.val + j.val, by omega⟩ p (by have := hok.1; simp at this; omega)))

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
