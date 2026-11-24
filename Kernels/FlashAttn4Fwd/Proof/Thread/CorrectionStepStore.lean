-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionStepLoad

@[expose] public section

/-! # The stores of the chunks

A rescale chunk's `tcgen05.st` writes the stage's columns at the address of the chunk's load
and continues at the next chunk's load or, after the last chunk, at the rescale's
`tcgen05.wait::st`. Each element of a final chunk's `st.shared.v4` writes its word and continues
at the next element, the chunk's second store, the next chunk's load or, after the last chunk,
the proxy fence. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- The instruction at `pc` is a `tcgen05.st` from the address in `ta`. -/
def stAt (pc ta : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨none, .tcSt ta' _⟩ => ta' == ta
  | _ => false

theorem stAt_spec {pc ta : Nat} (h : stAt pc ta = true) :
    ∃ ss, kernel.code[pc]? = some ⟨none, .tcSt ta ss⟩ := by
  unfold stAt at h
  split at h
  · rename_i ta' ss hc
    rw [beq_iff_eq] at h
    exact ⟨ss, by rw [hc, h]⟩
  · cases h

set_option maxHeartbeats 4000000 in
theorem code_rst (st : Fin 2) (j : Fin 8) :
    ∃ ss, kernel.code[(Site.rst st j).pc]? = some ⟨none, .tcSt (ldAddr st j) ss⟩ := by
  apply stAt_spec
  fin_cases st <;> fin_cases j <;> decide +kernel

set_option maxHeartbeats 4000000 in
theorem ldAddr_live_rst (st : Fin 2) (j : Fin 8) : ldAddr st j ∈ Flow.live (Site.rst st j).pc := by
  fin_cases st <;> fin_cases j <;> decide +kernel

/-- The site after a rescale store. -/
def afterRst (st : Fin 2) (j : Fin 8) : Site :=
  if h : j.val + 1 < 8 then .rld st ⟨j.val + 1, h⟩ else .rwait st

set_option maxHeartbeats 8000000 in
/-- **A rescale store**: the event stores the stage's columns; the next chunk's load or the
rescale's wait follows. -/
theorem step_rst {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (st : Fin 2) (j : Fin 8)
    (hs : d.site = .rst st j) (hi : Inv L g d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    Ev L g d e ∧ Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain ⟨ss, hcode⟩ := code_rst st j
  obtain rfl := Option.some.inj (hc.symm.trans hcode)
  have hr := holds_mem h.2.2.2.2 (mem_factsFrom (List.mem_append_left _ (ldAddr_live_rst st j)))
  rw [ldAddr_val] at hr
  obtain ⟨⟨vals, rfl⟩, rfl⟩ := fires_tcSt hr (tmem_lt L g _ (by omega)) hf
  refine ⟨⟨rfl, vals, rfl⟩, ?_⟩
  have hn : next L g ⟨.rst st j, i, tt, aw, a, o⟩ ⟨(Site.rst st j).pc,
      .tc (.st (tmem L g (256 + 128 * st.val + 16 * j.val)) vals .s32x32b)⟩ =
      some (some ⟨afterRst st j, i, tt, aw, a, o⟩) := by
    simp only [next, afterRst]
    split_ifs <;> rfl
  have hiv : Inv L g ⟨afterRst st j, i, tt, aw, a, o⟩ :=
    inv_same (d := ⟨.rst st j, i, tt, aw, a, o⟩) _ hi
      (by unfold afterRst; split_ifs <;> rfl) (.inl (by unfold afterRst; split_ifs <;> rfl))
      (fun _ => rfl) (fun _ => rfl)
      (fun hh => by unfold afterRst at hh; split_ifs at hh <;> simp at hh)
  refine step_of_run hn hiv (by unfold afterRst; split_ifs <;> rfl) ⟨0, ?_⟩
  fin_cases st <;> fin_cases j
  all_goals
    simp only [afterRst]
    corr_seg (At.next h) hpre

/-- The instruction at `pc` is a four-element `st.shared.v4.b32`. -/
def stvAt (pc : Nat) : Bool :=
  match kernel.code[pc]? with
  | some ⟨none, .mem
      { kind := .store, space := some (.shared .cta), sem := .weak, scope := none,
        elem := .int .b 32, vec := n, ext := .same, nc := false, noftz := false,
        hints := ⟨none, none, none, none, none⟩,
        addr := ⟨.reg _base 32, _off⟩, dsts := [], srcs := srcs, mmio := false }⟩ =>
    srcs.length == n && n == 4
  | _ => false

theorem stvAt_spec {pc : Nat} (h : stvAt pc = true) :
    ∃ base off srcs, kernel.code[pc]? = some ⟨none, .mem
      { kind := .store, space := some (.shared .cta), sem := .weak, elem := .int .b 32,
        vec := srcs.length, addr := ⟨.reg base 32, off⟩, srcs := srcs }⟩ ∧
      srcs.length = 4 := by
  unfold stvAt at h
  split at h
  · rename_i n base off srcs hc
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
    have h1 := beq_iff_eq.mp h1
    have h2 := beq_iff_eq.mp h2
    subst h1
    exact ⟨base, off, srcs, hc, h2⟩
  · cases h

set_option maxHeartbeats 4000000 in
theorem code_fst (st : Fin 2) (j : Fin 8) (h : Fin 2) (el : Fin 4) :
    ∃ base off srcs, kernel.code[(Site.fst st j h el).pc]? = some ⟨none, .mem
      { kind := .store, space := some (.shared .cta), sem := .weak, elem := .int .b 32,
        vec := srcs.length, addr := ⟨.reg base 32, off⟩, srcs := srcs }⟩ ∧
      srcs.length = 4 := by
  apply stvAt_spec
  simp only [Site.pc]
  fin_cases st <;> fin_cases j <;> fin_cases h <;> decide +kernel

/-- The site after the last element of a final store. -/
def afterFst (st : Fin 2) (j : Fin 8) (h : Fin 2) : Site :=
  if h.val = 0 then .fst st j 1 0 else if hj : j.val + 1 < 8 then .fld st ⟨j.val + 1, hj⟩
  else .fence st

set_option maxHeartbeats 8000000 in
/-- **An element of a final store**: the event writes; the next element, the second store, the
next chunk's load or the proxy fence follows. -/
theorem step_fst {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (st : Fin 2) (j : Fin 8) (h : Fin 2)
    (el : Fin 4) (hs : d.site = .fst st j h el) (hi : Inv L g d) (hpc : t.pc = d.site.pc)
    (hsub : t.sub = d.site.sub) (hacc : t.acc = []) (hfl : t.fault = none)
    (hF : Holds t.regs (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    Ev L g d e ∧ Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs hpc hsub hF hc hf hi ⊢
  subst hs
  obtain ⟨base, off, srcs, hcode, hlen⟩ := code_fst st j h el
  obtain rfl := Option.some.inj (hc.symm.trans hcode)
  obtain ⟨rfl, ac, bs, rfl⟩ := fires_stv_after (lsp := .shared)
    (by simp [MemAccess.rule, memTypeOk, DType.width, hlen])
    rfl hf
  refine ⟨⟨rfl, ac, bs, rfl⟩, ?_⟩
  have hiv : ∀ s : Site, s.inItem = true → s.inTrip = false → s.rescale = false →
      Inv L g ⟨s, i, tt, aw, a, o⟩ := fun s h1 h2 h3 =>
    inv_same (d := ⟨.fst st j h el, i, tt, aw, a, o⟩) s hi (by rw [h1]; rfl) (.inl h1)
      (fun h' => by rw [h2] at h'; cases h') (fun h' => by rw [h3] at h'; cases h')
      (fun hh => by rcases hh with rfl | rfl | ⟨_, rfl⟩ <;> cases h1)
  by_cases hel : el.val + 1 < 4
  · have hu := afterStore_mid (t := t) (srcs := srcs) (by rw [hlen, hsub]; exact hel)
    refine .inl (.inr ⟨⟨.fst st j h ⟨el.val + 1, hel⟩, i, tt, aw, a, o⟩, _, ?_, .refl,
      ⟨by rw [hu]; exact hpc, by rw [hu]; simp [hsub, Site.sub], by rw [hu]; exact hacc,
        by rw [hu]; exact hfl, by rw [hu]; exact hF⟩, hiv _ rfl rfl rfl⟩)
    simp [next, hel]
  · have hu := afterStore_last (t := t) (srcs := srcs) (by rw [hlen, hsub]; exact hel)
    have hel3 : el = 3 := by omega
    subst hel3
    have hat : At (afterStore t srcs) ((Site.fst st j h 3).pc + 1)
        (facts L g ⟨.fst st j h 3, i, tt, aw, a, o⟩) := by
      rw [hu]; exact ⟨by simp [hpc], rfl, hacc, hfl, hF⟩
    have hn : next L g ⟨.fst st j h 3, i, tt, aw, a, o⟩ ⟨(Site.fst st j h 3).pc, .wr ac bs⟩ =
        some (some ⟨afterFst st j h, i, tt, aw, a, o⟩) := by
      simp only [next, afterFst]
      split_ifs <;> rfl
    have hs3 : (afterFst st j h).inItem = true ∧ (afterFst st j h).inTrip = false ∧
        (afterFst st j h).rescale = false := by
      unfold afterFst; split_ifs <;> exact ⟨rfl, rfl, rfl⟩
    refine step_of_run hn (hiv _ hs3.1 hs3.2.1 hs3.2.2)
      (by unfold afterFst; split_ifs <;> rfl) ⟨0, ?_⟩
    fin_cases st <;> fin_cases j <;> fin_cases h
    all_goals
      simp only [afterFst]
      corr_seg hat hpre

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
