-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.Thread.SiteTmpl
public import Kernels.RmsNorm.Proof.Thread.StepVec

@[expose] public section

/-! # The stores

Every element of a vector store before the last moves to the next element. After the last, the
code continues to the next site: the staging stores to the next store or the next input load,
the second staging store of tile 1 sets the shuffle constants of the butterfly, the output
stores reach the next tile's weight load or the row's last barrier. Lane 0's store of its warp's
sum and thread 0's store of the total reach the barrier after them. -/

namespace PTX.Kernels.RmsNorm.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

local notation "Prod" => [Assumptions.idealArith, Assumptions.exactApprox]

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- A vector store step: an element before the last, or the last with continuation `hlast`. -/
theorem step_vstore {d d' : D} {t u : TState} {e : Event} {a : Acc} {bs : List Byte}
    {srcs : List Opnd} {pc : Nat} (hv : d.site.vec = true) (hvl : d.site.vload = false)
    (hn : ∀ e, next P g d e = storeNext d d') (hi : Inv P g d) (h : (code P L g).AtD d t)
    (hsrc : srcs.length = 4)
    (hf : Fires pc (.write a bs (afterStore t srcs)) e (some u))
    (hlast : d.sub = 3 → d.acc = [] → At u (d.site.pc + 1) (factsAt P g d.site.pc d) →
      ∃ t', Relation.ReflTransGen (Tau kernel Prod L g) u t' ∧ (code P L g).AtD d' t' ∧
        Inv P g d') : Cont P L g d e u := by
  have hlt : d.sub < 4 := hi.sub.1 hv
  have hacc : d.acc = [] := List.eq_nil_of_length_eq_zero (by simpa [hvl] using hi.acc)
  by_cases hmid : d.sub + 1 < 4
  · exact step_store_mid hv hvl hn hi h hsrc hmid hf
  have h3 : d.sub = 3 := by omega
  obtain ⟨-, hu⟩ := store_last h hsrc h3 hacc hf
  obtain ⟨t', hl, ha, hi'⟩ := hlast h3 hacc hu
  exact .inl ⟨d', t', by rw [hn]; simp [storeNext, h3], hl, ha, hi'⟩

theorem inv_vec_next {d : D} {s : Site} (hi : Inv P g d) (hv : s.vec = true)
    (hrow : d.site.inRow = true) (hb : ∀ k, s ≠ .bfa k ∧ s ≠ .bfb k)
      (h1 : s ≠ .ldws ∧ s ≠ .stts ∧ s ≠ .stws)
    (h2 : s ≠ .ldsa0 ∧ s ≠ .ldsb0 ∧ s ≠ .ldsa1 ∧ s ≠ .ldsb1) (hacc : d.acc = [])
    (rw : List Value) :
    Inv P g { d with site := s, sub := 0, raw := rw } := by
  refine ⟨⟨fun _ => by simp, fun h => by simp_all⟩, by simp [hacc], fun _ => hi.row hrow,
    fun h => by simp only at h; subst h; simp [Site.vec] at hv, fun k h => absurd h (hb k).1,
                  fun k h => absurd h (hb k).2, fun h => absurd h h1.1,
    fun h => absurd h h1.2.1, fun h => absurd h h1.2.2, fun h => absurd h (hb 0).2, ?_, ?_⟩
  · rintro (h | h) <;> simp_all
  · rintro (h | h) <;> simp_all

theorem step_stxa0 (hpre : Pre P L mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .stxa0) (hi : Inv P g d) (h : (code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Cont P L g d e u := by
  rw [tmpl_site hpre hi h hc] at hf
  simp only [siteTmpl, hs] at hf
  refine step_vstore (d' := { d with site := .stxa1, sub := 0 }) (by simp [hs, Site.vec])
    (by simp [hs, Site.vload]) (fun e => by simp only [next, hs]) hi h rfl hf ?_
  intro h3 hacc hu
  refine ⟨u, .refl, ⟨?_, ?_, ?_, hu.2.2.2.1, ?_⟩, ?_⟩
  · rw [hu.1, hs]; rfl
  · exact hu.2.1
  · exact hu.2.2.1.trans hacc.symm
  · rw [hs] at hu
    exact Flow.holds_factsFrom_mono hu.2.2.2.2 (by table_decide)
  · simpa using inv_vec_next (s := .stxa1) hi rfl (by simp [hs, Site.inRow])
      (by simp) (by simp) (by simp) hacc d.raw

theorem step_stxa1 (hpre : Pre P L mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .stxa1) (hi : Inv P g d) (h : (code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Cont P L g d e u := by
  rw [tmpl_site hpre hi h hc] at hf
  simp only [siteTmpl, hs] at hf
  refine step_vstore (d' := { d with site := .ldxb, sub := 0 }) (by simp [hs, Site.vec])
    (by simp [hs, Site.vload]) (fun e => by simp only [next, hs]) hi h rfl hf ?_
  intro h3 hacc hu
  have hrow := hi.row (by simp [hs, Site.inRow])
  rw [hs] at hu
  obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 1 u = some t' ∧
      At t' Site.ldxb.pc (facts P g ({ d with site := .ldxb, sub := 0 })) := by
    seg_fp hu using
      rms_values
      all_goals seg_close [row, off]
  refine ⟨t', run_rtg hr', atD_of rfl hacc ht', ?_⟩
  have := hacc
  simpa using inv_vec_next (s := .ldxb) hi rfl (by simp [hs, Site.inRow]) (by simp) (by simp)
    (by simp) hacc d.raw

theorem step_stxb0 (hpre : Pre P L mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .stxb0) (hi : Inv P g d) (h : (code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Cont P L g d e u := by
  rw [tmpl_site hpre hi h hc] at hf
  simp only [siteTmpl, hs] at hf
  refine step_vstore (d' := { d with site := .stxb1, sub := 0 }) (by simp [hs, Site.vec])
    (by simp [hs, Site.vload]) (fun e => by simp only [next, hs]) hi h rfl hf ?_
  intro h3 hacc hu
  have hrow := hi.row (by simp [hs, Site.inRow])
  rw [hs] at hu
  refine ⟨u, .refl, ⟨?_, ?_, ?_, hu.2.2.2.1, ?_⟩, ?_⟩
  · rw [hu.1]; rfl
  · exact hu.2.1
  · exact hu.2.2.1.trans hacc.symm
  · exact Flow.holds_factsFrom_mono hu.2.2.2.2 (by table_decide)
  · simpa using inv_vec_next (s := .stxb1) hi rfl (by simp [hs, Site.inRow])
      (by simp) (by simp) (by simp) hacc d.raw

theorem step_stxb1 (hpre : Pre P L mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .stxb1) (hi : Inv P g d) (h : (code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Cont P L g d e u := by
  rw [tmpl_site hpre hi h hc] at hf
  simp only [siteTmpl, hs] at hf
  refine step_vstore (d' := { d with site := .bfa 0, sub := 0 }) (by simp [hs, Site.vec])
    (by simp [hs, Site.vload]) (fun e => by simp only [next, hs]) hi h rfl hf ?_
  intro h3 hacc hu
  have hrow := hi.row (by simp [hs, Site.inRow])
  rw [hs] at hu
  obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 3 u = some t' ∧
      At t' (Site.bfa 0).pc (facts P g ({ d with site := .bfa 0, sub := 0 })) := by
    seg_fp hu using
      rms_values
      all_goals seg_close [row, off]
  refine ⟨t', run_rtg hr', atD_of rfl hacc ht', ?_⟩
  have := hacc
  inv_tac

theorem step_stoa (hpre : Pre P L mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .stoa) (hi : Inv P g d) (h : (code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Cont P L g d e u := by
  rw [tmpl_site hpre hi h hc] at hf
  simp only [siteTmpl, hs] at hf
  refine step_vstore (d' := { d with site := .ldwb, sub := 0, raw := [] }) (by simp [hs, Site.vec])
    (by simp [hs, Site.vload]) (fun e => by simp only [next, hs]) hi h rfl hf ?_
  intro h3 hacc hu
  have hrow := hi.row (by simp [hs, Site.inRow])
  rw [hs] at hu
  refine ⟨u, .refl, ⟨?_, ?_, ?_, hu.2.2.2.1, ?_⟩, ?_⟩
  · rw [hu.1]; rfl
  · exact hu.2.1
  · exact hu.2.2.1.trans hacc.symm
  · have hframe : ∀ r, r ∉ ([] : List Nat) → u.regs r = u.regs r := fun _ _ => rfl
    show Holds u.regs (factsAt P g Site.ldwb.pc _)
    frame_fp hu.2.2.2.2, hframe
    trivial
  · simpa using inv_vec_next (s := .ldwb) hi rfl (by simp [hs, Site.inRow])
      (by simp) (by simp) (by simp) hacc []

theorem step_stob (hpre : Pre P L mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .stob) (hi : Inv P g d) (h : (code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Cont P L g d e u := by
  rw [tmpl_site hpre hi h hc] at hf
  simp only [siteTmpl, hs] at hf
  refine step_vstore (d' := { d with site := .bar2, sub := 0 }) (by simp [hs, Site.vec])
    (by simp [hs, Site.vload]) (fun e => by simp only [next, hs]) hi h rfl hf ?_
  intro h3 hacc hu
  have hrow := hi.row (by simp [hs, Site.inRow])
  rw [hs] at hu
  obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 1 u = some t' ∧
      At t' Site.bar2.pc (facts P g ({ d with site := .bar2, sub := 0 })) := by
    seg_fp hu using
      rms_values
      all_goals seg_close [row, off]
  refine ⟨t', run_rtg hr', atD_of rfl hacc ht', ?_⟩
  have := hacc
  inv_tac

theorem step_stws (hpre : Pre P L mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .stws) (hi : Inv P g d) (h : (code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Cont P L g d e u := by
  rw [tmpl_site hpre hi h hc] at hf
  simp only [siteTmpl, hs] at hf
  obtain ⟨rfl, hu⟩ := hf
  cases hu
  have hsub : d.sub = 0 := hi.sub.2 (by simp [hs, Site.vec])
  have hacc : d.acc = [] := List.eq_nil_of_length_eq_zero (by simpa [hs, Site.vload] using hi.acc)
  have hrow := hi.row (by simp [hs, Site.inRow])
  have hat : At t Site.stws.pc (factsAt P g Site.stws.pc d) := by
    have := at_of_atD (L := L) hsub hacc h
    simpa [facts, hs] using this
  have hu : At (afterStore t [.reg 126]) (Site.stws.pc + 1) (factsAt P g Site.stws.pc d) := by
    rw [afterStore_last (by simp [h.2.1])]
    exact ⟨by simp [hat.1], rfl, hat.2.2.1, hat.2.2.2.1, hat.2.2.2.2⟩
  obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 3 (afterStore t [.reg 126]) = some t' ∧
      At t' Site.bar0.pc (facts P g { d with site := .bar0 }) := by
    seg_fp hu using
      rms_values
      all_goals seg_close [row, off]
  refine .inl ⟨{ d with site := .bar0 }, t', by simp [next, hs], run_rtg hr', atD_of hsub hacc ht',
                                                  ?_⟩
  have := hi.stws hs
  inv_tac

theorem step_stts (hpre : Pre P L mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .stts) (hi : Inv P g d) (h : (code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Cont P L g d e u := by
  rw [tmpl_site hpre hi h hc] at hf
  simp only [siteTmpl, hs] at hf
  obtain ⟨rfl, hu⟩ := hf
  cases hu
  have hsub : d.sub = 0 := hi.sub.2 (by simp [hs, Site.vec])
  have hacc : d.acc = [] := List.eq_nil_of_length_eq_zero (by simpa [hs, Site.vload] using hi.acc)
  have hrow := hi.row (by simp [hs, Site.inRow])
  have hat : At t Site.stts.pc (factsAt P g Site.stts.pc d) := by
    have := at_of_atD (L := L) hsub hacc h
    simpa [facts, hs] using this
  have hu : At (afterStore t [.reg 151]) (Site.stts.pc + 1) (factsAt P g Site.stts.pc d) := by
    rw [afterStore_last (by simp [h.2.1])]
    exact ⟨by simp [hat.1], rfl, hat.2.2.1, hat.2.2.2.1, hat.2.2.2.2⟩
  obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 2 (afterStore t [.reg 151]) = some t' ∧
      At t' Site.bar1.pc (facts P g { d with site := .bar1 }) := by
    seg_fp hu using
      rms_values
      all_goals seg_close [row, off]
  refine .inl ⟨{ d with site := .bar1 }, t', by simp [next, hs], run_rtg hr', atD_of hsub hacc ht',
                                                  ?_⟩
  have := hi.stts hs
  inv_tac

end
end PTX.Kernels.RmsNorm.Proof
