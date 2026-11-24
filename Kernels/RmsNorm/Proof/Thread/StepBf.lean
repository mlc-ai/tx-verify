-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.Thread.Pieces

@[expose] public section

/-! # The butterfly rounds

A round shuffles the lane's partial sum with the lane whose index differs in the round's bit,
and adds the value received (`exec_floatE_add`): the sum is the outcome of the ideal addition,
and where that faults (an operand without a number, or a NaN or `∞ - ∞` the ideal rule declines,
for which `add` without a rounding modifier has no Core rule) the thread is dead. The next
round's lane offset is set; after the last round lane 0 of a warp continues at its store of the
warp's sum, every other lane at the barrier. In warp 0's second butterfly the first round adds
the loaded warp sum (`0` for lanes 8..31); after its last round thread 0 continues at the store
of the total, every other thread at the barrier. -/

namespace PTX.Kernels.RmsNorm.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

local notation "Prod" => [Assumptions.idealArith, Assumptions.exactApprox]

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

theorem at_site {d : D} {t : TState} {s : Site} (hs : d.site = s) (hi : Inv P g d)
    (h : (code P L g).AtD d t) (hv : s.vec = false) : At t s.pc (factsAt P g s.pc d) := by
  have hsub : d.sub = 0 := hi.sub.2 (by rw [hs]; exact hv)
  have hvl : d.site.vload = false := by rw [hs]; cases s <;> simp_all [Site.vec, Site.vload]
  have hacc : d.acc = [] := List.eq_nil_of_length_eq_zero (by simpa [hvl] using hi.acc)
  have := at_of_atD (L := L) hsub hacc h
  simpa [facts, hs] using this


theorem step_bfa0 (hpre : Pre P L mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .bfa 0) (hi : Inv P g d) (h : (code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Cont P L g d e u := by
  have hat := at_site hs hi h rfl
  rms_hyps hpre
  have hsub : d.sub = 0 := hi.sub.2 (by simp [hs, Site.vec])
  have hacc : d.acc = [] := List.eq_nil_of_length_eq_zero (by simpa [hs, Site.vload] using hi.acc)
  rw [tmpl_site hpre hi h hc] at hf
  simp only [siteTmpl, hs, bfOff, bfaDst] at hf
  obtain ⟨recv, ok, rfl, hu⟩ := hf
  cases hu
  have hpc : t.pc = 95 := hat.1
  have hf1 : (PTX.next (setReg t 93 recv)).fault = none := by
    simpa [PTX.next, setReg] using hat.2.2.2.1
  have hsrc : (PTX.next (setReg t 93 recv)).regs 94 = some (bsumV (ssqV d) d.ra 0) := by
    simp only [PTX.next, setReg, ne_eq, Nat.reduceEqDiff, not_false_eq_true, Function.update_of_ne]
    exact reg_of hat.2.2.2.2 (by table_decide)
  have hdst : (PTX.next (setReg t 93 recv)).regs 93 = some recv := by
    simp [PTX.next, setReg]
  have hc1 : kernel.code[(PTX.next (setReg t 93 recv)).pc]? =
      some ⟨none, .float { addI true with dsts := [some 99], srcs := [.reg 94, .reg 93] }⟩ := by
    simp only [PTX.next, setReg, hpc]; exact Flow.code_96
  have hex := exec_floatE_add (A := Prod) (L := L) (g := g) (fz := true) (d := 99) ideal_add
    decline (.reg hsrc) (.reg hdst)
  rcases hy : floatE (addI true) [bsumV (ssqV d) d.ra 0, recv] with f | y
  · exact .inr ⟨by simp [next, hs, hy, Except.toBool], dead_of_error hc1 rfl hf1
      (by rw [hex, hy]; rfl)⟩
  have ho := tau_of_ok hc1 rfl hf1 (by rw [hex, hy]; rfl)
  have h2 : At (PTX.next (setReg (PTX.next (setReg t 93 recv)) 99
    y))
      (95 + 2) (factsAt P g (95 + 2) ({ d with ra := Function.update d.ra 0 recv })) := by
    refine ⟨by simp [PTX.next, setReg, hpc], hat.2.1, hat.2.2.1,
                 by simpa [PTX.next, setReg] using hf1, ?_⟩
    have hframe : ∀ r, r ∉ [93, 99] →
        (PTX.next (setReg (PTX.next (setReg t 93 recv)) 99
          y)).regs r =
          t.regs r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [PTX.next, setReg, Function.update_of_ne hr.1, Function.update_of_ne hr.2]
    frame_fp hat.2.2.2.2, hframe
    exact ⟨by simp only [PTX.next, setReg, Function.update_self]
              exact congrArg some (okVal_of_ok hy).symm, trivial⟩
  obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 1
      (PTX.next (setReg (PTX.next (setReg t 93 recv)) 99
        y)) = some t' ∧
      At t' (Site.bfa 1).pc (facts P g
        { { d with ra := Function.update d.ra 0 recv } with site := .bfa 1 }) := by
    seg_fp h2 using
      rms_values
      all_goals seg_close
  refine .inl ⟨{ { d with ra := Function.update d.ra 0 recv } with site := .bfa 1 }, t',
    by simp [next, hs, hy, bfaNext, Except.toBool],
    Relation.ReflTransGen.head ho (run_rtg hr'), atD_of hsub hacc ht', ?_⟩
  have := hi.row (by simp [hs, Site.inRow])

  inv_tac

theorem step_bfa1 (hpre : Pre P L mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .bfa 1) (hi : Inv P g d) (h : (code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Cont P L g d e u := by
  have hat := at_site hs hi h rfl
  rms_hyps hpre
  have hsub : d.sub = 0 := hi.sub.2 (by simp [hs, Site.vec])
  have hacc : d.acc = [] := List.eq_nil_of_length_eq_zero (by simpa [hs, Site.vload] using hi.acc)
  rw [tmpl_site hpre hi h hc] at hf
  simp only [siteTmpl, hs, bfOff, bfaDst] at hf
  obtain ⟨recv, ok, rfl, hu⟩ := hf
  cases hu
  have hpc : t.pc = 98 := hat.1
  have hf1 : (PTX.next (setReg t 98 recv)).fault = none := by
    simpa [PTX.next, setReg] using hat.2.2.2.1
  have hsrc : (PTX.next (setReg t 98 recv)).regs 99 = some (bsumV (ssqV d) d.ra 1) := by
    simp only [PTX.next, setReg, ne_eq, Nat.reduceEqDiff, not_false_eq_true, Function.update_of_ne]
    exact reg_of hat.2.2.2.2 (by table_decide)
  have hdst : (PTX.next (setReg t 98 recv)).regs 98 = some recv := by
    simp [PTX.next, setReg]
  have hc1 : kernel.code[(PTX.next (setReg t 98 recv)).pc]? =
      some ⟨none, .float { addI true with dsts := [some 102], srcs := [.reg 99, .reg 98] }⟩ := by
    simp only [PTX.next, setReg, hpc]; exact Flow.code_99
  have hex := exec_floatE_add (A := Prod) (L := L) (g := g) (fz := true) (d := 102) ideal_add
    decline (.reg hsrc) (.reg hdst)
  rcases hy : floatE (addI true) [bsumV (ssqV d) d.ra 1, recv] with f | y
  · exact .inr ⟨by simp [next, hs, hy, Except.toBool], dead_of_error hc1 rfl hf1
      (by rw [hex, hy]; rfl)⟩
  have ho := tau_of_ok hc1 rfl hf1 (by rw [hex, hy]; rfl)
  have h2 : At (PTX.next (setReg (PTX.next (setReg t 98 recv)) 102
    y))
      (98 + 2) (factsAt P g (98 + 2) ({ d with ra := Function.update d.ra 1 recv })) := by
    refine ⟨by simp [PTX.next, setReg, hpc], hat.2.1, hat.2.2.1,
                 by simpa [PTX.next, setReg] using hf1, ?_⟩
    have hframe : ∀ r, r ∉ [98, 102] →
        (PTX.next (setReg (PTX.next (setReg t 98 recv)) 102
          y)).regs r =
          t.regs r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [PTX.next, setReg, Function.update_of_ne hr.1, Function.update_of_ne hr.2]
    frame_fp hat.2.2.2.2, hframe
    exact ⟨by simp only [PTX.next, setReg, Function.update_self]
              exact congrArg some (okVal_of_ok hy).symm, trivial⟩
  obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 1
      (PTX.next (setReg (PTX.next (setReg t 98 recv)) 102
        y)) = some t' ∧
      At t' (Site.bfa 2).pc (facts P g
        { { d with ra := Function.update d.ra 1 recv } with site := .bfa 2 }) := by
    seg_fp h2 using
      rms_values
      all_goals seg_close
  refine .inl ⟨{ { d with ra := Function.update d.ra 1 recv } with site := .bfa 2 }, t',
    by simp [next, hs, hy, bfaNext, Except.toBool],
    Relation.ReflTransGen.head ho (run_rtg hr'), atD_of hsub hacc ht', ?_⟩
  have := hi.row (by simp [hs, Site.inRow])

  inv_tac

theorem step_bfa2 (hpre : Pre P L mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .bfa 2) (hi : Inv P g d) (h : (code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Cont P L g d e u := by
  have hat := at_site hs hi h rfl
  rms_hyps hpre
  have hsub : d.sub = 0 := hi.sub.2 (by simp [hs, Site.vec])
  have hacc : d.acc = [] := List.eq_nil_of_length_eq_zero (by simpa [hs, Site.vload] using hi.acc)
  rw [tmpl_site hpre hi h hc] at hf
  simp only [siteTmpl, hs, bfOff, bfaDst] at hf
  obtain ⟨recv, ok, rfl, hu⟩ := hf
  cases hu
  have hpc : t.pc = 101 := hat.1
  have hf1 : (PTX.next (setReg t 101 recv)).fault = none := by
    simpa [PTX.next, setReg] using hat.2.2.2.1
  have hsrc : (PTX.next (setReg t 101 recv)).regs 102 = some (bsumV (ssqV d) d.ra 2) := by
    simp only [PTX.next, setReg, ne_eq, Nat.reduceEqDiff, not_false_eq_true, Function.update_of_ne]
    exact reg_of hat.2.2.2.2 (by table_decide)
  have hdst : (PTX.next (setReg t 101 recv)).regs 101 = some recv := by
    simp [PTX.next, setReg]
  have hc1 : kernel.code[(PTX.next (setReg t 101 recv)).pc]? =
      some ⟨none, .float { addI true with dsts := [some 105], srcs := [.reg 102, .reg 101] }⟩ := by
    simp only [PTX.next, setReg, hpc]; exact Flow.code_102
  have hex := exec_floatE_add (A := Prod) (L := L) (g := g) (fz := true) (d := 105) ideal_add
    decline (.reg hsrc) (.reg hdst)
  rcases hy : floatE (addI true) [bsumV (ssqV d) d.ra 2, recv] with f | y
  · exact .inr ⟨by simp [next, hs, hy, Except.toBool], dead_of_error hc1 rfl hf1
      (by rw [hex, hy]; rfl)⟩
  have ho := tau_of_ok hc1 rfl hf1 (by rw [hex, hy]; rfl)
  have h2 : At (PTX.next (setReg (PTX.next (setReg t 101 recv)) 105
    y))
      (101 + 2) (factsAt P g (101 + 2) ({ d with ra := Function.update d.ra 2 recv })) := by
    refine ⟨by simp [PTX.next, setReg, hpc], hat.2.1, hat.2.2.1,
                 by simpa [PTX.next, setReg] using hf1, ?_⟩
    have hframe : ∀ r, r ∉ [101, 105] →
        (PTX.next (setReg (PTX.next (setReg t 101 recv)) 105
          y)).regs r =
          t.regs r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [PTX.next, setReg, Function.update_of_ne hr.1, Function.update_of_ne hr.2]
    frame_fp hat.2.2.2.2, hframe
    exact ⟨by simp only [PTX.next, setReg, Function.update_self]
              exact congrArg some (okVal_of_ok hy).symm, trivial⟩
  obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 1
      (PTX.next (setReg (PTX.next (setReg t 101 recv)) 105
        y)) = some t' ∧
      At t' (Site.bfa 3).pc (facts P g
        { { d with ra := Function.update d.ra 2 recv } with site := .bfa 3 }) := by
    seg_fp h2 using
      rms_values
      all_goals seg_close
  refine .inl ⟨{ { d with ra := Function.update d.ra 2 recv } with site := .bfa 3 }, t',
    by simp [next, hs, hy, bfaNext, Except.toBool],
    Relation.ReflTransGen.head ho (run_rtg hr'), atD_of hsub hacc ht', ?_⟩
  have := hi.row (by simp [hs, Site.inRow])

  inv_tac

theorem step_bfa3 (hpre : Pre P L mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .bfa 3) (hi : Inv P g d) (h : (code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Cont P L g d e u := by
  have hat := at_site hs hi h rfl
  rms_hyps hpre
  have hsub : d.sub = 0 := hi.sub.2 (by simp [hs, Site.vec])
  have hacc : d.acc = [] := List.eq_nil_of_length_eq_zero (by simpa [hs, Site.vload] using hi.acc)
  rw [tmpl_site hpre hi h hc] at hf
  simp only [siteTmpl, hs, bfOff, bfaDst] at hf
  obtain ⟨recv, ok, rfl, hu⟩ := hf
  cases hu
  have hpc : t.pc = 104 := hat.1
  have hf1 : (PTX.next (setReg t 104 recv)).fault = none := by
    simpa [PTX.next, setReg] using hat.2.2.2.1
  have hsrc : (PTX.next (setReg t 104 recv)).regs 105 = some (bsumV (ssqV d) d.ra 3) := by
    simp only [PTX.next, setReg, ne_eq, Nat.reduceEqDiff, not_false_eq_true, Function.update_of_ne]
    exact reg_of hat.2.2.2.2 (by table_decide)
  have hdst : (PTX.next (setReg t 104 recv)).regs 104 = some recv := by
    simp [PTX.next, setReg]
  have hc1 : kernel.code[(PTX.next (setReg t 104 recv)).pc]? =
      some ⟨none, .float { addI true with dsts := [some 108], srcs := [.reg 105, .reg 104] }⟩ := by
    simp only [PTX.next, setReg, hpc]; exact Flow.code_105
  have hex := exec_floatE_add (A := Prod) (L := L) (g := g) (fz := true) (d := 108) ideal_add
    decline (.reg hsrc) (.reg hdst)
  rcases hy : floatE (addI true) [bsumV (ssqV d) d.ra 3, recv] with f | y
  · exact .inr ⟨by simp [next, hs, hy, Except.toBool], dead_of_error hc1 rfl hf1
      (by rw [hex, hy]; rfl)⟩
  have ho := tau_of_ok hc1 rfl hf1 (by rw [hex, hy]; rfl)
  have h2 : At (PTX.next (setReg (PTX.next (setReg t 104 recv)) 108
    y))
      (104 + 2) (factsAt P g (104 + 2) ({ d with ra := Function.update d.ra 3 recv })) := by
    refine ⟨by simp [PTX.next, setReg, hpc], hat.2.1, hat.2.2.1,
                 by simpa [PTX.next, setReg] using hf1, ?_⟩
    have hframe : ∀ r, r ∉ [104, 108] →
        (PTX.next (setReg (PTX.next (setReg t 104 recv)) 108
          y)).regs r =
          t.regs r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [PTX.next, setReg, Function.update_of_ne hr.1, Function.update_of_ne hr.2]
    frame_fp hat.2.2.2.2, hframe
    exact ⟨by simp only [PTX.next, setReg, Function.update_self]
              exact congrArg some (okVal_of_ok hy).symm, trivial⟩
  obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 1
      (PTX.next (setReg (PTX.next (setReg t 104 recv)) 108
        y)) = some t' ∧
      At t' (Site.bfa 4).pc (facts P g
        { { d with ra := Function.update d.ra 3 recv } with site := .bfa 4 }) := by
    seg_fp h2 using
      rms_values
      all_goals seg_close
  refine .inl ⟨{ { d with ra := Function.update d.ra 3 recv } with site := .bfa 4 }, t',
    by simp [next, hs, hy, bfaNext, Except.toBool],
    Relation.ReflTransGen.head ho (run_rtg hr'), atD_of hsub hacc ht', ?_⟩
  have := hi.row (by simp [hs, Site.inRow])

  inv_tac

theorem step_bfa4 (hpre : Pre P L mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .bfa 4) (hi : Inv P g d) (h : (code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Cont P L g d e u := by
  have hat := at_site hs hi h rfl
  rms_hyps hpre
  have hsub : d.sub = 0 := hi.sub.2 (by simp [hs, Site.vec])
  have hacc : d.acc = [] := List.eq_nil_of_length_eq_zero (by simpa [hs, Site.vload] using hi.acc)
  rw [tmpl_site hpre hi h hc] at hf
  simp only [siteTmpl, hs, bfOff, bfaDst] at hf
  obtain ⟨recv, ok, rfl, hu⟩ := hf
  cases hu
  have hpc : t.pc = 107 := hat.1
  have hf1 : (PTX.next (setReg t 107 recv)).fault = none := by
    simpa [PTX.next, setReg] using hat.2.2.2.1
  have hsrc : (PTX.next (setReg t 107 recv)).regs 108 = some (bsumV (ssqV d) d.ra 4) := by
    simp only [PTX.next, setReg, ne_eq, Nat.reduceEqDiff, not_false_eq_true, Function.update_of_ne]
    exact reg_of hat.2.2.2.2 (by table_decide)
  have hdst : (PTX.next (setReg t 107 recv)).regs 107 = some recv := by
    simp [PTX.next, setReg]
  have hc1 : kernel.code[(PTX.next (setReg t 107 recv)).pc]? =
      some ⟨none, .float { addI true with dsts := [some 126], srcs := [.reg 108, .reg 107] }⟩ := by
    simp only [PTX.next, setReg, hpc]; exact Flow.code_108
  have hex := exec_floatE_add (A := Prod) (L := L) (g := g) (fz := true) (d := 126) ideal_add
    decline (.reg hsrc) (.reg hdst)
  rcases hy : floatE (addI true) [bsumV (ssqV d) d.ra 4, recv] with f | y
  · exact .inr ⟨by simp [next, hs, hy, Except.toBool], dead_of_error hc1 rfl hf1
      (by rw [hex, hy]; rfl)⟩
  have ho := tau_of_ok hc1 rfl hf1 (by rw [hex, hy]; rfl)
  have h2 : At (PTX.next (setReg (PTX.next (setReg t 107 recv)) 126
    y))
      (107 + 2) (factsAt P g (107 + 2) ({ d with ra := Function.update d.ra 4 recv })) := by
    refine ⟨by simp [PTX.next, setReg, hpc], hat.2.1, hat.2.2.1,
                 by simpa [PTX.next, setReg] using hf1, ?_⟩
    have hframe : ∀ r, r ∉ [107, 126] →
        (PTX.next (setReg (PTX.next (setReg t 107 recv)) 126
          y)).regs r =
          t.regs r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [PTX.next, setReg, Function.update_of_ne hr.1, Function.update_of_ne hr.2]
    frame_fp hat.2.2.2.2, hframe
    exact ⟨by simp only [PTX.next, setReg, Function.update_self]
              exact congrArg some (okVal_of_ok hy).symm, trivial⟩
  obtain ⟨u1, hr1, hu1⟩ := run_bra (K := kernel) (A := Prod) (L := L) (g := g) Flow.code_109
    (decide (g % 256 % 32 ≠ 0)) h2 (reg_of h2.2.2.2.2 (by table_decide))
    (localRule_bra L g _ _ _)
  have hl0 : Relation.ReflTransGen (Tau kernel Prod L g) _ u1 := .head ho (run_rtg hr1)
  have := hi.row (by simp [hs, Site.inRow])

  by_cases hz : g % 256 % 32 = 0
  · have hd : decide (g % 256 % 32 ≠ 0) = false := by simp; omega
    rw [hd] at hu1
    simp only [Bool.false_eq_true, ↓reduceIte] at hu1
    have h3 : At u1 (109 + 1)
      (factsAt P g (109 + 1) ({ d with ra := Function.update d.ra 4 recv })) :=
      At.mono hu1 (Flow.holds_factsFrom_mono hu1.2.2.2.2 (by table_decide))
    have h4 : At u1 Site.stws.pc
      (facts P g { { d with ra := Function.update d.ra 4 recv } with site := .stws }) :=
      At.mono h3 (Flow.holds_factsFrom_mono h3.2.2.2.2 (by table_decide))
    refine .inl ⟨{ { d with ra := Function.update d.ra 4 recv } with site := .stws }, u1,
      by simp [next, hs, hy, bfaNext, hz, Except.toBool], hl0, atD_of hsub hacc h4, ?_⟩
    inv_tac
  · have hd : decide (g % 256 % 32 ≠ 0) = true := by simp; omega
    rw [hd] at hu1
    simp only [↓reduceIte] at hu1
    obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 3 u1 = some t' ∧
        At t' (Site.bar0).pc (facts P g
          { { d with ra := Function.update d.ra 4 recv } with site := .bar0 }) := by
      seg_fp hu1 using
        rms_values
        all_goals seg_close
    have hz' : ¬ g % 32 = 0 := by omega
    refine .inl ⟨{ { d with ra := Function.update d.ra 4 recv } with site := .bar0 }, t',
      by simp [next, hs, hy, bfaNext, hz', Except.toBool],
      hl0.trans (run_rtg hr'), atD_of hsub hacc ht', ?_⟩
    inv_tac

theorem step_bfb0 (hpre : Pre P L mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .bfb 0) (hi : Inv P g d) (h : (code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Cont P L g d e u := by
  have hat := at_site hs hi h rfl
  rms_hyps hpre
  have hsub : d.sub = 0 := hi.sub.2 (by simp [hs, Site.vec])
  have hacc : d.acc = [] := List.eq_nil_of_length_eq_zero (by simpa [hs, Site.vload] using hi.acc)
  rw [tmpl_site hpre hi h hc] at hf
  simp only [siteTmpl, hs, bfOff, bfbDst, bfbOp] at hf
  obtain ⟨recv, ok, rfl, hu⟩ := hf
  cases hu
  have hpc : t.pc = 129 := hat.1
  have hf1 : (PTX.next (setReg t 134 recv)).fault = none := by
    simpa [PTX.next, setReg] using hat.2.2.2.1
  have hsrc : (PTX.next (setReg t 134 recv)).regs 281 = some (bsumV d.u d.rb 0) := by
    simp only [PTX.next, setReg, ne_eq, Nat.reduceEqDiff, not_false_eq_true, Function.update_of_ne]
    exact reg_of hat.2.2.2.2 (by table_decide)
  have hdst : (PTX.next (setReg t 134 recv)).regs 134 = some recv := by
    simp [PTX.next, setReg]
  have hc1 : kernel.code[(PTX.next (setReg t 134 recv)).pc]? =
      some ⟨none, .float { addI true with dsts := [some 139], srcs := [.reg 281, .reg 134] }⟩ := by
    simp only [PTX.next, setReg, hpc]; exact Flow.code_130
  have hex := exec_floatE_add (A := Prod) (L := L) (g := g) (fz := true) (d := 139) ideal_add
    decline (.reg hsrc) (.reg hdst)
  rcases hy : floatE (addI true) [bsumV d.u d.rb 0, recv] with f | y
  · exact .inr ⟨by simp [next, hs, hy, Except.toBool], dead_of_error hc1 rfl hf1
      (by rw [hex, hy]; rfl)⟩
  have ho := tau_of_ok hc1 rfl hf1 (by rw [hex, hy]; rfl)
  have h2 : At (PTX.next (setReg (PTX.next (setReg t 134 recv)) 139 y))
      (129 + 2) (factsAt P g (129 + 2) ({ d with rb := Function.update d.rb 0 recv })) := by
    refine ⟨by simp [PTX.next, setReg, hpc], hat.2.1, hat.2.2.1,
                 by simpa [PTX.next, setReg] using hf1, ?_⟩
    have hframe : ∀ r, r ∉ [134, 139] →
        (PTX.next (setReg (PTX.next (setReg t 134 recv)) 139 y)).regs r =
          t.regs r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [PTX.next, setReg, Function.update_of_ne hr.1, Function.update_of_ne hr.2]
    frame_fp hat.2.2.2.2, hframe
    exact ⟨by simp only [PTX.next, setReg, Function.update_self]
              exact congrArg some (okVal_of_ok hy).symm, trivial⟩
  obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 1
      (PTX.next (setReg (PTX.next (setReg t 134 recv)) 139 y)) = some t' ∧
      At t' (Site.bfb 1).pc (facts P g { { d with rb := Function.update d.rb 0 recv } with
        site := .bfb 1 }) := by
    seg_fp h2 using
      rms_values
      all_goals seg_close
  refine .inl ⟨{ { d with rb := Function.update d.rb 0 recv } with site := .bfb 1 }, t',
    by simp [next, hs, hy, bfbNext, Except.toBool, Except.toBool],
    Relation.ReflTransGen.head ho (run_rtg hr'), atD_of hsub hacc ht', ?_⟩
  have := hi.row (by simp [hs, Site.inRow])
  have := (hi.bfb _ hs).2
  inv_tac

theorem step_bfb1 (hpre : Pre P L mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .bfb 1) (hi : Inv P g d) (h : (code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Cont P L g d e u := by
  have hat := at_site hs hi h rfl
  rms_hyps hpre
  have hsub : d.sub = 0 := hi.sub.2 (by simp [hs, Site.vec])
  have hacc : d.acc = [] := List.eq_nil_of_length_eq_zero (by simpa [hs, Site.vload] using hi.acc)
  rw [tmpl_site hpre hi h hc] at hf
  simp only [siteTmpl, hs, bfOff, bfbDst, bfbOp] at hf
  obtain ⟨recv, ok, rfl, hu⟩ := hf
  cases hu
  have hpc : t.pc = 132 := hat.1
  have hf1 : (PTX.next (setReg t 138 recv)).fault = none := by
    simpa [PTX.next, setReg] using hat.2.2.2.1
  have hsrc : (PTX.next (setReg t 138 recv)).regs 139 = some (bsumV d.u d.rb 1) := by
    simp only [PTX.next, setReg, ne_eq, Nat.reduceEqDiff, not_false_eq_true, Function.update_of_ne]
    exact reg_of hat.2.2.2.2 (by table_decide)
  have hdst : (PTX.next (setReg t 138 recv)).regs 138 = some recv := by
    simp [PTX.next, setReg]
  have hc1 : kernel.code[(PTX.next (setReg t 138 recv)).pc]? =
      some ⟨none, .float { addI true with dsts := [some 142], srcs := [.reg 139, .reg 138] }⟩ := by
    simp only [PTX.next, setReg, hpc]; exact Flow.code_133
  have hex := exec_floatE_add (A := Prod) (L := L) (g := g) (fz := true) (d := 142) ideal_add
    decline (.reg hsrc) (.reg hdst)
  rcases hy : floatE (addI true) [bsumV d.u d.rb 1, recv] with f | y
  · exact .inr ⟨by simp [next, hs, hy, Except.toBool], dead_of_error hc1 rfl hf1
      (by rw [hex, hy]; rfl)⟩
  have ho := tau_of_ok hc1 rfl hf1 (by rw [hex, hy]; rfl)
  have h2 : At (PTX.next (setReg (PTX.next (setReg t 138 recv)) 142
    y))
      (132 + 2) (factsAt P g (132 + 2) ({ d with rb := Function.update d.rb 1 recv })) := by
    refine ⟨by simp [PTX.next, setReg, hpc], hat.2.1, hat.2.2.1,
                 by simpa [PTX.next, setReg] using hf1, ?_⟩
    have hframe : ∀ r, r ∉ [138, 142] →
        (PTX.next (setReg (PTX.next (setReg t 138 recv)) 142
          y)).regs r =
          t.regs r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [PTX.next, setReg, Function.update_of_ne hr.1, Function.update_of_ne hr.2]
    frame_fp hat.2.2.2.2, hframe
    exact ⟨by simp only [PTX.next, setReg, Function.update_self]
              exact congrArg some (okVal_of_ok hy).symm, trivial⟩
  obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 1
      (PTX.next (setReg (PTX.next (setReg t 138 recv)) 142
        y)) = some t' ∧
      At t' (Site.bfb 2).pc (facts P g
        { { d with rb := Function.update d.rb 1 recv } with site := .bfb 2 }) := by
    seg_fp h2 using
      rms_values
      all_goals seg_close
  refine .inl ⟨{ { d with rb := Function.update d.rb 1 recv } with site := .bfb 2 }, t',
    by simp [next, hs, hy, bfbNext, Except.toBool],
    Relation.ReflTransGen.head ho (run_rtg hr'), atD_of hsub hacc ht', ?_⟩
  have := hi.row (by simp [hs, Site.inRow])
  have := (hi.bfb _ hs).2
  inv_tac

theorem step_bfb2 (hpre : Pre P L mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .bfb 2) (hi : Inv P g d) (h : (code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Cont P L g d e u := by
  have hat := at_site hs hi h rfl
  rms_hyps hpre
  have hsub : d.sub = 0 := hi.sub.2 (by simp [hs, Site.vec])
  have hacc : d.acc = [] := List.eq_nil_of_length_eq_zero (by simpa [hs, Site.vload] using hi.acc)
  rw [tmpl_site hpre hi h hc] at hf
  simp only [siteTmpl, hs, bfOff, bfbDst, bfbOp] at hf
  obtain ⟨recv, ok, rfl, hu⟩ := hf
  cases hu
  have hpc : t.pc = 135 := hat.1
  have hf1 : (PTX.next (setReg t 141 recv)).fault = none := by
    simpa [PTX.next, setReg] using hat.2.2.2.1
  have hsrc : (PTX.next (setReg t 141 recv)).regs 142 = some (bsumV d.u d.rb 2) := by
    simp only [PTX.next, setReg, ne_eq, Nat.reduceEqDiff, not_false_eq_true, Function.update_of_ne]
    exact reg_of hat.2.2.2.2 (by table_decide)
  have hdst : (PTX.next (setReg t 141 recv)).regs 141 = some recv := by
    simp [PTX.next, setReg]
  have hc1 : kernel.code[(PTX.next (setReg t 141 recv)).pc]? =
      some ⟨none, .float { addI true with dsts := [some 145], srcs := [.reg 142, .reg 141] }⟩ := by
    simp only [PTX.next, setReg, hpc]; exact Flow.code_136
  have hex := exec_floatE_add (A := Prod) (L := L) (g := g) (fz := true) (d := 145) ideal_add
    decline (.reg hsrc) (.reg hdst)
  rcases hy : floatE (addI true) [bsumV d.u d.rb 2, recv] with f | y
  · exact .inr ⟨by simp [next, hs, hy, Except.toBool], dead_of_error hc1 rfl hf1
      (by rw [hex, hy]; rfl)⟩
  have ho := tau_of_ok hc1 rfl hf1 (by rw [hex, hy]; rfl)
  have h2 : At (PTX.next (setReg (PTX.next (setReg t 141 recv)) 145
    y))
      (135 + 2) (factsAt P g (135 + 2) ({ d with rb := Function.update d.rb 2 recv })) := by
    refine ⟨by simp [PTX.next, setReg, hpc], hat.2.1, hat.2.2.1,
                 by simpa [PTX.next, setReg] using hf1, ?_⟩
    have hframe : ∀ r, r ∉ [141, 145] →
        (PTX.next (setReg (PTX.next (setReg t 141 recv)) 145
          y)).regs r =
          t.regs r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [PTX.next, setReg, Function.update_of_ne hr.1, Function.update_of_ne hr.2]
    frame_fp hat.2.2.2.2, hframe
    exact ⟨by simp only [PTX.next, setReg, Function.update_self]
              exact congrArg some (okVal_of_ok hy).symm, trivial⟩
  obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 1
      (PTX.next (setReg (PTX.next (setReg t 141 recv)) 145
        y)) = some t' ∧
      At t' (Site.bfb 3).pc (facts P g
        { { d with rb := Function.update d.rb 2 recv } with site := .bfb 3 }) := by
    seg_fp h2 using
      rms_values
      all_goals seg_close
  refine .inl ⟨{ { d with rb := Function.update d.rb 2 recv } with site := .bfb 3 }, t',
    by simp [next, hs, hy, bfbNext, Except.toBool],
    Relation.ReflTransGen.head ho (run_rtg hr'), atD_of hsub hacc ht', ?_⟩
  have := hi.row (by simp [hs, Site.inRow])
  have := (hi.bfb _ hs).2
  inv_tac

theorem step_bfb3 (hpre : Pre P L mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .bfb 3) (hi : Inv P g d) (h : (code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Cont P L g d e u := by
  have hat := at_site hs hi h rfl
  rms_hyps hpre
  have hsub : d.sub = 0 := hi.sub.2 (by simp [hs, Site.vec])
  have hacc : d.acc = [] := List.eq_nil_of_length_eq_zero (by simpa [hs, Site.vload] using hi.acc)
  rw [tmpl_site hpre hi h hc] at hf
  simp only [siteTmpl, hs, bfOff, bfbDst, bfbOp] at hf
  obtain ⟨recv, ok, rfl, hu⟩ := hf
  cases hu
  have hpc : t.pc = 138 := hat.1
  have hf1 : (PTX.next (setReg t 144 recv)).fault = none := by
    simpa [PTX.next, setReg] using hat.2.2.2.1
  have hsrc : (PTX.next (setReg t 144 recv)).regs 145 = some (bsumV d.u d.rb 3) := by
    simp only [PTX.next, setReg, ne_eq, Nat.reduceEqDiff, not_false_eq_true, Function.update_of_ne]
    exact reg_of hat.2.2.2.2 (by table_decide)
  have hdst : (PTX.next (setReg t 144 recv)).regs 144 = some recv := by
    simp [PTX.next, setReg]
  have hc1 : kernel.code[(PTX.next (setReg t 144 recv)).pc]? =
      some ⟨none, .float { addI true with dsts := [some 148], srcs := [.reg 145, .reg 144] }⟩ := by
    simp only [PTX.next, setReg, hpc]; exact Flow.code_139
  have hex := exec_floatE_add (A := Prod) (L := L) (g := g) (fz := true) (d := 148) ideal_add
    decline (.reg hsrc) (.reg hdst)
  rcases hy : floatE (addI true) [bsumV d.u d.rb 3, recv] with f | y
  · exact .inr ⟨by simp [next, hs, hy, Except.toBool], dead_of_error hc1 rfl hf1
      (by rw [hex, hy]; rfl)⟩
  have ho := tau_of_ok hc1 rfl hf1 (by rw [hex, hy]; rfl)
  have h2 : At (PTX.next (setReg (PTX.next (setReg t 144 recv)) 148
    y))
      (138 + 2) (factsAt P g (138 + 2) ({ d with rb := Function.update d.rb 3 recv })) := by
    refine ⟨by simp [PTX.next, setReg, hpc], hat.2.1, hat.2.2.1,
                 by simpa [PTX.next, setReg] using hf1, ?_⟩
    have hframe : ∀ r, r ∉ [144, 148] →
        (PTX.next (setReg (PTX.next (setReg t 144 recv)) 148
          y)).regs r =
          t.regs r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [PTX.next, setReg, Function.update_of_ne hr.1, Function.update_of_ne hr.2]
    frame_fp hat.2.2.2.2, hframe
    exact ⟨by simp only [PTX.next, setReg, Function.update_self]
              exact congrArg some (okVal_of_ok hy).symm, trivial⟩
  obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 1
      (PTX.next (setReg (PTX.next (setReg t 144 recv)) 148
        y)) = some t' ∧
      At t' (Site.bfb 4).pc (facts P g
        { { d with rb := Function.update d.rb 3 recv } with site := .bfb 4 }) := by
    seg_fp h2 using
      rms_values
      all_goals seg_close
  refine .inl ⟨{ { d with rb := Function.update d.rb 3 recv } with site := .bfb 4 }, t',
    by simp [next, hs, hy, bfbNext, Except.toBool],
    Relation.ReflTransGen.head ho (run_rtg hr'), atD_of hsub hacc ht', ?_⟩
  have := hi.row (by simp [hs, Site.inRow])
  have := (hi.bfb _ hs).2
  inv_tac

theorem step_bfb4 (hpre : Pre P L mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .bfb 4) (hi : Inv P g d) (h : (code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Cont P L g d e u := by
  have hat := at_site hs hi h rfl
  rms_hyps hpre
  have hsub : d.sub = 0 := hi.sub.2 (by simp [hs, Site.vec])
  have hacc : d.acc = [] := List.eq_nil_of_length_eq_zero (by simpa [hs, Site.vload] using hi.acc)
  rw [tmpl_site hpre hi h hc] at hf
  simp only [siteTmpl, hs, bfOff, bfbDst, bfbOp] at hf
  obtain ⟨recv, ok, rfl, hu⟩ := hf
  cases hu
  have hpc : t.pc = 141 := hat.1
  have hf1 : (PTX.next (setReg t 147 recv)).fault = none := by
    simpa [PTX.next, setReg] using hat.2.2.2.1
  have hsrc : (PTX.next (setReg t 147 recv)).regs 148 = some (bsumV d.u d.rb 4) := by
    simp only [PTX.next, setReg, ne_eq, Nat.reduceEqDiff, not_false_eq_true, Function.update_of_ne]
    exact reg_of hat.2.2.2.2 (by table_decide)
  have hdst : (PTX.next (setReg t 147 recv)).regs 147 = some recv := by
    simp [PTX.next, setReg]
  have hc1 : kernel.code[(PTX.next (setReg t 147 recv)).pc]? =
      some ⟨none, .float { addI true with dsts := [some 151], srcs := [.reg 148, .reg 147] }⟩ := by
    simp only [PTX.next, setReg, hpc]; exact Flow.code_142
  have hex := exec_floatE_add (A := Prod) (L := L) (g := g) (fz := true) (d := 151) ideal_add
    decline (.reg hsrc) (.reg hdst)
  rcases hy : floatE (addI true) [bsumV d.u d.rb 4, recv] with f | y
  · exact .inr ⟨by simp [next, hs, hy, Except.toBool], dead_of_error hc1 rfl hf1
      (by rw [hex, hy]; rfl)⟩
  have ho := tau_of_ok hc1 rfl hf1 (by rw [hex, hy]; rfl)
  have h2 : At (PTX.next (setReg (PTX.next (setReg t 147 recv)) 151
    y))
      (141 + 2) (factsAt P g (141 + 2) ({ d with rb := Function.update d.rb 4 recv })) := by
    refine ⟨by simp [PTX.next, setReg, hpc], hat.2.1, hat.2.2.1,
                 by simpa [PTX.next, setReg] using hf1, ?_⟩
    have hframe : ∀ r, r ∉ [147, 151] →
        (PTX.next (setReg (PTX.next (setReg t 147 recv)) 151
          y)).regs r =
          t.regs r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [PTX.next, setReg, Function.update_of_ne hr.1, Function.update_of_ne hr.2]
    frame_fp hat.2.2.2.2, hframe
    exact ⟨by simp only [PTX.next, setReg, Function.update_self]
              exact congrArg some (okVal_of_ok hy).symm, trivial⟩
  obtain ⟨u1, hr1, hu1⟩ := run_bra (K := kernel) (A := Prod) (L := L) (g := g) Flow.code_143
    (decide (g % 256 % 32 ≠ 0)) h2 (reg_of h2.2.2.2.2 (by table_decide))
    (localRule_bra L g _ _ _)
  have hl0 : Relation.ReflTransGen (Tau kernel Prod L g) _ u1 := .head ho (run_rtg hr1)
  have := hi.row (by simp [hs, Site.inRow])
  have := (hi.bfb _ hs).2
  by_cases hz : g % 256 = 0
  · have hd : decide (g % 256 % 32 ≠ 0) = false := by simp; omega
    rw [hd] at hu1
    simp only [Bool.false_eq_true, ↓reduceIte] at hu1
    have h3 : At u1 (143 + 1)
      (factsAt P g (143 + 1) ({ d with rb := Function.update d.rb 4 recv })) :=
      At.mono hu1 (Flow.holds_factsFrom_mono hu1.2.2.2.2 (by table_decide))
    obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 2 u1 = some t' ∧
        At t' (Site.stts).pc (facts P g
          { { d with rb := Function.update d.rb 4 recv } with site := .stts }) := by
      seg_fp h3 using
        rms_values
        all_goals seg_close [hpre.hyp.shared]
    refine .inl ⟨{ { d with rb := Function.update d.rb 4 recv } with site := .stts }, t',
      by simp [next, hs, hy, bfbNext, hz, Except.toBool],
      hl0.trans (run_rtg hr'), atD_of hsub hacc ht', ?_⟩
    inv_tac
  · have hd : decide (g % 256 % 32 ≠ 0) = true := by simp; omega
    rw [hd] at hu1
    simp only [↓reduceIte] at hu1
    obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 2 u1 = some t' ∧
        At t' (Site.bar1).pc (facts P g
          { { d with rb := Function.update d.rb 4 recv } with site := .bar1 }) := by
      seg_fp hu1 using
        rms_values
        all_goals seg_close
    refine .inl ⟨{ { d with rb := Function.update d.rb 4 recv } with site := .bar1 }, t',
      by simp [next, hs, hy, bfbNext, hz, Except.toBool],
      hl0.trans (run_rtg hr'), atD_of hsub hacc ht', ?_⟩
    inv_tac

end
end PTX.Kernels.RmsNorm.Proof
