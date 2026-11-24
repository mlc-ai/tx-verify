-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionAll
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionCounts
public import Lemmas.Flow.LoadShared
public import Lemmas.Flow.Recip

@[expose] public section

/-! # The loads of the row statistics

In a trip, stage `st` loads `α` from its row's slot (`+332 + 512 st + 4 ρ`) and compares it
with `1` (`setp.lt.f32`): the thread reaches the vote with the word and the comparison's outcome
(`ltOneE`), or is dead when the bytes do not form a value or the comparison faults. In the final
part it loads `l` from the same slot and credits the statistics barrier. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

theorem stat_bound {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0) :
    sb L + 4 * rowOf L g + 844 < 2 ^ 32 := by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hrow : rowOf L g < 128 := Nat.mod_lt _ (by decide)
  simp only [sb] at *
  omega

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}

set_option maxHeartbeats 8000000 in
/-- **The load of `α` of stage 0** and its comparison with `1`. -/
theorem step_ldA0 {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .ldA 0)
    (hi : Inv L g d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    Ev L g d e ∧ Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_1)
  have hr : t.regs 627 = some (b32 (sb L + 4 * rowOf L g)) :=
    holds_mem h.2.2.2.2 (List.mem_map.mpr ⟨627, by table_decide, by
      simp only [valueOf, values, chunkValues, loadValues, PTX.Flow.lookupLit, Option.getD_some]⟩)
  have hb := stat_bound (g := g) hpre
  obtain ⟨ac, bs, rfl, hloc, rfl⟩ := fires_ld_shared (off := 332) hr (by omega) h.2.1 hf
  refine ⟨⟨rfl, ac, bs, rfl, by rw [hloc]; simp only [ownLoc, ctaOf]; congr 1; omega⟩, ?_⟩
  cases hv : rebuild 3 bs with
  | error f =>
    exact .inr ⟨by simp [next, hv], Machine.dead_of_fault (f := f) (by simp [afterLoad, hv])⟩
  | ok v =>
    rw [afterLoad_ok h.2.1 h.2.2.1 hv]
    set u1 : TState := { setReg t 663 v with pc := t.pc + 1, sub := 0, acc := [] }
    have hc1 : kernel.code[u1.pc]? = some ⟨none, .float
        { setpI (.ord .lt) false with
          dsts := [some 299], srcs := [.reg 663, .f32imm 1065353216] }⟩ := by
      simp only [u1, h.1]; exact Flow.code_3854
    have hu1 : u1.regs 663 = some v := by simp [u1, setReg]
    have hpc1 : 3700 ≤ u1.pc := by simp only [u1, h.1]; decide
    have hex := exec_setpE (L := L) (g := g) (t := u1) (idealAt (.inr (.inl rfl)) hpc1)
      (declineAt (f := .setp .f32) hpc1)
      (c := .ord .lt) (cmp := .lt) (fz := false) (p := 299) (Or.inl rfl) rfl (by decide)
      (OpndIs.reg hu1) (OpndIs.imm (b := 1065353216))
    cases hx : ltOneE v with
    | error f =>
      refine .inr ⟨by simp [next, hv, hx], dead_of_error (f := f) hc1 rfl h.2.2.2.1 ?_⟩
      rw [hex]; unfold ltOneE at hx; rw [hx]; rfl
    | ok x =>
      have hst : out kernel asms L g u1 = .tau (PTX.next (setReg u1 299 (.pred x))) := by
        refine tau_of_ok hc1 rfl h.2.2.2.1 ?_
        rw [hex]; unfold ltOneE at hx; rw [hx]; rfl
      have hlt : ltOne v = x := by simp [ltOne, hx]
      have hframe : ∀ r, r ∉ [299, 663] →
          (PTX.next (setReg u1 299 (.pred x))).regs r =
            t.regs r := by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [u1, PTX.next, setReg, Function.update_of_ne hr.1, Function.update_of_ne hr.2]
      refine .inl (.inr ⟨⟨.vote 0, i, tt, v, rd32 v, o⟩, _, by simp [next, hv, hx],
        .single hst, ⟨by simp [u1, PTX.next, setReg, h.1]; rfl, rfl, rfl,
          h.2.2.2.1, ?_⟩,
        ⟨fun _ => hi.item rfl, fun h' => by simp [Site.inItem] at h', fun h' => by simp at h',
          fun _ => hi.trip rfl, fun _ => ⟨x, hx⟩⟩⟩)
      have hS := h.2.2.2.2
      frame_fp hS, hframe
      simp [PTX.next, setReg, u1, Holds, Flow.factsFrom, valueOf, values, chunkValues,
        loadValues, PTX.Flow.lookupLit, hlt]

set_option maxHeartbeats 8000000 in
/-- **The load of `α` of stage 1** and its comparison with `1`. -/
theorem step_ldA1 {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .ldA 1)
    (hi : Inv L g d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    Ev L g d e ∧ Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_2)
  have hr : t.regs 627 = some (b32 (sb L + 4 * rowOf L g)) :=
    holds_mem h.2.2.2.2 (List.mem_map.mpr ⟨627, by table_decide, by
      simp only [valueOf, values, chunkValues, loadValues, PTX.Flow.lookupLit, Option.getD_some]⟩)
  have hb := stat_bound (g := g) hpre
  obtain ⟨ac, bs, rfl, hloc, rfl⟩ := fires_ld_shared (off := 844) hr (by omega) h.2.1 hf
  refine ⟨⟨rfl, ac, bs, rfl, by rw [hloc]; simp only [ownLoc, ctaOf]; congr 1; omega⟩, ?_⟩
  cases hv : rebuild 3 bs with
  | error f =>
    exact .inr ⟨by simp [next, hv], Machine.dead_of_fault (f := f) (by simp [afterLoad, hv])⟩
  | ok v =>
    rw [afterLoad_ok h.2.1 h.2.2.1 hv]
    set u1 : TState := { setReg t 664 v with pc := t.pc + 1, sub := 0, acc := [] }
    have hc1 : kernel.code[u1.pc]? = some ⟨none, .float
        { setpI (.ord .lt) false with
          dsts := [some 301], srcs := [.reg 664, .f32imm 1065353216] }⟩ := by
      simp only [u1, h.1]; exact Flow.code_4073
    have hu1 : u1.regs 664 = some v := by simp [u1, setReg]
    have hpc1 : 3700 ≤ u1.pc := by simp only [u1, h.1]; decide
    have hex := exec_setpE (L := L) (g := g) (t := u1) (idealAt (.inr (.inl rfl)) hpc1)
      (declineAt (f := .setp .f32) hpc1)
      (c := .ord .lt) (cmp := .lt) (fz := false) (p := 301) (Or.inl rfl) rfl (by decide)
      (OpndIs.reg hu1) (OpndIs.imm (b := 1065353216))
    cases hx : ltOneE v with
    | error f =>
      refine .inr ⟨by simp [next, hv, hx], dead_of_error (f := f) hc1 rfl h.2.2.2.1 ?_⟩
      rw [hex]; unfold ltOneE at hx; rw [hx]; rfl
    | ok x =>
      have hst : out kernel asms L g u1 = .tau (PTX.next (setReg u1 301 (.pred x))) := by
        refine tau_of_ok hc1 rfl h.2.2.2.1 ?_
        rw [hex]; unfold ltOneE at hx; rw [hx]; rfl
      have hlt : ltOne v = x := by simp [ltOne, hx]
      have hframe : ∀ r, r ∉ [301, 664] →
          (PTX.next (setReg u1 301 (.pred x))).regs r =
            t.regs r := by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [u1, PTX.next, setReg, Function.update_of_ne hr.1, Function.update_of_ne hr.2]
      refine .inl (.inr ⟨⟨.vote 1, i, tt, v, rd32 v, o⟩, _, by simp [next, hv, hx],
        .single hst, ⟨by simp [u1, PTX.next, setReg, h.1]; rfl, rfl, rfl,
          h.2.2.2.1, ?_⟩,
        ⟨fun _ => hi.item rfl, fun h' => by simp [Site.inItem] at h', fun h' => by simp at h',
          fun _ => hi.trip rfl, fun _ => ⟨x, hx⟩⟩⟩)
      have hS := h.2.2.2.2
      frame_fp hS, hframe
      simp [PTX.next, setReg, u1, Holds, Flow.factsFrom, valueOf, values, chunkValues,
        loadValues, PTX.Flow.lookupLit, hlt]


set_option maxHeartbeats 8000000 in
/-- **The load of `l` of stage 0**, then the credit of its statistics barrier. -/
theorem step_ldL0 {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .ldL 0)
    (hi : Inv L g d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    Ev L g d e ∧ Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_3)
  have hr : t.regs 627 = some (b32 (sb L + 4 * rowOf L g)) :=
    holds_mem h.2.2.2.2 (List.mem_map.mpr ⟨627, by table_decide, by
      simp only [valueOf, values, chunkValues, loadValues, PTX.Flow.lookupLit, Option.getD_some]⟩)
  have hb := stat_bound (g := g) hpre
  obtain ⟨ac, bs, rfl, hloc, rfl⟩ := fires_ld_shared (off := 332) hr (by omega) h.2.1 hf
  refine ⟨⟨rfl, ac, bs, rfl, by rw [hloc]; simp only [ownLoc, ctaOf]; congr 1; omega⟩, ?_⟩
  cases hv : rebuild 3 bs with
  | error f =>
    exact .inr ⟨by simp [next, hv], Machine.dead_of_fault (f := f) (by simp [afterLoad, hv])⟩
  | ok v =>
    rw [afterLoad_ok h.2.1 h.2.2.1 hv]
    have hframe : ∀ r, r ∉ [3254] →
        ({ setReg t 3254 v with pc := t.pc + 1, sub := 0, acc := [] } : TState).regs r =
          t.regs r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp [setReg, Function.update_of_ne hr]
    refine step_of_run (d' := ⟨.credit ⟨4 + 0, by omega⟩, i, tt, v, a, o⟩)
      (by simp [next, hv]) ⟨fun _ => hi.item rfl, fun h' => by simp [Site.inItem] at h',
        fun h' => by simp at h', fun h' => by simp [Site.inTrip] at h',
        fun h' => by simp [Site.rescale] at h'⟩ rfl ⟨0, _, rfl, by simp [h.1]; rfl, rfl, rfl,
          h.2.2.2.1, ?_⟩
    have hS := h.2.2.2.2
    frame_fp hS, hframe
    simp [setReg, Holds, Flow.factsFrom, valueOf, values, chunkValues, loadValues,
      PTX.Flow.lookupLit]

set_option maxHeartbeats 8000000 in
/-- **The load of `l` of stage 1**, then the credit of its statistics barrier. -/
theorem step_ldL1 {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .ldL 1)
    (hi : Inv L g d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    Ev L g d e ∧ Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_4)
  have hr : t.regs 627 = some (b32 (sb L + 4 * rowOf L g)) :=
    holds_mem h.2.2.2.2 (List.mem_map.mpr ⟨627, by table_decide, by
      simp only [valueOf, values, chunkValues, loadValues, PTX.Flow.lookupLit, Option.getD_some]⟩)
  have hb := stat_bound (g := g) hpre
  obtain ⟨ac, bs, rfl, hloc, rfl⟩ := fires_ld_shared (off := 844) hr (by omega) h.2.1 hf
  refine ⟨⟨rfl, ac, bs, rfl, by rw [hloc]; simp only [ownLoc, ctaOf]; congr 1; omega⟩, ?_⟩
  cases hv : rebuild 3 bs with
  | error f =>
    exact .inr ⟨by simp [next, hv], Machine.dead_of_fault (f := f) (by simp [afterLoad, hv])⟩
  | ok v =>
    rw [afterLoad_ok h.2.1 h.2.2.1 hv]
    have hframe : ∀ r, r ∉ [3577] →
        ({ setReg t 3577 v with pc := t.pc + 1, sub := 0, acc := [] } : TState).regs r =
          t.regs r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp [setReg, Function.update_of_ne hr]
    refine step_of_run (d' := ⟨.credit ⟨4 + 1, by omega⟩, i, tt, v, a, o⟩)
      (by simp [next, hv]) ⟨fun _ => hi.item rfl, fun h' => by simp [Site.inItem] at h',
        fun h' => by simp at h', fun h' => by simp [Site.inTrip] at h',
        fun h' => by simp [Site.rescale] at h'⟩ rfl ⟨0, _, rfl, by simp [h.1]; rfl, rfl, rfl,
          h.2.2.2.1, ?_⟩
    have hS := h.2.2.2.2
    frame_fp hS, hframe
    simp [setReg, Holds, Flow.factsFrom, valueOf, values, chunkValues, loadValues,
      PTX.Flow.lookupLit]
end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
