-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ProASiteTac
public import Kernels.InklingRelDecode.Proof.Thread.ProAStepQ

@[expose] public section

/-! # The prologue's sites that `site_cases` does not discharge

`stepOk_of` turns a site's step lemma (`StepD`: a successor, `some none`, or a fault for the
reason `Stop`) into the obligation of `code`. The sites here are those whose segment needs a fact
the evaluation cannot use or a lemma it cannot find:

* `ldSk`: the signed division at pc 59 needs `WordsOk`;
* `bar2`, `pel*_3`, `ptc*_3`: the segment passes `add.s32 %r30, %r2, 256` (pc 319) on the base
  word, which faults on a word without an outcome (`addOk`, `SegD`);
* `pel*_0`: the `and.b32` after the election reads the received word (`seg_and1`, `dead_and1`);
* `ldq15`, `ldq31`, `ldq47`, `ldq63`, `stq*_3`: the packing of two query values into a word
  (`seg_pack32`) needs their two bytes, and the skip of a masked group is long. -/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event} {ins : Instr}

/-- The obligation of `code` at `d` from the step lemma of its site. -/
theorem stepOk_of {P : Inh} {d : D} (h : ∀ {t u : TState} {e : Event} {ins : Instr},
    Inv L g d → AtS L g d t → kernel.code[d.site.pc]? = some ins →
    Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u) → StepD L g d e u) :
    (code L g P).StepOk d := by
  refine ⟨fun {t e u} ins hA hi hc hf => ?_⟩
  rcases h hi hA hc hf with hs | ⟨hn, hd, -⟩ | ⟨hn, hd, -⟩
  · exact .inl hs
  · exact .inr ⟨hn, hd⟩
  · exact .inr ⟨hn, hd⟩

/-- The obligation of `code` at `d` from a step lemma without a fault. -/
theorem stepOk_s {P : Inh} {d : D} (h : ∀ {t u : TState} {e : Event} {ins : Instr},
    Inv L g d → AtS L g d t → kernel.code[d.site.pc]? = some ins →
    Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u) → Step L g d e u) :
    (code L g P).StepOk d :=
  stepOk_of fun hi hA hc hf => .inl (h hi hA hc hf)

/-- The obligation of `code` at a site from its `StepAt` lemma (`ProAStepQ`). -/
theorem stepOk_q {P : Inh} {s : Site} {dt : Dat} (h : StepAt L g s) :
    (code L g P).StepOk ⟨s, dt⟩ :=
  stepOk_of fun hi hA hc hf => .inl (h rfl hi hA hc hf)

theorem step_ldSk (hs : d.site = .ldSk) (hi : Inv L g d) (h : AtS L g d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  obtain ⟨site, dt⟩ := d
  simp only at hs
  subst hs
  obtain ⟨a, ha1, ha2, ha3, ha4, ha5⟩ : ∃ a : MemAccess,
      kernel.code[41]? = some ⟨none, .mem a⟩ ∧ a.kind = .load ∧ a.nc = false ∧
      a.ext = .same ∧ a.regs = [612] :=
    ⟨_, Flow.code_41, rfl, rfl, rfl, rfl⟩
  obtain rfl := Option.some.inj (hc.symm.trans ha1)
  obtain ⟨r, bs, rfl, rfl⟩ := fires_load ha2 ha3 hf ha4
  have h := h.at rfl rfl
  rw [ha5]
  cases hv : rebuild 3 bs with
  | error f => exact .inl (by simp [next, hv])
  | ok v =>
    cases hw : word32 v with
    | none => exact .inl (by simp [next, hv, hw])
    | some x =>
      obtain ⟨hvx, hxl⟩ := word32_spec hw
      subst hvx
      have hU : At (afterLoad t [612] bs) 42 (factsAt L g 42 { dt with sk := x }) := by
        rw [afterLoad_ok h.2.1 h.2.2.1 hv]
        refine ⟨by show t.pc + 1 = 42; rw [h.1]; rfl, rfl, rfl, h.2.2.2.1, ?_⟩
        have hframe : ∀ r, r ∉ [612] → (setRegs t [612] ([] ++ [b32 x])).regs r = t.regs r := by
          intro r hr
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          simp [setRegs, setReg, Function.update_of_ne hr]
        frame_fp h.2.2.2.2, hframe
        simp only [Flow.factsFrom, List.map_cons, List.map_nil]
        simp [setReg, valueOf, table, PTX.Flow.lookupLit, v_r151, b32]
      by_cases hww : WordsOk L g { dt with sk := x }
      · have hi' : Inv L g ⟨.el0, { dt with sk := x }⟩ :=
          Inv.mv hi _ _ rfl rfl (fun j hj => hi.qz j (qle hj)) hi.qb
        have hqz : ∀ j, 0 ≤ j → { dt with sk := x }.q j = qZero := qz0 hi'
        exact step_of_seg (d' := ⟨.el0, { dt with sk := x }⟩) (by simp [next, hv, hw, hww]) hi'
          rfl hU ⟨_, (Seg.comp (seg_42_54 L g { dt with sk := x }) (Seg.comp (seg_54_59 L g { dt
              with sk := x }) (Seg.comp (seg_59_60 L g { dt with sk := x } hi'.args hww)
              (Seg.comp (seg_60_72 L g { dt with sk := x }) (Seg.comp (seg_72_84 L g { dt with sk :=
              x }) (Seg.comp (seg_84_96 L g { dt with sk := x }) (Seg.comp (seg_96_108 L g { dt with
              sk := x }) (Seg.comp (seg_108_120 L g { dt with sk := x }) (seg_120_130 L g { dt with
              sk := x })))))))))⟩
      · exact .inl (by simp [next, hv, hw, hww])

theorem step_pel0_0 (hs : d.site = .pel0_0) (hi : Inv L g d) (h : AtS L g d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : StepD L g d e u := by
  obtain ⟨site, dt⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_12)
  obtain ⟨mk, inst, ld, rfl, rfl⟩ := fires_elect hf
  simp only [Option.elim]
  have h := h.at rfl rfl
  have hU : At (PTX.next (setReg (setReg t 694 (.bits 32 (BitVec.ofNat 64 ld))) 58
      (.pred (laneOf L g == ld)))) 204 (factsAt L g 204 (elDt dt 203 (laneOf L g == ld))) := by
    refine ⟨by show t.pc + 1 = 204; rw [h.1]; rfl, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
    have hframe : ∀ r, r ∉ [694, 58] → (PTX.next (setReg (setReg t 694
        (.bits 32 (BitVec.ofNat 64 ld))) 58 (.pred (laneOf L g == ld)))).regs r = t.regs r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [setReg, PTX.next, Function.update_of_ne hr.1, Function.update_of_ne hr.2]
    frame_fp h.2.2.2.2, hframe
    simp only [Flow.factsFrom, List.map_cons, List.map_nil]
    refine ⟨?_, trivial⟩
    simp [setReg, PTX.next, valueOf, table, PTX.Flow.lookupLit, elDt]
  obtain ⟨t1, hr1, ht1⟩ := seg_204_205 L g (elDt dt 203 (laneOf L g == ld)) _ hU
  have hU2 : At t1 205 ((59, .pred (v_p59 L g (elDt dt 203 (laneOf L g == ld)))) ::
      (58, .pred (laneOf L g == ld)) :: factsAt L g 205 (elDt dt 203 (laneOf L g == ld))) :=
    at_ex2 ht1 (mem_facts (by table_decide) rfl) (mem_facts (by table_decide) rfl)
  obtain ⟨t2, hr2, ht2⟩ := seg_205_206 L g (elDt dt 203 (laneOf L g == ld)) _ _ _ hU2
  have hsh : (elDt dt 203 (laneOf L g == ld)).sh0 = dt.sh0 := rfl
  cases hw : Raw.word32Of dt.sh0 with
  | none =>
    refine .inr (.inl ⟨by simp [next, hw], ?_, 0, by norm_num, rfl, hw⟩)
    have hd := dead_and1 (L := L) (g := g) Flow.code_206 (asms_segFree (by decide +kernel))
      (List.mem_cons_of_mem _ (Flow.mem_factsFrom (by decide +kernel)))
      (show Raw.word32Of (valueOf L g (elDt dt 203 (laneOf L g == ld)) 693) = none by
        simpa [valueOf, table, PTX.Flow.lookupLit, hsh] using hw) ht2
    exact dead_of_run hr1 (dead_of_run hr2 hd)
  | some m =>
    have hw' : Raw.word32Of (elDt dt 203 (laneOf L g == ld)).sh0 = some m := hw
    have hn : (Raw.word32Of dt.sh0 = none) = False := by simp [hw]
    obtain ⟨t3, hr3, ht3⟩ := seg_206_207 L g (elDt dt 203 (laneOf L g == ld)) _ hw' t2 ht2
    refine .inl ?_
    by_cases hh : (v_p59 L g (elDt dt 203 (laneOf L g == ld)) && (laneOf L g == ld)) = true
    · have hi' : Inv L g ⟨.ptc0_0, (elDt dt 203 (laneOf L g == ld))⟩ := inv_to hi
      rw [hh] at ht3
      obtain ⟨t4, hr4, ht4⟩ := seg_207_211_hit L g (elDt dt 203 (laneOf L g == ld)) t3 ht3
      refine .inr ⟨⟨.ptc0_0, (elDt dt 203 (laneOf L g == ld))⟩, t4,
        by simp [next, hw, hh], ?_, ?_, hi'⟩
      · exact (run_rtg hr1).trans ((run_rtg hr2).trans ((run_rtg hr3).trans (run_rtg hr4)))
      · exact ⟨ht4.1, ht4.2.1, ht4.2.2.1, ht4.2.2.2.1, ht4.2.2.2.2⟩
    · have hi' : Inv L g ⟨.pbC0, (elDt dt 203 (laneOf L g == ld))⟩ := inv_to hi
      have hh' : (v_p59 L g (elDt dt 203 (laneOf L g == ld)) && (laneOf L g == ld)) = false :=
        by simpa using hh
      rw [hh'] at ht3
      obtain ⟨t4, hr4, ht4⟩ := seg_207_212_miss L g (elDt dt 203 (laneOf L g == ld)) t3 ht3
      refine .inr ⟨⟨.pbC0, (elDt dt 203 (laneOf L g == ld))⟩, t4,
        by simp [next, hw, hh], ?_, ?_, hi'⟩
      · exact (run_rtg hr1).trans ((run_rtg hr2).trans ((run_rtg hr3).trans (run_rtg hr4)))
      · exact ⟨ht4.1, ht4.2.1, ht4.2.2.1, ht4.2.2.2.1, ht4.2.2.2.2⟩

theorem step_pel0_3 (hs : d.site = .pel0_3) (hi : Inv L g d) (h : AtS L g d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : StepD L g d e u := by
  obtain ⟨site, dt⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_15)
  obtain ⟨mk, inst, ld, rfl, rfl⟩ := fires_elect hf
  simp only [Option.elim]
  have h := h.at rfl rfl
  have hU : At (PTX.next (setReg (setReg t 700 (.bits 32 (BitVec.ofNat 64 ld))) 62
      (.pred (laneOf L g == ld)))) 229 (factsAt L g 229 (elDt dt 228 (laneOf L g == ld))) := by
    refine ⟨by show t.pc + 1 = 229; rw [h.1]; rfl, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
    have hframe : ∀ r, r ∉ [700, 62] → (PTX.next (setReg (setReg t 700
        (.bits 32 (BitVec.ofNat 64 ld))) 62 (.pred (laneOf L g == ld)))).regs r = t.regs r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [setReg, PTX.next, Function.update_of_ne hr.1, Function.update_of_ne hr.2]
    frame_fp h.2.2.2.2, hframe
    simp only [Flow.factsFrom, List.map_cons, List.map_nil]
    refine ⟨?_, trivial⟩
    simp [setReg, PTX.next, valueOf, table, PTX.Flow.lookupLit, elDt]
  have hU2 := (at_ex2 (r1 := 59) (r2 := 62) (v1 := .pred (v_p59 L g (elDt dt 228 (laneOf L g ==
      ld))))
    (v2 := .pred (laneOf L g == ld)) hU (mem_facts (by table_decide) rfl)
    (mem_facts (by table_decide) rfl))
  by_cases hh : (v_p59 L g (elDt dt 228 (laneOf L g == ld)) && (laneOf L g == ld)) = true
  · have hi' : Inv L g ⟨.ptc0_3, (elDt dt 228 (laneOf L g == ld))⟩ := inv_to hi
    exact .inl (step_of_seg (d' := ⟨.ptc0_3, (elDt dt 228 (laneOf L g == ld))⟩) (by simp [next, hh])
        hi' rfl hU2 ⟨_, seg_229_231_hit L g _ _ _ hh⟩)
  · have hi1 : Inv L g ⟨.pel0_3, (elDt dt 228 (laneOf L g == ld))⟩ := inv_to hi
    have hi' : Inv L g ⟨(if v_p63 L g (elDt dt 228 (laneOf L g == ld)) then qSite L g (elDt dt 228
        (laneOf L g == ld)) 0 else Site.pbA1), (elDt dt 228 (laneOf L g == ld))⟩ := by
      split
      · exact inv_qSite hi1 (by norm_num) (by decide)
      · exact inv_to hi1
    have hqz : ∀ j, 0 ≤ j → (elDt dt 228 (laneOf L g == ld)).q j = qZero := qz0 hi1
    obtain ⟨n, hn⟩ := seg_ab0 L g (elDt dt 228 (laneOf L g == ld)) hi'.args hqz hi'.qb
    have hs0 : sub ⟨(if v_p63 L g (elDt dt 228 (laneOf L g == ld)) then qSite L g (elDt dt 228
        (laneOf L g == ld)) 0 else Site.pbA1), (elDt dt 228 (laneOf L g == ld))⟩ = 0 := by
      dsimp only [sub]
      split_ifs
      · exact qSite_sub 0
      · rfl

    exact stepD_gate (c := v_p63 L g (elDt dt 228 (laneOf L g == ld)))
      (d' := ⟨(if v_p63 L g (elDt dt 228 (laneOf L g == ld)) then
        qSite L g (elDt dt 228 (laneOf L g == ld)) 0 else Site.pbA1),
        (elDt dt 228 (laneOf L g == ld))⟩)
      (fun h' => by
        cases hq : v_p63 L g (elDt dt 228 (laneOf L g == ld)) <;>
          cases h59 : v_p59 L g (elDt dt 228 (laneOf L g == ld)) <;> simp_all [next])
      (fun h1 h2 => by cases h59 : v_p59 L g (elDt dt 228 (laneOf L g == ld)) <;> simp_all [next])
      hi' hs0 hU2
      ⟨_, Raw.segD_pre (seg_229_232_miss L g _ _ _ (by simpa using hh)) hn⟩

theorem step_pel1_0 (hs : d.site = .pel1_0) (hi : Inv L g d) (h : AtS L g d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : StepD L g d e u := by
  obtain ⟨site, dt⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_16)
  obtain ⟨mk, inst, ld, rfl, rfl⟩ := fires_elect hf
  simp only [Option.elim]
  have h := h.at rfl rfl
  have hU : At (PTX.next (setReg (setReg t 715 (.bits 32 (BitVec.ofNat 64 ld))) 68
      (.pred (laneOf L g == ld)))) 246 (factsAt L g 246 (elDt dt 245 (laneOf L g == ld))) := by
    refine ⟨by show t.pc + 1 = 246; rw [h.1]; rfl, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
    have hframe : ∀ r, r ∉ [715, 68] → (PTX.next (setReg (setReg t 715
        (.bits 32 (BitVec.ofNat 64 ld))) 68 (.pred (laneOf L g == ld)))).regs r = t.regs r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [setReg, PTX.next, Function.update_of_ne hr.1, Function.update_of_ne hr.2]
    frame_fp h.2.2.2.2, hframe
    simp only [Flow.factsFrom, List.map_cons, List.map_nil]
    refine ⟨?_, trivial⟩
    simp [setReg, PTX.next, valueOf, table, PTX.Flow.lookupLit, elDt]
  have hU2 : At _ 246 ((59, .pred (v_p59 L g (elDt dt 245 (laneOf L g == ld)))) ::
      (68, .pred (laneOf L g == ld)) :: factsAt L g 246 (elDt dt 245 (laneOf L g == ld))) :=
    at_ex2 hU (mem_facts (by table_decide) rfl) (mem_facts (by table_decide) rfl)
  obtain ⟨t2, hr2, ht2⟩ := seg_246_247 L g (elDt dt 245 (laneOf L g == ld)) _ _ _ hU2
  have hsh : (elDt dt 245 (laneOf L g == ld)).sh1 = dt.sh1 := rfl
  cases hw : Raw.word32Of dt.sh1 with
  | none =>
    refine .inr (.inl ⟨by simp [next, hw], ?_, 1, by norm_num, rfl, hw⟩)
    have hd := dead_and1 (L := L) (g := g) Flow.code_247 (asms_segFree (by decide +kernel))
      (List.mem_cons_of_mem _ (Flow.mem_factsFrom (by decide +kernel)))
      (show Raw.word32Of (valueOf L g (elDt dt 245 (laneOf L g == ld)) 714) = none by
        simpa [valueOf, table, PTX.Flow.lookupLit, hsh] using hw) ht2
    exact dead_of_run hr2 hd
  | some m =>
    have hw' : Raw.word32Of (elDt dt 245 (laneOf L g == ld)).sh1 = some m := hw
    have hn : (Raw.word32Of dt.sh1 = none) = False := by simp [hw]
    obtain ⟨t3, hr3, ht3⟩ := seg_247_248 L g (elDt dt 245 (laneOf L g == ld)) _ hw' t2 ht2
    refine .inl ?_
    by_cases hh : (v_p59 L g (elDt dt 245 (laneOf L g == ld)) && (laneOf L g == ld)) = true
    · have hi' : Inv L g ⟨.ptc1_0, (elDt dt 245 (laneOf L g == ld))⟩ := inv_to hi
      rw [hh] at ht3
      obtain ⟨t4, hr4, ht4⟩ := seg_248_253_hit L g (elDt dt 245 (laneOf L g == ld)) t3 ht3
      refine .inr ⟨⟨.ptc1_0, (elDt dt 245 (laneOf L g == ld))⟩, t4,
        by simp [next, hw, hh], ?_, ?_, hi'⟩
      · exact ((run_rtg hr2).trans ((run_rtg hr3).trans (run_rtg hr4)))
      · exact ⟨ht4.1, ht4.2.1, ht4.2.2.1, ht4.2.2.2.1, ht4.2.2.2.2⟩
    · have hi' : Inv L g ⟨.pbC1, (elDt dt 245 (laneOf L g == ld))⟩ := inv_to hi
      have hh' : (v_p59 L g (elDt dt 245 (laneOf L g == ld)) && (laneOf L g == ld)) = false :=
        by simpa using hh
      rw [hh'] at ht3
      obtain ⟨t4, hr4, ht4⟩ := seg_248_254_miss L g (elDt dt 245 (laneOf L g == ld)) t3 ht3
      refine .inr ⟨⟨.pbC1, (elDt dt 245 (laneOf L g == ld))⟩, t4,
        by simp [next, hw, hh], ?_, ?_, hi'⟩
      · exact ((run_rtg hr2).trans ((run_rtg hr3).trans (run_rtg hr4)))
      · exact ⟨ht4.1, ht4.2.1, ht4.2.2.1, ht4.2.2.2.1, ht4.2.2.2.2⟩

theorem step_pel1_3 (hs : d.site = .pel1_3) (hi : Inv L g d) (h : AtS L g d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : StepD L g d e u := by
  obtain ⟨site, dt⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_19)
  obtain ⟨mk, inst, ld, rfl, rfl⟩ := fires_elect hf
  simp only [Option.elim]
  have h := h.at rfl rfl
  have hU : At (PTX.next (setReg (setReg t 722 (.bits 32 (BitVec.ofNat 64 ld))) 71
      (.pred (laneOf L g == ld)))) 271 (factsAt L g 271 (elDt dt 270 (laneOf L g == ld))) := by
    refine ⟨by show t.pc + 1 = 271; rw [h.1]; rfl, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
    have hframe : ∀ r, r ∉ [722, 71] → (PTX.next (setReg (setReg t 722
        (.bits 32 (BitVec.ofNat 64 ld))) 71 (.pred (laneOf L g == ld)))).regs r = t.regs r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [setReg, PTX.next, Function.update_of_ne hr.1, Function.update_of_ne hr.2]
    frame_fp h.2.2.2.2, hframe
    simp only [Flow.factsFrom, List.map_cons, List.map_nil]
    refine ⟨?_, trivial⟩
    simp [setReg, PTX.next, valueOf, table, PTX.Flow.lookupLit, elDt]
  have hU2 := (at_ex2 (r1 := 59) (r2 := 71) (v1 := .pred (v_p59 L g (elDt dt 270 (laneOf L g ==
      ld))))
    (v2 := .pred (laneOf L g == ld)) hU (mem_facts (by table_decide) rfl)
    (mem_facts (by table_decide) rfl))
  by_cases hh : (v_p59 L g (elDt dt 270 (laneOf L g == ld)) && (laneOf L g == ld)) = true
  · have hi' : Inv L g ⟨.ptc1_3, (elDt dt 270 (laneOf L g == ld))⟩ := inv_to hi
    exact .inl (step_of_seg (d' := ⟨.ptc1_3, (elDt dt 270 (laneOf L g == ld))⟩) (by simp [next, hh])
        hi' rfl hU2 ⟨_, seg_271_273_hit L g _ _ _ hh⟩)
  · have hi1 : Inv L g ⟨.pel1_3, (elDt dt 270 (laneOf L g == ld))⟩ := inv_to hi
    have hi' : Inv L g ⟨(if v_p72 L g (elDt dt 270 (laneOf L g == ld)) then qSite L g (elDt dt 270
        (laneOf L g == ld)) 0 else Site.pbA2), (elDt dt 270 (laneOf L g == ld))⟩ := by
      split
      · exact inv_qSite hi1 (by norm_num) (by decide)
      · exact inv_to hi1
    have hqz : ∀ j, 0 ≤ j → (elDt dt 270 (laneOf L g == ld)).q j = qZero := qz0 hi1
    obtain ⟨n, hn⟩ := seg_ab1 L g (elDt dt 270 (laneOf L g == ld)) hi'.args hqz hi'.qb
    have hs0 : sub ⟨(if v_p72 L g (elDt dt 270 (laneOf L g == ld)) then qSite L g (elDt dt 270
        (laneOf L g == ld)) 0 else Site.pbA2), (elDt dt 270 (laneOf L g == ld))⟩ = 0 := by
      dsimp only [sub]
      split_ifs
      · exact qSite_sub 0
      · rfl

    exact stepD_gate (c := v_p72 L g (elDt dt 270 (laneOf L g == ld)))
      (d' := ⟨(if v_p72 L g (elDt dt 270 (laneOf L g == ld)) then
        qSite L g (elDt dt 270 (laneOf L g == ld)) 0 else Site.pbA2),
        (elDt dt 270 (laneOf L g == ld))⟩)
      (fun h' => by
        cases hq : v_p72 L g (elDt dt 270 (laneOf L g == ld)) <;>
          cases h59 : v_p59 L g (elDt dt 270 (laneOf L g == ld)) <;> simp_all [next])
      (fun h1 h2 => by cases h59 : v_p59 L g (elDt dt 270 (laneOf L g == ld)) <;> simp_all [next])
      hi' hs0 hU2
      ⟨_, Raw.segD_pre (seg_271_274_miss L g _ _ _ (by simpa using hh)) hn⟩

theorem step_pel2_0 (hs : d.site = .pel2_0) (hi : Inv L g d) (h : AtS L g d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : StepD L g d e u := by
  obtain ⟨site, dt⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_20)
  obtain ⟨mk, inst, ld, rfl, rfl⟩ := fires_elect hf
  simp only [Option.elim]
  have h := h.at rfl rfl
  have hU : At (PTX.next (setReg (setReg t 737 (.bits 32 (BitVec.ofNat 64 ld))) 77
      (.pred (laneOf L g == ld)))) 288 (factsAt L g 288 (elDt dt 287 (laneOf L g == ld))) := by
    refine ⟨by show t.pc + 1 = 288; rw [h.1]; rfl, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
    have hframe : ∀ r, r ∉ [737, 77] → (PTX.next (setReg (setReg t 737
        (.bits 32 (BitVec.ofNat 64 ld))) 77 (.pred (laneOf L g == ld)))).regs r = t.regs r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [setReg, PTX.next, Function.update_of_ne hr.1, Function.update_of_ne hr.2]
    frame_fp h.2.2.2.2, hframe
    simp only [Flow.factsFrom, List.map_cons, List.map_nil]
    refine ⟨?_, trivial⟩
    simp [setReg, PTX.next, valueOf, table, PTX.Flow.lookupLit, elDt]
  have hU2 : At _ 288 ((59, .pred (v_p59 L g (elDt dt 287 (laneOf L g == ld)))) ::
      (77, .pred (laneOf L g == ld)) :: factsAt L g 288 (elDt dt 287 (laneOf L g == ld))) :=
    at_ex2 hU (mem_facts (by table_decide) rfl) (mem_facts (by table_decide) rfl)
  obtain ⟨t2, hr2, ht2⟩ := seg_288_289 L g (elDt dt 287 (laneOf L g == ld)) _ _ _ hU2
  have hsh : (elDt dt 287 (laneOf L g == ld)).sh2 = dt.sh2 := rfl
  cases hw : Raw.word32Of dt.sh2 with
  | none =>
    refine .inr (.inl ⟨by simp [next, hw], ?_, 2, by norm_num, rfl, hw⟩)
    have hd := dead_and1 (L := L) (g := g) Flow.code_289 (asms_segFree (by decide +kernel))
      (List.mem_cons_of_mem _ (Flow.mem_factsFrom (by decide +kernel)))
      (show Raw.word32Of (valueOf L g (elDt dt 287 (laneOf L g == ld)) 736) = none by
        simpa [valueOf, table, PTX.Flow.lookupLit, hsh] using hw) ht2
    exact dead_of_run hr2 hd
  | some m =>
    have hw' : Raw.word32Of (elDt dt 287 (laneOf L g == ld)).sh2 = some m := hw
    have hn : (Raw.word32Of dt.sh2 = none) = False := by simp [hw]
    obtain ⟨t3, hr3, ht3⟩ := seg_289_290 L g (elDt dt 287 (laneOf L g == ld)) _ hw' t2 ht2
    refine .inl ?_
    by_cases hh : (v_p59 L g (elDt dt 287 (laneOf L g == ld)) && (laneOf L g == ld)) = true
    · have hi' : Inv L g ⟨.ptc2_0, (elDt dt 287 (laneOf L g == ld))⟩ := inv_to hi
      rw [hh] at ht3
      obtain ⟨t4, hr4, ht4⟩ := seg_290_295_hit L g (elDt dt 287 (laneOf L g == ld)) t3 ht3
      refine .inr ⟨⟨.ptc2_0, (elDt dt 287 (laneOf L g == ld))⟩, t4,
        by simp [next, hw, hh], ?_, ?_, hi'⟩
      · exact ((run_rtg hr2).trans ((run_rtg hr3).trans (run_rtg hr4)))
      · exact ⟨ht4.1, ht4.2.1, ht4.2.2.1, ht4.2.2.2.1, ht4.2.2.2.2⟩
    · have hi' : Inv L g ⟨.pbC2, (elDt dt 287 (laneOf L g == ld))⟩ := inv_to hi
      have hh' : (v_p59 L g (elDt dt 287 (laneOf L g == ld)) && (laneOf L g == ld)) = false :=
        by simpa using hh
      rw [hh'] at ht3
      obtain ⟨t4, hr4, ht4⟩ := seg_290_296_miss L g (elDt dt 287 (laneOf L g == ld)) t3 ht3
      refine .inr ⟨⟨.pbC2, (elDt dt 287 (laneOf L g == ld))⟩, t4,
        by simp [next, hw, hh], ?_, ?_, hi'⟩
      · exact ((run_rtg hr2).trans ((run_rtg hr3).trans (run_rtg hr4)))
      · exact ⟨ht4.1, ht4.2.1, ht4.2.2.1, ht4.2.2.2.1, ht4.2.2.2.2⟩

theorem step_pel2_3 (hs : d.site = .pel2_3) (hi : Inv L g d) (h : AtS L g d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : StepD L g d e u := by
  obtain ⟨site, dt⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_23)
  obtain ⟨mk, inst, ld, rfl, rfl⟩ := fires_elect hf
  simp only [Option.elim]
  have h := h.at rfl rfl
  have hU : At (PTX.next (setReg (setReg t 744 (.bits 32 (BitVec.ofNat 64 ld))) 80
      (.pred (laneOf L g == ld)))) 313 (factsAt L g 313 (elDt dt 312 (laneOf L g == ld))) := by
    refine ⟨by show t.pc + 1 = 313; rw [h.1]; rfl, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
    have hframe : ∀ r, r ∉ [744, 80] → (PTX.next (setReg (setReg t 744
        (.bits 32 (BitVec.ofNat 64 ld))) 80 (.pred (laneOf L g == ld)))).regs r = t.regs r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [setReg, PTX.next, Function.update_of_ne hr.1, Function.update_of_ne hr.2]
    frame_fp h.2.2.2.2, hframe
    simp only [Flow.factsFrom, List.map_cons, List.map_nil]
    refine ⟨?_, trivial⟩
    simp [setReg, PTX.next, valueOf, table, PTX.Flow.lookupLit, elDt]
  have hU2 := (at_ex2 (r1 := 59) (r2 := 80) (v1 := .pred (v_p59 L g (elDt dt 312 (laneOf L g ==
      ld))))
    (v2 := .pred (laneOf L g == ld)) hU (mem_facts (by table_decide) rfl)
    (mem_facts (by table_decide) rfl))
  by_cases hh : (v_p59 L g (elDt dt 312 (laneOf L g == ld)) && (laneOf L g == ld)) = true
  · have hi' : Inv L g ⟨.ptc2_3, (elDt dt 312 (laneOf L g == ld))⟩ := inv_to hi
    exact .inl (step_of_seg (d' := ⟨.ptc2_3, (elDt dt 312 (laneOf L g == ld))⟩) (by simp [next, hh])
        hi' rfl hU2 ⟨_, seg_313_315_hit L g _ _ _ hh⟩)
  · have hi1 : Inv L g ⟨.pel2_3, (elDt dt 312 (laneOf L g == ld))⟩ := inv_to hi
    have hi' : Inv L g ⟨(qSite L g (elDt dt 312 (laneOf L g == ld)) 0), (elDt dt 312 (laneOf L g ==
        ld))⟩ := inv_qSite hi1 (by norm_num) (by decide)
    have hqz : ∀ j, 0 ≤ j → (elDt dt 312 (laneOf L g == ld)).q j = qZero := qz0 hi1
    obtain ⟨n, hn⟩ := qenter L g (elDt dt 312 (laneOf L g == ld)) hi'.args hqz hi'.qb
    have hs0 : sub ⟨(qSite L g (elDt dt 312 (laneOf L g == ld)) 0), (elDt dt 312 (laneOf L g ==
        ld))⟩ = 0 := by
      dsimp only [sub]
      exact qSite_sub 0
    exact stepD_gate (c := true)
      (d' := ⟨(qSite L g (elDt dt 312 (laneOf L g == ld)) 0), (elDt dt 312 (laneOf L g == ld))⟩)
      (fun h' => by cases h59 : v_p59 L g (elDt dt 312 (laneOf L g == ld)) <;> simp_all [next])
      (fun h1 h2 => by cases h59 : v_p59 L g (elDt dt 312 (laneOf L g == ld)) <;> simp_all [next])
      hi' hs0 hU2
      ⟨_, Raw.segD_iff (Raw.segD_pre (seg_313_316_miss L g _ _ _ (by simpa using hh)) hn)
        (by simp)⟩

theorem step_ldq15 : StepAt L g .ldq15 :=
  step_ldq_grp (s := .ldq15) (G := 1) Flow.code_418 (qseg1 L g)

theorem step_ldq31 : StepAt L g .ldq31 :=
  step_ldq_grp (s := .ldq31) (G := 2) Flow.code_450 (qseg2 L g)

theorem step_ldq47 : StepAt L g .ldq47 :=
  step_ldq_grp (s := .ldq47) (G := 3) Flow.code_482 (qseg3 L g)

theorem step_ldq63 : StepAt L g .ldq63 :=
  step_ldq (s := .ldq63) (nx := fun _ => .stq0_0) Flow.code_514 fun dt v hi hqz hqb =>
    ⟨Inv.mv hi _ _ rfl rfl (fun j hj => hqz j (qlt hj)) hqb, rfl,
      qlast L g _ hqb⟩

theorem step_stq0_3 : StepAt L g .stq0_3 := step_stq_last Flow.code_526 fun dt hqb =>
  ⟨_, (seg_527_528 L g dt).comp <| (seg_528_529 L g dt hqb).comp <| (seg_529_530 L g dt hqb).comp <|
    (seg_530_531 L g dt hqb).comp (seg_531_532 L g dt hqb)⟩

theorem step_stq1_3 : StepAt L g .stq1_3 := step_stq_last Flow.code_532 fun dt hqb =>
  ⟨_, (seg_533_534 L g dt).comp <| (seg_534_535 L g dt hqb).comp <| (seg_535_536 L g dt hqb).comp <|
    (seg_536_537 L g dt hqb).comp (seg_537_538 L g dt hqb)⟩

theorem step_stq2_3 : StepAt L g .stq2_3 := step_stq_last Flow.code_538 fun dt hqb =>
  ⟨_, (seg_539_540 L g dt).comp <| (seg_540_541 L g dt hqb).comp <| (seg_541_542 L g dt hqb).comp <|
    (seg_542_543 L g dt hqb).comp (seg_543_544 L g dt hqb)⟩

theorem step_stq3_3 : StepAt L g .stq3_3 := step_stq_last Flow.code_544 fun dt hqb =>
  ⟨_, (seg_545_546 L g dt).comp <| (seg_546_547 L g dt hqb).comp <| (seg_547_548 L g dt hqb).comp <|
    (seg_548_549 L g dt hqb).comp (seg_549_550 L g dt hqb)⟩

theorem step_stq4_3 : StepAt L g .stq4_3 := step_stq_last Flow.code_550 fun dt hqb =>
  ⟨_, (seg_551_552 L g dt).comp <| (seg_552_553 L g dt hqb).comp <| (seg_553_554 L g dt hqb).comp <|
    (seg_554_555 L g dt hqb).comp (seg_555_556 L g dt hqb)⟩

theorem step_stq5_3 : StepAt L g .stq5_3 := step_stq_last Flow.code_556 fun dt hqb =>
  ⟨_, (seg_557_558 L g dt).comp <| (seg_558_559 L g dt hqb).comp <| (seg_559_560 L g dt hqb).comp <|
    (seg_560_561 L g dt hqb).comp (seg_561_562 L g dt hqb)⟩

theorem step_stq6_3 : StepAt L g .stq6_3 := step_stq_last Flow.code_562 fun dt hqb =>
  ⟨_, (seg_563_564 L g dt).comp <| (seg_564_565 L g dt hqb).comp <| (seg_565_566 L g dt hqb).comp <|
    (seg_566_567 L g dt hqb).comp (seg_567_568 L g dt hqb)⟩

/-- An issue site whose successor `d'` is reached through `add.s32 %r30, %r2, 256` (pc 319) when
`c` holds: on a base word without an outcome the thread dies there and `next` is `none`. -/
theorem stepOk_gate {P : Inh} {s : Site} {dt : Dat} {d' : D} {c : Bool} {ins0 : Instr}
    (hc0 : kernel.code[s.pc]? = some ins0)
    (hadv : ∀ {t e u}, Fires s.pc (eventTmpl asms L g t ins0.op) e (some u) → u = PTX.next t)
    (hn : ∀ e, next L g ⟨s, dt⟩ e =
      if c = true ∧ addOk dt.w = false then none else some (some d'))
    (hs : s.sub = 0) (hl : ∀ r ∈ Flow.live (s.pc + 1), r ∈ Flow.live s.pc)
    (hseg : Inv L g ⟨s, dt⟩ → Inv L g d' ∧ sub d' = 0 ∧ ∃ n, SegD kernel asms L g n (s.pc + 1)
      (factsAt L g (s.pc + 1) dt) d'.site.pc (facts L g d') (c = true → addOk dt.w = true)) :
    (code L g P).StepOk ⟨s, dt⟩ := by
  refine stepOk_of fun {t u e ins} hi h hc hf => ?_
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain rfl := hadv hf
  obtain ⟨hi', hs', hsd⟩ := hseg hi
  refine stepD_gate (fun hok => ?_) (fun h1 h2 => by rw [hn]; simp [h1, h2]) hi' hs'
    (at_next_live (h.at hs rfl) hl) hsd
  have hnc : ¬ (c = true ∧ addOk dt.w = false) := fun ⟨h1, h2⟩ => by simp [hok h1] at h2
  rw [hn]
  simp only [hnc, ↓reduceIte]

/-- The successor of the barrier and of the last copy of a block: the next block, or the query
loads (`qSite`), as `Inv` and the sub-step need it. -/
theorem inv_qSel {s s' : Site} {dt : Dat} {c : Bool} (hi : Inv L g ⟨s, dt⟩)
    (hq : s.qIdx = 0) (hi' : Inv L g ⟨s', dt⟩) (hs' : s'.sub = 0) :
    Inv L g ⟨if c then qSite L g dt 0 else s', dt⟩ ∧
      sub ⟨if c then qSite L g dt 0 else s', dt⟩ = 0 := by
  split
  · exact ⟨inv_qSite hi (by norm_num) (by omega), qSite_sub 0⟩
  · exact ⟨hi', hs'⟩

/-- A step whose successor `d'` is reached when the condition `B` fails, and where the thread dies
otherwise (a conditional piece, `SegD`, to the successor's site under `¬ B`). -/
theorem stepOk_gateP {P : Inh} {s : Site} {dt : Dat} {d' : D} {B : Prop} [Decidable B]
    {ins0 : Instr} (hc0 : kernel.code[s.pc]? = some ins0)
    (hadv : ∀ {t e u}, Fires s.pc (eventTmpl asms L g t ins0.op) e (some u) → u = PTX.next t)
    (hn : ∀ e, next L g ⟨s, dt⟩ e = if B then none else some (some d'))
    (hs : s.sub = 0) (hl : ∀ r ∈ Flow.live (s.pc + 1), r ∈ Flow.live s.pc)
    (hseg : Inv L g ⟨s, dt⟩ → Inv L g d' ∧ sub d' = 0 ∧ ∃ n, SegD kernel asms L g n (s.pc + 1)
      (factsAt L g (s.pc + 1) dt) d'.site.pc (facts L g d') (¬ B)) :
    (code L g P).StepOk ⟨s, dt⟩ := by
  refine ⟨fun {t e u} ins hA hi hc hf => ?_⟩
  obtain rfl := Option.some.inj (hc.symm.trans hc0)
  obtain rfl := hadv hf
  obtain ⟨hi', hs', n, hsd⟩ := hseg hi
  have hU := at_next_live (AtS.at hA hs rfl) hl
  by_cases hB : B
  · exact .inr ⟨show next L g ⟨s, dt⟩ e = none by rw [hn]; simp [hB],
      (hsd _ hU).2 (not_not.mpr hB)⟩
  · obtain ⟨t', hr, ht'⟩ := (hsd _ hU).1 hB
    have hst : Step L g ⟨s, dt⟩ e (PTX.next t) := .inr ⟨d', t', by rw [hn]; simp [hB],
      run_rtg hr, ⟨ht'.1, hs' ▸ ht'.2.1, ht'.2.2.1, ht'.2.2.2.1, ht'.2.2.2.2⟩, hi'⟩
    exact .inl hst

theorem ov_bar2 {P : Inh} {dt : Dat} : (code L g P).StepOk ⟨.bar2, dt⟩ := by
  refine stepOk_gateP (B := div182 L g dt = false ∨ ((!v_p53 L g dt) = true ∧ addOk dt.w = false))
    Flow.code_bar_2 (fires_async_next (by exact trivial)) (fun _ => rfl) rfl (by table_decide)
    fun hi => ⟨?_, ?_, ?_⟩
  · split
    · exact inv_to hi
    · exact inv_qSite hi (by norm_num) (by decide)
  · dsimp only [sub]
    split
    · rfl
    · exact qSite_sub 0
  · obtain ⟨n, h⟩ := seg_bar2 L g dt hi.args (qz0 hi) hi.qb
    exact ⟨n, h.iff (by
      cases div182 L g dt <;> cases v_p53 L g dt <;> cases addOk dt.w <;> simp)⟩

theorem ov_ptc0_3 {P : Inh} {dt : Dat} : (code L g P).StepOk ⟨.ptc0_3, dt⟩ := by
  refine stepOk_gate (c := v_p63 L g dt) Flow.code_tensorCopy_3 (fires_next (by exact trivial))
    (fun _ => rfl) rfl (by table_decide) fun hi => ?_
  obtain ⟨h1, h2⟩ := inv_qSel (c := v_p63 L g dt) hi rfl (inv_to hi : Inv L g ⟨.pbA1, dt⟩) rfl
  exact ⟨h1, h2, seg_ab0 L g dt hi.args (qz0 hi) hi.qb⟩

theorem ov_ptc1_3 {P : Inh} {dt : Dat} : (code L g P).StepOk ⟨.ptc1_3, dt⟩ := by
  refine stepOk_gate (c := v_p72 L g dt) Flow.code_tensorCopy_7 (fires_next (by exact trivial))
    (fun _ => rfl) rfl (by table_decide) fun hi => ?_
  obtain ⟨h1, h2⟩ := inv_qSel (c := v_p72 L g dt) hi rfl (inv_to hi : Inv L g ⟨.pbA2, dt⟩) rfl
  exact ⟨h1, h2, seg_ab1 L g dt hi.args (qz0 hi) hi.qb⟩

theorem ov_ptc2_3 {P : Inh} {dt : Dat} : (code L g P).StepOk ⟨.ptc2_3, dt⟩ := by
  refine stepOk_gate (c := true) (d' := ⟨qSite L g dt 0, dt⟩) Flow.code_tensorCopy_11
    (fires_next (by exact trivial)) (fun _ => by simp [next]) rfl (by table_decide) fun hi => ?_
  obtain ⟨n, hn⟩ := qenter L g dt hi.args (qz0 hi) hi.qb
  exact ⟨inv_qSite hi (by norm_num) (by decide), qSite_sub 0, ⟨_, Raw.segD_iff hn (by simp)⟩⟩

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
