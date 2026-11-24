-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionAll
public import Lemmas.Flow.Recip
public import Lemmas.Flow.SegDead

@[expose] public section

/-! # The reciprocal of the row sum

After the credit that follows the load of `l`, the code computes the reciprocal of `l'`
(`l' = l`, or `1` when `l = 0`: `setp.ne.f32`, `selp.f32`, `rcp.approx.ftz.f32`) and reaches the
poll of the stage's final accumulator with the outcome `recipE` of the word (the exact `1 / l'`
on a number, by ASM-IDEAL and ASM-APPROX, and the Core rule's result where those decline); where
a step faults the thread is dead (`recip_steps`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

/-- **The three steps of the reciprocal** at the correction code: the outcome `recipE` of the
word in `l`, in `r`, or a dead thread where a step faults. -/
theorem recip_steps {L : Launch} {g : Nat} {u : TState} {pc p l s r : Nat} {aw : Value}
    (hpc : 3700 ≤ pc) (hu : u.pc = pc) (hf : u.fault = none)
    (h1 : kernel.code[pc]? = some ⟨none, .float
      { setpI (.ord .ne) false with dsts := [some p], srcs := [.reg l, .f32imm 0] }⟩)
    (h2 : kernel.code[pc + 1]? = some ⟨none,
      .int ⟨.selp, .float .f32, false, [some s], [.reg l, .f32imm 1065353216, .reg p]⟩⟩)
    (h3 : kernel.code[pc + 2]? = some ⟨none, .float
      { rcpI true with dsts := [some r], srcs := [.reg s] }⟩)
    (hpl : p ≠ l) (ha : u.regs l = some aw) :
    (∀ v, recipE aw = .ok v → ∃ ps : Bool, run kernel asms L g 3 u = some (PTX.next (setReg
      (PTX.next (setReg (PTX.next (setReg u p (.pred ps))) s (if ps then aw else one32))) r v))) ∧
    (∀ f, recipE aw = .error f →
      Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) u) := by
  have hp0 : 3700 ≤ u.pc := hu ▸ hpc
  have hc1 : kernel.code[u.pc]? = some ⟨none, .float
      { setpI (.ord .ne) false with dsts := [some p], srcs := [.reg l, .f32imm 0] }⟩ := hu ▸ h1
  have hex1 := exec_setpE (L := L) (g := g) (t := u) (idealAt (.inr (.inl rfl)) hp0)
    (declineAt (f := .setp .f32) hp0) (c := .ord .ne) (cmp := .ne) (fz := false) (p := p)
    (a := .reg l) (b := .f32imm 0) (Or.inl rfl) rfl (by decide) (OpndIs.reg ha)
    (OpndIs.imm (b := 0))
  cases hps : setpE (.ord .ne) false aw zero32 with
  | error f =>
    have hd : Machine.Dead (K := kernel) (A := asms) (L := L) (g := g) u :=
      dead_of_error (f := f) hc1 rfl hf (by rw [hex1, hps]; rfl)
    exact ⟨fun v hv => by simp [recipE, hps, bind, Except.bind] at hv, fun _ _ => hd⟩
  | ok ps =>
    set u1 := PTX.next (setReg u p (.pred ps))
    have o1 : out kernel asms L g u = .tau u1 := tau_of_ok hc1 rfl hf (by rw [hex1, hps]; rfl)
    have hb : ps = true → aw.bytes = 4 := fun _ => setpE_bytes (Or.inl rfl) hps
    set sv : Value := if ps then aw else one32
    set u2 := PTX.next (setReg u1 s sv)
    have hc2 : kernel.code[u1.pc]? = some ⟨none,
        .int ⟨.selp, .float .f32, false, [some s], [.reg l, .f32imm 1065353216, .reg p]⟩⟩ := by
      rw [show u1.pc = pc + 1 by simp [u1, PTX.next, setReg, hu]]; exact h2
    have hp1 : u1.regs p = some (.pred ps) := by simp [u1, PTX.next, setReg]
    have ha1 : u1.regs l = some aw := by
      simp [u1, PTX.next, setReg, Function.update_of_ne hpl.symm, ha]
    have hex2 : execLocalA asms L g u1 (.int ⟨.selp, .float .f32, false, [some s],
        [.reg l, .f32imm 1065353216, .reg p]⟩) = .ok u2 := by
      rw [(segFree (pc := pc + 1) (by omega)).exec (by simp [u1, PTX.next, setReg, hu]),
        execLocalRule_of_none asms_localRule_none]
      cases ps
      · simp [execLocal_selp (i := ⟨.selp, .float .f32, false, [some s],
          [.reg l, .f32imm 1065353216, .reg p]⟩) rfl, execMove, DType.width, readReg, hp1,
          readValue, readBits, sv, u2, bind, Except.bind, pure, Except.pure, Value.bytes]
      · simp [execLocal_selp (i := ⟨.selp, .float .f32, false, [some s],
          [.reg l, .f32imm 1065353216, .reg p]⟩) rfl, execMove, DType.width, readReg, hp1,
          readValue, ha1, hb rfl, sv, u2, bind, Except.bind, pure, Except.pure]
    have o2 : out kernel asms L g u1 = .tau u2 := tau_of_ok hc2 rfl hf hex2
    have hp2 : 3700 ≤ u2.pc := by simp [u2, u1, PTX.next, setReg, hu]; omega
    have hc3 : kernel.code[u2.pc]? = some ⟨none, .float
        { rcpI true with dsts := [some r], srcs := [.reg s] }⟩ := by
      rw [show u2.pc = pc + 2 by simp [u2, u1, PTX.next, setReg, hu]]; exact h3
    have hs2 : u2.regs s = some sv := by simp [u2, PTX.next, setReg]
    have hex3 := exec_rcpE (L := L) (g := g) (t := u2) (approxAt_rcp hp2).1
      (approxAt_rcp hp2).2 (fz := true) (d := r) (OpndIs.reg hs2)
    have hre : recipE aw = rcpE true sv := by simp [recipE, hps, bind, Except.bind, sv]
    refine ⟨fun v hv => ⟨ps, ?_⟩, fun f hfl => ?_⟩
    · rw [hre] at hv
      have o3 : out kernel asms L g u2 = .tau (PTX.next (setReg u2 r v)) :=
        tau_of_ok hc3 rfl hf (by rw [hex3, hv]; rfl)
      simp only [run, tauStep, o1, o2, o3, Option.bind_some]; rfl
    · rw [hre] at hfl
      exact Machine.dead_of_tau o1 (Machine.dead_of_tau o2
        (dead_of_error (f := f) hc3 rfl hf (by rw [hex3, hfl]; rfl)))

set_option maxHeartbeats 8000000 in
/-- **The credit after the load of `l` of stage 0**, then the reciprocal of `l'` and the
poll of the final accumulator. -/
theorem step_credit4 {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {d : D} {t u : TState} {e : Event} {ins : Instr} (_hpre : Pre P L mem0)
    (hs : d.site = .credit 4) (hi : Inv L g d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_22)
  obtain ⟨rfl, -⟩ := fires_arrive_state hf
  have h1 := At.clear_state h
    (not_mem_factsFrom (show 5067 ∉ Flow.live Flow.mbarArrive_22 ++ [] by table_decide))
  set u := PTX.next (mbarStateDest t (some 5067))
  have ha : u.regs 3254 = some aw :=
    holds_mem h1.2.2.2.2 (List.mem_map.mpr ⟨3254, by table_decide, by
      simp only [valueOf, values, chunkValues, loadValues, PTX.Flow.lookupLit, Option.getD_some]⟩)
  have hrs := recip_steps (L := L) (g := g) (u := u) (pc := 4298) (by decide) h1.1 h1.2.2.2.1
    Flow.code_4298 Flow.code_4299 Flow.code_4300 (by decide) ha
  cases hx : recipE aw with
  | error f => exact .inr ⟨by simp [next, hx], hrs.2 f hx⟩
  | ok v =>
    obtain ⟨ps, hrun⟩ := hrs.1 v hx
    have hrv : recipV aw = v := okVal_of_ok hx
    have hframe : ∀ r, r ∉ [304, 3255, 3256] →
        (PTX.next (setReg (PTX.next (setReg (PTX.next (setReg u 304 (.pred ps))) 3255
          (if ps then aw else one32))) 3256 v)).regs r = u.regs r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [PTX.next, setReg, Function.update_of_ne hr.1, Function.update_of_ne hr.2.1,
        Function.update_of_ne hr.2.2]
    refine step_of_run (d' := ⟨.oWait 0, i, tt, aw, rd32 v, o⟩)
      (by simp [next, hx]) ⟨fun _ => hi.item rfl, fun h' => by simp [Site.inItem] at h',
        fun h' => by simp at h', fun h' => by simp [Site.inTrip] at h',
        fun h' => by simp [Site.rescale] at h'⟩ rfl ⟨3, _, hrun, by
          simp [PTX.next, setReg, h1.1]; rfl, h1.2.1, h1.2.2.1, h1.2.2.2.1, ?_⟩
    have hS := h1.2.2.2.2
    frame_fp hS, hframe
    simp [PTX.next, setReg, Holds, Flow.factsFrom, valueOf, values, chunkValues,
      loadValues, PTX.Flow.lookupLit, hrv]

set_option maxHeartbeats 8000000 in
/-- **The credit after the load of `l` of stage 1**, then the reciprocal of `l'` and the
poll of the final accumulator. -/
theorem step_credit5 {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {d : D} {t u : TState} {e : Event} {ins : Instr} (_hpre : Pre P L mem0)
    (hs : d.site = .credit 5) (hi : Inv L g d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_25)
  obtain ⟨rfl, -⟩ := fires_arrive_state hf
  have h1 := At.clear_state h
    (not_mem_factsFrom (show 5198 ∉ Flow.live Flow.mbarArrive_25 ++ [] by table_decide))
  set u := PTX.next (mbarStateDest t (some 5198))
  have ha : u.regs 3577 = some aw :=
    holds_mem h1.2.2.2.2 (List.mem_map.mpr ⟨3577, by table_decide, by
      simp only [valueOf, values, chunkValues, loadValues, PTX.Flow.lookupLit, Option.getD_some]⟩)
  have hrs := recip_steps (L := L) (g := g) (u := u) (pc := 4594) (by decide) h1.1 h1.2.2.2.1
    Flow.code_4594 Flow.code_4595 Flow.code_4596 (by decide) ha
  cases hx : recipE aw with
  | error f => exact .inr ⟨by simp [next, hx], hrs.2 f hx⟩
  | ok v =>
    obtain ⟨ps, hrun⟩ := hrs.1 v hx
    have hrv : recipV aw = v := okVal_of_ok hx
    have hframe : ∀ r, r ∉ [305, 3578, 3579] →
        (PTX.next (setReg (PTX.next (setReg (PTX.next (setReg u 305 (.pred ps))) 3578
          (if ps then aw else one32))) 3579 v)).regs r = u.regs r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [PTX.next, setReg, Function.update_of_ne hr.1, Function.update_of_ne hr.2.1,
        Function.update_of_ne hr.2.2]
    refine step_of_run (d' := ⟨.oWait 1, i, tt, aw, rd32 v, o⟩)
      (by simp [next, hx]) ⟨fun _ => hi.item rfl, fun h' => by simp [Site.inItem] at h',
        fun h' => by simp at h', fun h' => by simp [Site.inTrip] at h',
        fun h' => by simp [Site.rescale] at h'⟩ rfl ⟨3, _, hrun, by
          simp [PTX.next, setReg, h1.1]; rfl, h1.2.1, h1.2.2.1, h1.2.2.2.1, ?_⟩
    have hS := h1.2.2.2.2
    frame_fp hS, hframe
    simp [PTX.next, setReg, Holds, Flow.factsFrom, valueOf, values, chunkValues,
      loadValues, PTX.Flow.lookupLit, hrv]

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
