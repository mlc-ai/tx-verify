-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.Thread.StepBar
public import Kernels.RmsNorm.Proof.Thread.Pieces
public import Kernels.RmsNorm.Assumptions

@[expose] public section

/-! # The scalar shared loads

Warp 0's load of a warp sum continues at the second butterfly; a loaded value that is not four
bytes wide makes the shuffle's template undefined. The load of the total is divided by `4096`
(`div.approx`), offset by `eps` and passed to `rsqrt.approx`, whose result is paired for the
packed multiplications: each step writes its outcome (`approxE`, `floatE`), and the machine stops
where one faults (`ttOk`), for instance where the `rsqrt` argument is not positive. -/

namespace PTX.Kernels.RmsNorm.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

local notation "Prod" => [Assumptions.idealArith, Assumptions.exactApprox]

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

theorem f32Value_4096 : f32Value 1166016512 = some 4096 := by
  simp [f32Value, FloatFmt.decode, FloatFmt.layout, Layout.decode, Layout.fieldVal,
    Layout.magnitude, Layout.bias, Layout.width, FVal.num]
  norm_num

theorem c4096_eq : c4096 = 4096 := by norm_num [c4096, f32Value_4096]

theorem valFloat_4096 : valFloat .f32 (b32 1166016512) = .ok c4096 := by
  rw [valFloat_b32 (by norm_num) f32Value_4096, c4096_eq]; norm_num

theorem f32Value_eps : f32Value 897988541 = some ((f32Value 897988541).getD 0) := by
  simp [f32Value, FloatFmt.decode, FloatFmt.layout, Layout.decode, Layout.fieldVal,
    Layout.magnitude, Layout.bias, Layout.width, FVal.num]

theorem valFloat_eps : valFloat .f32 (.bits 32 (BitVec.ofNat 64 897988541)) = .ok eps :=
  valFloat_b32 (by norm_num) f32Value_eps

theorem step_ldws (hpre : Pre P L mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .ldws) (hi : Inv P g d) (h : (code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Cont P L g d e u := by
  have hat := at_site hs hi h rfl
  rms_hyps hpre
  have hsub : d.sub = 0 := hi.sub.2 (by simp [hs, Site.vec])
  have hacc : d.acc = [] := List.eq_nil_of_length_eq_zero (by simpa [hs, Site.vload] using hi.acc)
  have hrow := hi.row (by simp [hs, Site.inRow])
  have hw := hi.ldws hs
  rw [tmpl_site hpre hi h hc] at hf
  simp only [siteTmpl, hs] at hf
  obtain ⟨bs, -, rfl, hu⟩ := hf
  cases hu
  cases hb : rebuild 3 bs with
  | error f =>
    exact .inr ⟨by simp [next, hs, hb], Machine.dead_of_fault (f := f) (by simp [afterLoad, hb])⟩
  | ok v =>
    rw [afterLoad_ok hat.2.1 hat.2.2.1 hb]
    have h125 : At { setReg t 281 v with pc := t.pc + 1, sub := 0, acc := [] } (Flow.load_2 + 1)
        (factsAt P g (Flow.load_2 + 1) { d with u := v }) := by
      refine ⟨by simp only [hat.1]; rfl, rfl, rfl, by simpa [setReg] using hat.2.2.2.1, ?_⟩
      have hframe : ∀ r, r ∉ [281] → (setReg t 281 v).regs r = t.regs r := by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        simp [setReg, Function.update_of_ne hr]
      change Holds (setReg t 281 v).regs _
      frame_fp hat.2.2.2.2, hframe
      exact ⟨by simp only [setReg, Function.update_self]; rfl, trivial⟩
    obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 4
        { setReg t 281 v with pc := t.pc + 1, sub := 0, acc := [] } = some t' ∧
        At t' (Site.bfb 0).pc (facts P g { d with site := .bfb 0, u := v }) := by
      seg_fp h125 using
        rms_values
        all_goals seg_close
    by_cases h4 : v.bytes = 4
    · refine .inl ⟨{ d with site := .bfb 0, u := v }, t', by simp [next, hs, hb, h4],
        run_rtg hr', atD_of hsub hacc ht', ?_⟩
      inv_tac
    · refine .inr ⟨by simp [next, hs, hb, h4], t', .typeMismatch, run_rtg hr', ?_⟩
      have hout := out_event (K := kernel) (A := Prod) (L := L) (g := g) ht'.2.2.2.1
        (by rw [ht'.1]; exact Flow.code_shfl_6) rfl rfl
      rw [hout]
      have h281 : t'.regs 281 = some v := reg_of ht'.2.2.2.2 (by table_decide)
      have h135 : t'.regs 135 = some (b32 16) := reg_of ht'.2.2.2.2 (by table_decide)
      have h136 : t'.regs 136 = some (b32 31) := reg_of ht'.2.2.2.2 (by table_decide)
      have h137 : t'.regs 137 = some (b32 4294967295) := reg_of ht'.2.2.2.2 (by table_decide)
      have hB : L.block % 32 = 0 := by rw [hpre.hyp.block]
      simp only [eventTmpl, warpTmpl, WarpInstr.rule, shflTmpl, List.head?_nil, Option.join,
        readBits, readValue, readReg, h281, h135, h136, h137, b32, hB, pure, Except.pure, bind,
        Except.bind]
      rw [ite_eq_left (by decide), ite_eq_right h4]

theorem step_ldts (hpre : Pre P L mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .ldts) (hi : Inv P g d) (h : (code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Cont P L g d e u := by
  have hat := at_site hs hi h rfl
  rms_hyps hpre
  have hsub : d.sub = 0 := hi.sub.2 (by simp [hs, Site.vec])
  have hacc : d.acc = [] := List.eq_nil_of_length_eq_zero (by simpa [hs, Site.vload] using hi.acc)
  have hrow := hi.row (by simp [hs, Site.inRow])
  rw [tmpl_site hpre hi h hc] at hf
  simp only [siteTmpl, hs] at hf
  obtain ⟨bs, -, rfl, hu⟩ := hf
  cases hu
  cases hb : rebuild 3 bs with
  | error f =>
    exact .inr ⟨by simp [next, hs, hb], Machine.dead_of_fault (f := f) (by simp [afterLoad, hb])⟩
  | ok v =>
    rw [afterLoad_ok hat.2.1 hat.2.2.1 hb]
    set t0 : TState := { setReg t 155 v with pc := t.pc + 1, sub := 0, acc := [] } with ht0
    have hpc : t.pc = Flow.load_3 := hat.1
    have hf0 : t0.fault = none := by simpa [ht0, setReg] using hat.2.2.2.1
    have hnx : ∀ (pc : Nat) (a : Acc), next P g d ⟨pc, .rd a bs⟩ =
        if ttOk v then some (some { d with site := .ldwa, tt := v, raw := [] }) else none :=
      fun pc a => by simp [next, hs, hb]
    -- the constant `4096`
    set t1 := PTX.next (setReg t0 275 (b32 1166016512)) with ht1
    have o1 : out kernel Prod L g t0 = .tau t1 := by
      have hc0 : kernel.code[t0.pc]? =
          some ⟨none, .move ⟨.scalar, .int .b 32, [some 275], [.f32imm 1166016512]⟩⟩ := by
        simp only [ht0, hpc]; exact Flow.code_153
      simp only [out, hf0, hc0, guardHolds, pure, Except.pure, Op.isLocal]
      rfl
    have hf1 : t1.fault = none := hf0
    have r155 : t1.regs 155 = some v := by simp [ht1, ht0, PTX.next, setReg]
    have r275 : t1.regs 275 = some (b32 1166016512) := by simp [ht1, PTX.next, setReg]
    -- the mean
    have hc1 : kernel.code[t1.pc]? = some ⟨none, .float
        { divI true with dsts := [some 276], srcs := [.reg 155, .reg 275] }⟩ := by
      simp only [ht1, ht0, PTX.next, setReg, hpc]; exact Flow.code_154
    have hex1 := exec_approxE_div (A := Prod) (L := L) (g := g) (fz := true) (d := 276)
      (approx (by simp)).1 (approx (by simp)).2 (.reg r155) (.reg r275)
    rcases h1 : approxE (divI true) [v, c4096w] with f | q
    · exact .inr ⟨by rw [hnx]; simp only [ttOk, h1, Except.toBool]; rfl, Machine.dead_of_tau o1
        (dead_of_error hc1 rfl hf1 (by rw [hex1, h1]; rfl))⟩
    set t2 := PTX.next (setReg t1 276 q) with ht2
    have o2 : out kernel Prod L g t1 = .tau t2 := tau_of_ok hc1 rfl hf1 (by rw [hex1, h1]; rfl)
    have hf2 : t2.fault = none := hf0
    have r276 : t2.regs 276 = some q := by simp [ht2, PTX.next, setReg]
    -- plus `eps`
    have hc2 : kernel.code[t2.pc]? = some ⟨none, .float
        { addI true with dsts := [some 277], srcs := [.reg 276, .f32imm 897988541] }⟩ := by
      simp only [ht2, ht1, ht0, PTX.next, setReg, hpc]; exact Flow.code_155
    have hex2 := exec_floatE_add (A := Prod) (L := L) (g := g) (fz := true) (d := 277) ideal_add
      decline (.reg r276) (.imm (b := 897988541))
    have hq : divV v = q := okVal_of_ok h1
    rcases h2 : floatE (addI true) [q, epsw] with f | m
    · exact .inr ⟨by rw [hnx]; simp only [ttOk, h1, h2, hq, Except.toBool]; rfl,
        Machine.dead_of_tau o1 (Machine.dead_of_tau o2
          (dead_of_error hc2 rfl hf2 (by
            rw [hex2, show floatE (addI true) [q, .bits 32 (BitVec.ofNat 64 897988541)] = _
              from h2]; rfl)))⟩
    set t3 := PTX.next (setReg t2 277 m) with ht3
    have o3 : out kernel Prod L g t2 = .tau t3 := tau_of_ok hc2 rfl hf2 (by
      rw [hex2, show floatE (addI true) [q, .bits 32 (BitVec.ofNat 64 897988541)] = _ from h2]
      rfl)
    have hf3 : t3.fault = none := hf0
    have r277 : t3.regs 277 = some m := by simp [ht3, PTX.next, setReg]
    -- the inverse square root
    have hc3 : kernel.code[t3.pc]? = some ⟨none, .float
        { rsqrtI true with dsts := [some 278], srcs := [.reg 277] }⟩ := by
      simp only [ht3, ht2, ht1, ht0, PTX.next, setReg, hpc]; exact Flow.code_156
    have hex3 := exec_approxE_rsqrt (A := Prod) (L := L) (g := g) (fz := true) (d := 278)
      (approx (by simp)).1 (approx (by simp)).2 (.reg r277)
    have hm : addV q epsw = m := okVal_of_ok h2
    rcases h3 : approxE (rsqrtI true) [m] with f | r
    · exact .inr ⟨by rw [hnx]; simp only [ttOk, h1, h2, h3, hq, hm, Except.toBool]; rfl,
        Machine.dead_of_tau o1 (Machine.dead_of_tau o2 (Machine.dead_of_tau o3
          (dead_of_error hc3 rfl hf3 (by rw [hex3, h3]; rfl))))⟩
    have hok : ttOk v = true := by simp only [ttOk, h1, h2, h3, hq, hm, Except.toBool]; rfl
    set t4 := PTX.next (setReg t3 278 r) with ht4
    have o4 : out kernel Prod L g t3 = .tau t4 := tau_of_ok hc3 rfl hf3 (by rw [hex3, h3]; rfl)
    have hf4 : t4.fault = none := hf0
    have r278 : t4.regs 278 = some r := by simp [ht4, PTX.next, setReg]
    have hr : rrV v = r := by rw [rrV, hq, hm]; exact okVal_of_ok h3
    have hr4 : r.bytes = 4 := approxE_four rfl _ r h3
    -- the pair of scale factors
    have hc4 : kernel.code[t4.pc]? =
        some ⟨none, .move ⟨.pack, .int .b 64, [some 295], [.reg 278, .reg 278]⟩⟩ := by
      simp only [ht4, ht3, ht2, ht1, ht0, PTX.next, setReg, hpc]; exact Flow.code_157
    set t5 := PTX.next (setReg t4 295 (joinValue r r)) with ht5
    have o5 : out kernel Prod L g t4 = .tau t5 := tau_of_ok hc4 rfl hf4 (by
      rw [exec_packE coreMoves (by hooks_off) r278 r278]
      simp [packE, hr4, Except.map, ht5])
    have hl : Relation.ReflTransGen (Tau kernel Prod L g) t0 t5 :=
      .head o1 (.head o2 (.head o3 (.head o4 (.single o5))))
    refine .inl ⟨{ d with site := .ldwa, tt := v, raw := [] }, t5,
      by simp only [hnx, hok, ↓reduceIte],
      hl, ⟨by simp [ht5, ht4, ht3, ht2, ht1, ht0, PTX.next, setReg, hpc]; rfl, hsub.symm,
                hacc.symm, hf0, ?_⟩, ?_⟩
    · have hframe : ∀ r, r ∉ [155, 275, 276, 277, 278, 295] → t5.regs r = t.regs r := by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [ht5, ht4, ht3, ht2, ht1, ht0, PTX.next, setReg, Function.update_of_ne hr.1,
          Function.update_of_ne hr.2.1, Function.update_of_ne hr.2.2.1,
          Function.update_of_ne hr.2.2.2.1, Function.update_of_ne hr.2.2.2.2.1,
          Function.update_of_ne hr.2.2.2.2.2]
      show Holds t5.regs (factsAt P g Site.ldwa.pc _)
      frame_fp hat.2.2.2.2, hframe
      exact ⟨by simp only [ht5, PTX.next, setReg, Function.update_self]
                exact congrArg some (show joinValue r r = cpair v by rw [cpair, hr]), trivial⟩
    · inv_tac

end
end PTX.Kernels.RmsNorm.Proof
