-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrPolls
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrStage
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsCorrRstSite
public import Lemmas.Flow.TmplOkVec
public import Lemmas.Flow.TmplOkOff

@[expose] public section

/-! # The correction sites are not undefined behaviour

At every site of the correction role the instruction's event is not undefined behaviour (the
correction part of `Cross.SitesTmplOk`): the register request, the fences, the waits of Tensor
Memory and the return are plain; the start and end barriers have immediate ids and counts and the
statistics syncs ids below 16 in a register with the count 64; the polls and arrivals name
barriers through registers of the state (the leader's through its `mapa` pointer); the loads of
the statistics words are 4-aligned; the vote is a full-mask ballot of a predicate register; the
Tensor Memory loads and stores name the warp's lanes, the stores sixteen single-precision
products; the staging stores write 4-byte words of a 16-aligned vector; the implicit waits are
the waits. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- The warp's lanes of a column are a supported Tensor Memory address. -/
theorem corr_tmem_supported (col : Nat) (hc : col < 512) :
    tcDataAddressOk L g .s32x32b (Correction.tmem L g col) = true := by
  have hk : Correction.kOf L g < 4 := Nat.mod_lt _ (by decide)
  have hf : Correction.tmem L g col / 2 ^ 16 = 32 * Correction.kOf L g := by
    simp only [Correction.tmem]; omega
  show tmemLaneFieldOk L g (Correction.tmem L g col / 2 ^ 16) 32 = true
  rw [hf]
  have hl : laneBase L g = 32 * Correction.kOf L g := by
    simp only [laneBase, Correction.kOf, Correction.tidOf]; omega
  simp [tmemLaneFieldOk, hl]

theorem corr_ub_values (L : Launch) (g : Nat) (d : Correction.D) :
    Correction.valueOf L g d 620 = Correction.leadPtr L g 144 ∧
    Correction.valueOf L g d 621 = Correction.leadPtr L g 152 ∧
    Correction.valueOf L g d 3939 = b32 ((d.i + 1) % 2) ∧
    Correction.valueOf L g d 622 = b32 (Correction.kOf L g + 3) ∧
    Correction.valueOf L g d 623 = b32 (Correction.kOf L g + 7) ∧
    Correction.valueOf L g d 343 = b32 (Correction.sb L + 240) ∧
    Correction.valueOf L g d 628 = b32 (Correction.sb L + 248) ∧
    Correction.valueOf L g d 970 = b32 (Correction.sb L + 256) ∧
    Correction.valueOf L g d 661 = b32 (Correction.sb L + 264) ∧
    Correction.valueOf L g d 2733 = b32 1 ∧ Correction.valueOf L g d 2991 = b32 1 ∧
    Correction.valueOf L g d 3249 = b32 1 ∧ Correction.valueOf L g d 3253 = b32 1 ∧
    Correction.valueOf L g d 627 = b32 (Correction.sb L + 4 * Correction.rowOf L g) ∧
    Correction.valueOf L g d 299 = .pred (Correction.ltOne d.aw) ∧
    Correction.valueOf L g d 301 = .pred (Correction.ltOne d.aw) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [Correction.valueOf, Correction.values, Correction.chunkValues,
      Correction.loadValues, PTX.Flow.lookupLit, Option.getD_some]

/-- Both halves of a product have four bytes. -/
theorem prodV_split_bytes (o : List Value) (c : Value) (q : Nat) :
    (splitValue 64 (Correction.prodV o c q)).1.bytes = 4 ∧
      (splitValue 64 (Correction.prodV o c q)).2.bytes = 4 := by
  obtain ⟨x, y, hp, hx, hy⟩ := Correction.prodV_pair o c q
  rw [hp]
  exact ⟨hx, hy⟩

/-- A register of the site's live set holds its table value. -/
theorem corr_regAt {d : Correction.D} {t : TState} {s : Correction.Site} (hs : d.site = s)
    (h4 : Holds t.regs (Correction.facts L g d)) {r : Nat} (hl : r ∈ Flow.live s.pc) :
    t.regs r = some (Correction.valueOf L g d r) := by
  subst hs
  exact corr_reg h4 hl

/-- **No correction site's instruction is undefined behaviour.** -/
theorem corr_tmpl_ok (hpre : Pre P L mem0) (hg : g < L.threads) {d : Correction.D} {t : TState}
    (hi : Correction.Inv L g d)
    (h : t.pc = d.site.pc ∧ t.sub = d.site.sub ∧ t.acc = [] ∧ t.fault = none ∧
      Holds t.regs (Correction.facts L g d))
    {ins : Instr} (hc : kernel.code[d.site.pc]? = some ins) (f : Fault) :
    eventTmpl asms L g t ins.op ≠ .ub f := by
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  have h4 := h.2.2.2.2
  have hbase := hpre.sharedRange
  have hal := hpre.sharedAlignment
  unfold sharedBytes at hbase
  have hcta : g / L.block < L.grid := cta_lt hg
  have hgr := hpre.grid
  have hcl := hpre.cluster
  have hrow : Correction.rowOf L g < 128 := Nat.mod_lt _ (by decide)
  have hk : Correction.kOf L g < 4 := Nat.mod_lt _ (by decide)
  obtain ⟨v620, v621, v3939, v622, v623, v343, v628, v970, v661, v2733, v2991, v3249, v3253,
    v627, v299, v301⟩ := corr_ub_values L g d
  -- an arrival on the leader's barrier through its pointer
  have lead : ∀ {r c off : Nat} {o : Option Nat}, t.regs r = some (Correction.leadPtr L g off) →
      t.regs c = some (b32 1) → off < 1024 → off % 8 = 0 →
      eventTmpl asms L g t (.mbarArrive r 0 (.imm 0) (.reg c) true true .cta o) ≠ .ub f := by
    intro r c off o hr hcnt hoff h8
    have hm := mbarClusterLoc_ptr (L := L) (g := g) (t := t) (base := r)
      (cta := 2 * (g / L.block / 2)) (a := L.sharedBase + off) hr hg (by omega)
      (by simp only [Launch.oneDim_clusterOfCta hpre.oneDimLaunch.1, hcl]; omega) (by omega)
      (by omega)
    exact not_ub_of_fires (pc := 0) (fun f hf => by
      obtain ⟨_, _, he⟩ := fires_arrive_state_at (cluster := true) (by simpa using hm)
        (rfl : readBits L g t 32 (.imm 0) = _) (readBits_b32' hcnt) hf
      cases he) f
  -- an arrival on a barrier of the thread's CTA
  have own : ∀ {r c off : Nat} {o : Option Nat}, t.regs r = some (b32 (Correction.sb L + off)) →
      t.regs c = some (b32 1) → off < 1024 → off % 8 = 0 →
      eventTmpl asms L g t (.mbarArrive r 0 (.imm 0) (.reg c) false true .cta o) ≠ .ub f := by
    intro r c off o hr hcnt hoff h8
    have hm := mbarLoc_b32 (L := L) (g := g) hr (by simp only [Correction.sb]; omega)
      (by simp only [Correction.sb]; omega)
    exact not_ub_of_fires (pc := 0) (fun f hf => by
      obtain ⟨_, _, he⟩ := fires_arrive_state_at (cluster := false) (by simpa using hm)
        (rfl : readBits L g t 32 (.imm 0) = _) (readBits_b32' hcnt) hf
      cases he) f
  have reg : ∀ (s : Correction.Site) (r : Nat), r ∈ Flow.live s.pc → d.site = s →
      ∀ {v : Value}, Correction.valueOf L g d r = v → t.regs r = some v := by
    intro s r hl hs v hv
    rw [corr_regAt hs h4 hl, hv]
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hc h4 hi v3939 v299 v301 reg
  cases site
  case setMaxReg =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_5)
    exact plainOk_tmpl hb (by decide) f
  case bar0 =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_3)
    exact (bar_ok (by decide) (by decide) (by decide) (by decide) f).1
  case barEnd =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_barArrive_4)
    exact (bar_ok (by decide) (by decide) (by decide) (by decide) f).2
  case exit =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
    exact plainOk_tmpl hb rfl f
  case free st =>
    obtain rfl : i = 0 := hi.start (.inr (.inr ⟨st, rfl⟩))
    fin_cases st
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_14)
      exact lead (reg _ 620 (by decide +kernel) rfl (by rw [v620]))
        (reg _ 3939 (by decide +kernel) rfl (by rw [v3939])) (by decide) (by decide)
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_15)
      exact lead (reg _ 621 (by decide +kernel) rfl (by rw [v621]))
        (reg _ 3939 (by decide +kernel) rfl (by rw [v3939])) (by decide) (by decide)
  case sync st gen =>
    fin_cases st <;> cases gen
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_4)
      exact barSyncReg_ok (reg _ 622 (by decide +kernel) rfl (by rw [v622]))
        (by omega) (by decide) (by decide) (by decide) f
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_6)
      exact barSyncReg_ok (reg _ 622 (by decide +kernel) rfl (by rw [v622]))
        (by omega) (by decide) (by decide) (by decide) f
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_8)
      exact barSyncReg_ok (reg _ 622 (by decide +kernel) rfl (by rw [v622]))
        (by omega) (by decide) (by decide) (by decide) f
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_5)
      exact barSyncReg_ok (reg _ 623 (by decide +kernel) rfl (by rw [v623]))
        (by omega) (by decide) (by decide) (by decide) f
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_7)
      exact barSyncReg_ok (reg _ 623 (by decide +kernel) rfl (by rw [v623]))
        (by omega) (by decide) (by decide) (by decide) f
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_9)
      exact barSyncReg_ok (reg _ 623 (by decide +kernel) rfl (by rw [v623]))
        (by omega) (by decide) (by decide) (by decide) f
  case credit c =>
    fin_cases c
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_16)
      exact own (reg _ 343 (by decide +kernel) rfl (by rw [v343]))
        (reg _ 2733 (by decide +kernel) rfl (by rw [v2733])) (by decide) (by decide)
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_18)
      exact own (reg _ 628 (by decide +kernel) rfl (by rw [v628]))
        (reg _ 2991 (by decide +kernel) rfl (by rw [v2991])) (by decide) (by decide)
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_20)
      exact own (reg _ 343 (by decide +kernel) rfl (by rw [v343]))
        (reg _ 3249 (by decide +kernel) rfl (by rw [v3249])) (by decide) (by decide)
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_21)
      exact own (reg _ 628 (by decide +kernel) rfl (by rw [v628]))
        (reg _ 3253 (by decide +kernel) rfl (by rw [v3253])) (by decide) (by decide)
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_22)
      exact own (reg _ 343 (by decide +kernel) rfl (by rw [v343]))
        (reg _ 3253 (by decide +kernel) rfl (by rw [v3253])) (by decide) (by decide)
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_25)
      exact own (reg _ 628 (by decide +kernel) rfl (by rw [v628]))
        (reg _ 3253 (by decide +kernel) rfl (by rw [v3253])) (by decide) (by decide)
  case oFree st fin =>
    fin_cases st <;> cases fin
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_17)
      exact lead (reg _ 620 (by decide +kernel) rfl (by rw [v620]))
        (reg _ 2991 (by decide +kernel) rfl (by rw [v2991])) (by decide) (by decide)
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_23)
      exact lead (reg _ 620 (by decide +kernel) rfl (by rw [v620]))
        (reg _ 3253 (by decide +kernel) rfl (by rw [v3253])) (by decide) (by decide)
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_19)
      exact lead (reg _ 621 (by decide +kernel) rfl (by rw [v621]))
        (reg _ 3249 (by decide +kernel) rfl (by rw [v3249])) (by decide) (by decide)
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_26)
      exact lead (reg _ 621 (by decide +kernel) rfl (by rw [v621]))
        (reg _ 3253 (by decide +kernel) rfl (by rw [v3253])) (by decide) (by decide)
  case staged st =>
    fin_cases st
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_24)
      exact own (reg _ 970 (by decide +kernel) rfl (by rw [v970]))
        (reg _ 3253 (by decide +kernel) rfl (by rw [v3253])) (by decide) (by decide)
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_27)
      exact own (reg _ 661 (by decide +kernel) rfl (by rw [v661]))
        (reg _ 3253 (by decide +kernel) rfl (by rw [v3253])) (by decide) (by decide)
  case oWait st =>
    obtain ⟨⟨l1, l2⟩, ⟨l3, l4⟩, -⟩ := corr_wait_live
    obtain ⟨w1, w2, -, -, w5, -⟩ := corr_wait_values L g ⟨.oWait st, i, tt, aw, a, o⟩
    fin_cases st
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_36)
      exact wait_loc_ok (mbarLoc_b32 ((corr_regAt rfl h4 l1).trans (by rw [w1]))
        (by simp only [Correction.sb]; omega) (by simp only [Correction.sb]; omega))
        (readBits_b32' ((corr_regAt rfl h4 l2).trans (by rw [w5]))) f
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_38)
      exact wait_loc_ok (mbarLoc_b32 ((corr_regAt rfl h4 l3).trans (by rw [w2]))
        (by simp only [Correction.sb]; omega) (by simp only [Correction.sb]; omega))
        (readBits_b32' ((corr_regAt rfl h4 l4).trans (by rw [w5]))) f
  case fWait st =>
    obtain ⟨-, -, ⟨l5, l6⟩, ⟨l7, l8⟩, -⟩ := corr_wait_live
    obtain ⟨-, -, w3, w4, -, w6⟩ := corr_wait_values L g ⟨.fWait st, i, tt, aw, a, o⟩
    fin_cases st
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_37)
      exact wait_loc_ok (mbarLoc_b32 ((corr_regAt rfl h4 l5).trans (by rw [w3]))
        (by simp only [Correction.sb]; omega) (by simp only [Correction.sb]; omega))
        (readBits_b32' ((corr_regAt rfl h4 l6).trans (by rw [w6]))) f
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_39)
      exact wait_loc_ok (mbarLoc_b32 ((corr_regAt rfl h4 l7).trans (by rw [w4]))
        (by simp only [Correction.sb]; omega) (by simp only [Correction.sb]; omega))
        (readBits_b32' ((corr_regAt rfl h4 l8).trans (by rw [w6]))) f
  case tailWait =>
    obtain ⟨-, -, -, -, ⟨l9, l10⟩⟩ := corr_wait_live
    obtain ⟨-, -, -, w4, -, w6⟩ := corr_wait_values L g ⟨.tailWait, i, tt, aw, a, o⟩
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_40)
    exact wait_loc_ok (mbarLoc_b32 ((corr_regAt rfl h4 l9).trans (by rw [w4]))
      (by simp only [Correction.sb]; omega) (by simp only [Correction.sb]; omega))
      (readBits_b32' ((corr_regAt rfl h4 l10).trans (by rw [w6]))) f
  case ldA st =>
    have hs0 : t.sub = 0 := h.2.1
    fin_cases st
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_1)
      exact ld_off_ok (off := 332) (reg _ 627 (by decide +kernel) rfl (by rw [v627]))
        (by simp only [Correction.sb]; omega) (by simp only [Correction.sb]; omega) hs0 f
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_2)
      exact ld_off_ok (off := 844) (reg _ 627 (by decide +kernel) rfl (by rw [v627]))
        (by simp only [Correction.sb]; omega) (by simp only [Correction.sb]; omega) hs0 f
  case ldL st =>
    have hs0 : t.sub = 0 := h.2.1
    fin_cases st
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_3)
      exact ld_off_ok (off := 332) (reg _ 627 (by decide +kernel) rfl (by rw [v627]))
        (by simp only [Correction.sb]; omega) (by simp only [Correction.sb]; omega) hs0 f
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_4)
      exact ld_off_ok (off := 844) (reg _ 627 (by decide +kernel) rfl (by rw [v627]))
        (by simp only [Correction.sb]; omega) (by simp only [Correction.sb]; omega) hs0 f
  case vote st =>
    fin_cases st
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_vote_0)
      exact vote_ok hb (reg _ 299 (by decide +kernel) rfl (by rw [v299])) f
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_vote_1)
      exact vote_ok hb (reg _ 301 (by decide +kernel) rfl (by rw [v301])) f
  case rld st j =>
    obtain rfl := Option.some.inj (hc.symm.trans (Correction.code_rld st j))
    have hr := corr_regAt rfl h4 (Correction.ldAddr_live st j).1
    rw [Correction.ldAddr_val] at hr
    exact tcLd_ok hb
      (by rw [(Correction.rldRegs_ok ⟨8 * st.val + j.val, by omega⟩).1]; decide) hr
      (Correction.tmem_lt L g _ (by omega)) (corr_tmem_supported _ (by omega)) f
  case fld st j =>
    obtain rfl := Option.some.inj (hc.symm.trans (Correction.code_fld st j))
    have hr := corr_regAt rfl h4 (Correction.ldAddr_live st j).2
    rw [Correction.ldAddr_val] at hr
    exact tcLd_ok hb
      (by rw [(Correction.fldRegs_ok ⟨8 * st.val + j.val, by omega⟩).1]; decide) hr
      (Correction.tmem_lt L g _ (by omega)) (corr_tmem_supported _ (by omega)) f
  case rldW st j =>
    obtain rfl := Option.some.inj (hc.symm.trans (Correction.code_rld st j))
    exact tcLdWait_ok (by rw [h.1]; exact Correction.tcLdWait_rld st j)
      (by rw [h.2.1]; simp [Correction.Site.sub]) f
  case fldW st j =>
    obtain rfl := Option.some.inj (hc.symm.trans (Correction.code_fld st j))
    exact tcLdWait_ok (by rw [h.1]; exact Correction.tcLdWait_fld st j)
      (by rw [h.2.1]; simp [Correction.Site.sub]) f
  case rst st j =>
    obtain rfl := Option.some.inj (hc.symm.trans (Correction.code_rst_spec st j))
    have hr := corr_regAt rfl h4 (Correction.ldAddr_live_rst st j)
    rw [Correction.ldAddr_val] at hr
    obtain ⟨vals, hm, hv4⟩ := mapM_regs_ok (L := L) (g := g) (t := t)
      (ss := Correction.rstSrcs st.val j.val) fun p hp => by
        simp only [Correction.rstSrcs, List.length_map, List.length_range] at hp
        refine ⟨Correction.rstReg st.val j.val p, _, by simp [Correction.rstSrcs, hp],
          (corr_regAt rfl h4 (Correction.rst_live st j ⟨p, hp⟩)).trans
            (by rw [Correction.rstReg_value L g _ st j ⟨p, hp⟩]), ?_⟩
        simp only [Correction.rs]
        split_ifs
        exacts [(prodV_split_bytes _ _ _).1, (prodV_split_bytes _ _ _).2]
    exact tcSt_ok hb (by simp [Correction.rstSrcs]; decide) hr (Correction.tmem_lt L g _ (by omega))
      (corr_tmem_supported _ (by omega)) hm hv4 f
  case rwait st =>
    fin_cases st
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemWait_4)
      exact plainOk_tmpl hb rfl f
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemWait_5)
      exact plainOk_tmpl hb rfl f
  case fence st =>
    fin_cases st
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceProxy_0)
      exact plainOk_tmpl hb rfl f
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceProxy_1)
      exact plainOk_tmpl hb rfl f
  case fst st j hh el =>
    obtain rfl := Option.some.inj (hc.symm.trans (Correction.code_fst_spec st j hh el))
    have hl := Correction.fst_live st j hh el
    have hr := (corr_regAt rfl h4 hl.1).trans
      (by rw [Correction.fstBase_value L g _ st ⟨_, by omega⟩])
    have hv := (corr_regAt rfl h4 hl.2).trans
      (by rw [Correction.fwReg_value L g _ st j ⟨_, by omega⟩])
    have hlt := Correction.stage_lt (g := g) hpre st.val (2 * (j.val % 4) + hh.val) st.isLt
      (by omega)
    have hsub : t.sub = el.val := h.2.1
    simp only at hr
    refine stv_off_ok hr rfl (by omega) (by simp [Correction.fstSrcs]) ?_
      (by rw [hsub]; simp [Correction.fstSrcs]) hv
      (by simp only [Correction.fw, cvtOfPair, cvtPairV_bytes]) f
    have hx : Correction.lnOf L g % 8 ^^^ (2 * (j.val % 4) + hh.val) < 2 ^ 3 :=
      Nat.xor_lt_two_pow (Nat.mod_lt _ (by decide)) (by omega)
    simp only [Correction.fstSrcs, List.length_map, List.length_range]
    unfold Correction.stage
    simp only [Correction.sb]
    omega

end

/-- **The correction part of `Cross.SitesTmplOk`**: at a correction state of the composed machine,
the site's instruction has no undefined-behaviour template. -/
theorem Cross.SitesTmplOk_corr {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0)
    {g : Nat} (hg : g < L.threads) (d : Correction.D) (t : TState) (ins : Instr)
    (hat : (code L g).AtD (.inr (.corr d)) t) (hi : (code L g).inv (.inr (.corr d)))
    (hc : kernel.code[(code L g).pc (.inr (.corr d))]? = some ins) (f : Fault) :
    eventTmpl asms L g t ins.op ≠ .ub f :=
  corr_tmpl_ok hpre hg hi hat hc f

end PTX.Kernels.FlashAttn4Fwd.Proof
