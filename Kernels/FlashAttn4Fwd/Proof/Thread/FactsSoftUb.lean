-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftPack
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSoftPKeys
public import Lemmas.Flow.TmplOkMore

@[expose] public section

/-! # The softmax sites are not undefined behaviour

At every site of the softmax role the instruction's event is not undefined behaviour (the
softmax part of `Cross.SitesTmplOk`): the register request and the return are plain; the start
and end barriers and the statistics barriers have ids below 16 and the counts 416 and 64; the
polls and arrivals name barriers through registers of the state; the loads and stores name the
warp's lanes of the stage's columns and store packed half-precision pairs; the statistics
stores write a 4-byte register to an aligned word; the warp barriers and elections use the full
mask; the implicit waits are the waits. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {t : TState} {d : D}

/-- The warp's lanes of a column of its stage are a supported Tensor Memory address. -/
theorem tmem_supported (hw : warpOf L g < 8) (col : Nat) (hc : col < 256) :
    tcDataAddressOk L g .s32x32b (tmem L g col) = true := by
  have hk : kOf L g < 4 := Nat.mod_lt _ (by decide)
  have hst : stOf L g < 2 := by simp only [stOf]; omega
  have hf : tmem L g col / 2 ^ 16 = 32 * kOf L g := by simp only [tmem]; omega
  have hk' : kOf L g = g % L.block / 32 % 4 := rfl
  show tmemLaneFieldOk L g (tmem L g col / 2 ^ 16) 32 = true
  rw [hf]
  have hl : laneBase L g = 32 * kOf L g := by simp only [laneBase]; omega
  simp [tmemLaneFieldOk, hl]

/-- A barrier register of the state names a barrier of the CTA. -/
theorem mbarLoc_sb (hpre : Pre P L mem0) {base off : Nat} (hr : t.regs base = some
    (Prologue.sb L off)) (hoff : off < 1024) (h8 : off % 8 = 0) :
    mbarLoc L g t base 0 = .ok ⟨.shared, g / L.block, L.sharedBase + off⟩ := by
  have hbase := hpre.sharedRange
  have hal := hpre.sharedAlignment
  unfold sharedBytes at hbase
  simp only [Prologue.sb] at hr
  exact mbarLoc_b32 hr (by omega) (by omega)

theorem tmpl_ok_wait (hpre : Pre P L mem0) (hi : Inv L g d) (h : AtS L g d t) {ins : Instr}
    (hc : kernel.code[d.site.pc]? = some ins) (f : Fault)
    (hs : (∃ w, d.site = .statsW w) ∨ ∃ lp, d.site = .sW lp) :
    eventTmpl asms L g t ins.op ≠ .ub f := by
  have h4 := h.2.2.2.2
  have hst : stOf L g < 2 := by have := hi.warp; simp only [stOf]; omega
  rcases hs with ⟨w, hsd⟩ | ⟨lp, hsd⟩ <;> rw [hsd] at hc
  · rcases fin4_cases w with rfl | rfl | rfl | rfl
    · obtain ⟨r1, r2⟩ := regs_statsW0 hsd h4
      obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_30)
      exact wait_loc_ok (mbarLoc_sb hpre r1 (by omega) (by omega)) (readBits_b32' r2) f
    · obtain ⟨r1, r2⟩ := regs_statsW1 hsd h4
      obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_32)
      exact wait_loc_ok (mbarLoc_sb hpre r1 (by omega) (by omega)) (readBits_b32' r2) f
    · obtain ⟨r1, r2⟩ := regs_statsW2 hsd h4
      obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_34)
      exact wait_loc_ok (mbarLoc_sb hpre r1 (by omega) (by omega)) (readBits_b32' r2) f
    · obtain ⟨r1, r2⟩ := regs_statsW3 hsd h4
      obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_35)
      exact wait_loc_ok (mbarLoc_sb hpre r1 (by omega) (by omega)) (readBits_b32' r2) f
  · cases lp
    · obtain ⟨r1, r2⟩ := regs_sW0 hsd h4
      obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_31)
      exact wait_loc_ok (mbarLoc_sb hpre r1 (by omega) (by omega)) (readBits_b32' r2) f
    · obtain ⟨r1, r2⟩ := regs_sW1 hsd h4
      obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarWait_33)
      exact wait_loc_ok (mbarLoc_sb hpre r1 (by omega) (by omega)) (readBits_b32' r2) f

theorem tmpl_ok_arrive (hpre : Pre P L mem0) (hg : g < L.threads) (hi : Inv L g d)
    (h : AtS L g d t) {ins : Instr} (hc : kernel.code[d.site.pc]? = some ins) (f : Fault)
    (hs : (∃ lp, d.site = .pArr lp) ∨ ∃ lp, d.site = .p2Arr lp) :
    eventTmpl asms L g t ins.op ≠ .ub f := by
  have h4 := h.2.2.2.2
  have hst : stOf L g < 2 := by have := hi.warp; simp only [stOf]; omega
  have hbase := hpre.sharedRange
  have hal := hpre.sharedAlignment
  unfold sharedBytes at hbase
  have hcta : g / L.block < L.grid := cta_lt hg
  have hgr := hpre.grid
  have hcl := hpre.cluster
  have key : ∀ {r c off : Nat}, t.regs r = some (leadPtr L g off) → t.regs c = some (b32 1) →
      off < 1024 → off % 8 = 0 →
      eventTmpl asms L g t (.mbarArrive r 0 (.imm 0) (.reg c) true true .cta none) ≠ .ub f := by
    intro r c off hr hcnt hoff h8
    have hm := mbarClusterLoc_ptr (L := L) (g := g) (t := t) (base := r)
      (cta := 2 * (g / L.block / 2)) (a := L.sharedBase + off) hr hg (by omega)
      (by simp only [Launch.oneDim_clusterOfCta hpre.oneDimLaunch.1, hcl]; omega) (by omega)
      (by omega)
    exact arrive_loc_ok (cluster := true) (by simpa using hm)
      (rfl : readBits L g t 32 (.imm 0) = _) (readBits_b32' hcnt) f
  rcases hs with ⟨lp, hsd⟩ | ⟨lp, hsd⟩ <;> rw [hsd] at hc <;> cases lp
  · obtain ⟨r1, r2⟩ := regs_pArr0 hsd h4
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_10)
    exact key r1 r2 (by omega) (by omega)
  · obtain ⟨r1, r2⟩ := regs_pArr1 hsd h4
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_12)
    exact key r1 r2 (by omega) (by omega)
  · obtain ⟨r1, r2⟩ := regs_p2Arr0 hsd h4
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_11)
    exact key r1 r2 (by omega) (by omega)
  · obtain ⟨r1, r2⟩ := regs_p2Arr1 hsd h4
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_13)
    exact key r1 r2 (by omega) (by omega)

theorem tmpl_ok_ld (hpre : Pre P L mem0) (hi : Inv L g d) (h : AtS L g d t) {ins : Instr}
    (hc : kernel.code[d.site.pc]? = some ins) (f : Fault) {lp : Bool} {c : Fin 4}
    (hsd : d.site = .ld lp c) : eventTmpl asms L g t ins.op ≠ .ub f := by
  have h4 := h.2.2.2.2
  have hw := hi.warp
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  have key : ∀ {ds : List Nat} {ta col : Nat},
      kernel.code[d.site.pc]? = some ⟨none, .tcLd ds ta⟩ → ds.length = 32 →
      t.regs ta = some (b32 (tmem L g col)) → col < 256 →
      eventTmpl asms L g t ins.op ≠ .ub f := by
    intro ds ta col hcd hl hr hcol
    obtain rfl := Option.some.inj (hc.symm.trans hcd)
    exact tcLd_ok hb (by rw [hl]; decide) hr (tmem_lt hw _ (by omega))
      (tmem_supported hw col hcol) f
  cases lp <;> rcases fin4_cases c with rfl | rfl | rfl | rfl
  · exact key (by rw [hsd]; exact Flow.code_tmemLoad_0) rfl (regs_ldF0 hsd h4) (by decide)
  · exact key (by rw [hsd]; exact Flow.code_tmemLoad_1) rfl (regs_ldF1 hsd h4) (by decide)
  · exact key (by rw [hsd]; exact Flow.code_tmemLoad_2) rfl (regs_ldF2 hsd h4) (by decide)
  · exact key (by rw [hsd]; exact Flow.code_tmemLoad_3) rfl (regs_ldF3 hsd h4) (by decide)
  · exact key (by rw [hsd]; exact Flow.code_tmemLoad_4) rfl (regs_ldT0 hsd h4) (by decide)
  · exact key (by rw [hsd]; exact Flow.code_tmemLoad_5) rfl (regs_ldT1 hsd h4) (by decide)
  · exact key (by rw [hsd]; exact Flow.code_tmemLoad_6) rfl (regs_ldT2 hsd h4) (by decide)
  · exact key (by rw [hsd]; exact Flow.code_tmemLoad_7) rfl (regs_ldT3 hsd h4) (by decide)

theorem tmpl_ok_pst (hpre : Pre P L mem0) (hi : Inv L g d) (h : AtS L g d t) {ins : Instr}
    (hc : kernel.code[d.site.pc]? = some ins) (f : Fault) {lp : Bool} {c : Fin 4}
    (hsd : d.site = .pst lp c) : eventTmpl asms L g t ins.op ≠ .ub f := by
  have h4 := h.2.2.2.2
  have hw := hi.warp
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  obtain ⟨ta, ss, hcd, hl⟩ := pst_len lp c
  rw [hsd] at hc
  obtain rfl := Option.some.inj (hc.symm.trans hcd)
  have hp : ∀ p < 16, ∃ r v, ss[p]? = some (.reg r) ∧ t.regs r = some v ∧ v.bytes = 4 := by
    cases lp <;> rcases fin4_cases c with rfl | rfl | rfl | rfl
    · exact pst_bytes_0 hsd h4 hcd
    · exact pst_bytes_1 hsd h4 hcd
    · exact pst_bytes_2 hsd h4 hcd
    · exact pst_bytes_3 hsd h4 hcd
    · exact pst_bytes_4 hsd h4 hcd
    · exact pst_bytes_5 hsd h4 hcd
    · exact pst_bytes_6 hsd h4 hcd
    · exact pst_bytes_7 hsd h4 hcd
  obtain ⟨vals, hm, h4b⟩ := mapM_regs_ok (L := L) (g := g) (t := t) (ss := ss) fun p hp' =>
    hp p (by omega)
  have key : ∀ {col : Nat}, t.regs ta = some (b32 (tmem L g col)) → col < 256 →
      eventTmpl asms L g t (.tcSt ta ss) ≠ .ub f := fun hr hcol =>
    tcSt_ok hb (by rw [hl]; decide) hr (tmem_lt hw _ (by omega)) (tmem_supported hw _ hcol) hm
      h4b f
  have hta : ∀ lp' c', ∀ hs : d.site = .pst lp' c',
      kernel.code[(Site.pst lp' c').pc]? = some ⟨none, .tcSt ta ss⟩ →
      ∃ col < 256, t.regs ta = some (b32 (tmem L g col)) := by
    intro lp' c' hs hcd'
    cases lp' <;> rcases fin4_cases c' with rfl | rfl | rfl | rfl
    · obtain rfl := congrArg (fun i : Instr => match i.op with | .tcSt a _ => a | _ => 0)
        (Option.some.inj (hcd'.symm.trans Flow.code_tmemStore_0))
      exact ⟨_, by decide, regs_pstF0 hs h4⟩
    · obtain rfl := congrArg (fun i : Instr => match i.op with | .tcSt a _ => a | _ => 0)
        (Option.some.inj (hcd'.symm.trans Flow.code_tmemStore_1))
      exact ⟨_, by decide, regs_pstF1 hs h4⟩
    · obtain rfl := congrArg (fun i : Instr => match i.op with | .tcSt a _ => a | _ => 0)
        (Option.some.inj (hcd'.symm.trans Flow.code_tmemStore_2))
      exact ⟨_, by decide, regs_pstF2 hs h4⟩
    · obtain rfl := congrArg (fun i : Instr => match i.op with | .tcSt a _ => a | _ => 0)
        (Option.some.inj (hcd'.symm.trans Flow.code_tmemStore_3))
      exact ⟨_, by decide, regs_pstF3 hs h4⟩
    · obtain rfl := congrArg (fun i : Instr => match i.op with | .tcSt a _ => a | _ => 0)
        (Option.some.inj (hcd'.symm.trans Flow.code_tmemStore_4))
      exact ⟨_, by decide, regs_pstT0 hs h4⟩
    · obtain rfl := congrArg (fun i : Instr => match i.op with | .tcSt a _ => a | _ => 0)
        (Option.some.inj (hcd'.symm.trans Flow.code_tmemStore_5))
      exact ⟨_, by decide, regs_pstT1 hs h4⟩
    · obtain rfl := congrArg (fun i : Instr => match i.op with | .tcSt a _ => a | _ => 0)
        (Option.some.inj (hcd'.symm.trans Flow.code_tmemStore_6))
      exact ⟨_, by decide, regs_pstT2 hs h4⟩
    · obtain rfl := congrArg (fun i : Instr => match i.op with | .tcSt a _ => a | _ => 0)
        (Option.some.inj (hcd'.symm.trans Flow.code_tmemStore_7))
      exact ⟨_, by decide, regs_pstT3 hs h4⟩
  obtain ⟨col, hcol, hr⟩ := hta lp c hsd hcd
  exact key hr hcol

/-- **No site of the softmax has an undefined-behaviour template.** -/
theorem tmpl_ok (hpre : Pre P L mem0) (hg : g < L.threads) (hi : Inv L g d) (h : AtS L g d t)
    {ins : Instr} (hc : kernel.code[d.site.pc]? = some ins) (f : Fault) :
    eventTmpl asms L g t ins.op ≠ .ub f := by
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  have h4 := h.2.2.2.2
  have hbase := hpre.sharedRange
  have hal := hpre.sharedAlignment
  unfold sharedBytes at hbase
  have htid : tidOf L g < 512 := by
    simp only [tidOf, hpre.block]; exact Nat.mod_lt _ (by decide)
  have hst : stOf L g < 2 := by have := hi.warp; simp only [stOf]; omega
  cases hsd : d.site with
  | statsW w => exact tmpl_ok_wait hpre hi h hc f (.inl ⟨w, hsd⟩)
  | sW lp => exact tmpl_ok_wait hpre hi h hc f (.inr ⟨lp, hsd⟩)
  | pArr lp => exact tmpl_ok_arrive hpre hg hi h hc f (.inl ⟨lp, hsd⟩)
  | p2Arr lp => exact tmpl_ok_arrive hpre hg hi h hc f (.inr ⟨lp, hsd⟩)
  | ld lp c => exact tmpl_ok_ld hpre hi h hc f hsd
  | pst lp c => exact tmpl_ok_pst hpre hi h hc f hsd
  | setMaxReg =>
    rw [hsd] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_4)
    exact plainOk_tmpl hb (by decide) f
  | exit =>
    rw [hsd] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
    exact plainOk_tmpl hb rfl f
  | bar0 =>
    rw [hsd] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_2)
    exact (bar_ok (by decide) (by decide) (by decide) (by decide) f).1
  | barEnd =>
    rw [hsd] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_barArrive_3)
    exact (bar_ok (by decide) (by decide) (by decide) (by decide) f).2
  | gen j =>
    have hr := regs_gen hsd h4
    have hk : kOf L g < 4 := Nat.mod_lt _ (by decide)
    rw [hsd] at hc
    rcases fin3_cases j with rfl | rfl | rfl
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_barArrive_0)
      exact barReg_ok hr (by omega) (by decide) (by decide) (by decide) f
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_barArrive_1)
      exact barReg_ok hr (by omega) (by decide) (by decide) (by decide) f
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_barArrive_2)
      exact barReg_ok hr (by omega) (by decide) (by decide) (by decide) f
  | ldW lp c =>
    obtain ⟨ds, ta, hcd⟩ := code_ldW lp c
    rw [hsd] at hc
    obtain rfl := Option.some.inj (hc.symm.trans hcd)
    have hw : asms.any (·.tcLdWait t.pc) = true := by
      rw [h.1, hsd]
      cases lp
      · exact tcLdWait_ld false c
      · exact tcLdWait_ld true c
    exact tcLdWait_ok hw (by rw [h.2.1, hsd]; simp [Site.sub]) f
  | alphaSt =>
    obtain ⟨r1, r2⟩ := regs_alphaSt hsd h4
    simp only [Prologue.sb] at r1
    rw [hsd] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_store_0)
    exact st_ok (off := 332) r1 (by omega) (by omega) (by rw [h.2.1, hsd]; rfl) r2
      (alphaV_bytes L d) f
  | lSt =>
    obtain ⟨r1, r2⟩ := regs_lSt hsd h4
    simp only [Prologue.sb] at r1
    rw [hsd] at hc
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_store_1)
    exact st_ok (off := 332) r1 (by omega) (by omega) (by rw [h.2.1, hsd]; rfl) r2
      hi.lBytes f
  | pwait lp hh =>
    rw [hsd] at hc
    have hop : ins.op = .tcWaitSt := by
      cases lp <;> rcases fin2_cases hh with rfl | rfl
      · exact congrArg Instr.op (Option.some.inj (hc.symm.trans Flow.code_tmemWait_0))
      · exact congrArg Instr.op (Option.some.inj (hc.symm.trans Flow.code_tmemWait_1))
      · exact congrArg Instr.op (Option.some.inj (hc.symm.trans Flow.code_tmemWait_2))
      · exact congrArg Instr.op (Option.some.inj (hc.symm.trans Flow.code_tmemWait_3))
    rw [hop]
    exact plainOk_tmpl hb rfl f
  | warpBar lp =>
    rw [hsd] at hc
    have hop : ins.op = .warp ⟨.barWarp, none, [], [], some (.imm (-1))⟩ := by
      cases lp
      · exact congrArg Instr.op (Option.some.inj (hc.symm.trans Flow.code_warpBar_0))
      · exact congrArg Instr.op (Option.some.inj (hc.symm.trans Flow.code_warpBar_1))
    rw [hop]
    exact warpBar_ok f
  | el lp =>
    rw [hsd] at hc
    cases lp
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_52)
      exact elect_imm_ok f
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_53)
      exact elect_imm_ok f

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

/-- **The softmax part of `Cross.SitesTmplOk`**: at a softmax state of the composed machine, the
site's instruction has no undefined-behaviour template. -/
theorem Cross.SitesTmplOk_soft {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0)
    {g : Nat} (hg : g < L.threads) (d : Softmax.D) (t : TState) (ins : Instr)
    (hat : (code L g).AtD (.inr (.softmax d)) t) (hi : (code L g).inv (.inr (.softmax d)))
    (hc : kernel.code[(code L g).pc (.inr (.softmax d))]? = some ins) (f : Fault) :
    eventTmpl asms L g t ins.op ≠ .ub f :=
  Softmax.tmpl_ok hpre hg hi hat hc f

end PTX.Kernels.FlashAttn4Fwd.Proof
