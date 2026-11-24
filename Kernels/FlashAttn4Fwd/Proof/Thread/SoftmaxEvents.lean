-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxCounts
public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.WaitLd
public import Lemmas.Flow.StoreLoc
public import Lemmas.Flow.BarReg

@[expose] public section

/-! # The softmax warps' events by site

The event a softmax state fires and continues after is the event of its site (`Ev`), read off
its instruction and the site's register facts: the polls name the stage's barrier in the
thread's CTA, the arrivals the leader CTA's barrier through its `mapa` pointer, the Tensor
Memory loads and stores the stage's columns, the stores of the statistics word the thread's
word, the named barriers their ids. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {t u : TState} {e : Event}
  {ins : Instr}

theorem reg_val {d : D} (h : Holds t.regs (facts L g d)) {r : Nat}
    (hl : r ∈ Flow.live d.site.pc ++ d.site.extra) : t.regs r = some (valueOf L g d r) :=
  holds_mem h (mem_factsFrom hl)

/-- A register fact of the table, at a concrete site. -/
syntax "regv " term:max term:max : term
macro_rules
  | `(regv $h $r) => `((by
      have hh := reg_val (r := $r) $h (by table_decide)
      simp only [valueOf, ctrlValues, PTX.Flow.lookupLit, Option.getD_some] at hh
      exact hh))

/-- A poll of the thread's CTA's barrier at `off`. -/
theorem ev_waitOwn {pc p r q off x : Nat} (hpre : Pre P L mem0)
    (hc : kernel.code[pc]? = some ⟨none, .mbarWait p r 0 (.reg q) true .cta⟩)
    (hr : t.regs r = some (Prologue.sb L off)) (hq : t.regs q = some (b32 x))
    (hoff : off < 1024) (h8 : off % 8 = 0) (hins : kernel.code[pc]? = some ins)
    (hf : Fires pc (eventTmpl asms L g t ins.op) e (some u)) :
    ∃ par ok acq sc, e.kind = .wait (ownLoc L g off) par ok acq sc := by
  obtain rfl := Option.some.inj (hins.symm.trans hc)
  have hbase := hpre.sharedRange
  have hal := hpre.sharedAlignment
  unfold sharedBytes at hbase
  simp only [Prologue.sb] at hr
  obtain ⟨ok, acq, sc, he, -⟩ := fires_wait_at (L := L) (g := g) (A := asms)
    (mbarLoc_b32 (L := L) (g := g) hr (by omega) (by omega)) (readBits_b32' hq) hf
  exact ⟨_, ok, acq, sc, by rw [he]; rfl⟩

/-- An arrival on the leader CTA's barrier at `off`, through its `mapa` pointer. -/
theorem ev_arriveLead {pc r c off : Nat} (hpre : Pre P L mem0) (hg : g < L.threads)
    (hc : kernel.code[pc]? = some ⟨none, .mbarArrive r 0 (.imm 0) (.reg c) true true .cta none⟩)
    (hr : t.regs r = some (leadPtr L g off)) (hcnt : t.regs c = some (b32 1))
    (hoff : off < 1024) (h8 : off % 8 = 0) (hins : kernel.code[pc]? = some ins)
    (hf : Fires pc (eventTmpl asms L g t ins.op) e (some u)) :
    ∃ tx n rel sc, e.kind = .arrive (leadLoc L g off) tx n rel sc := by
  obtain rfl := Option.some.inj (hins.symm.trans hc)
  have hbase := hpre.sharedRange
  have hal := hpre.sharedAlignment
  unfold sharedBytes at hbase
  have hcta : g / L.block < L.grid := cta_lt hg
  have hgr := hpre.grid
  have hcl := hpre.cluster
  have hm := mbarClusterLoc_ptr (L := L) (g := g) (t := t) (base := r)
    (cta := 2 * (g / L.block / 2)) (a := L.sharedBase + off) hr hg (by omega)
    (by simp only [Launch.oneDim_clusterOfCta hpre.oneDimLaunch.1, hcl]; omega) (by omega)
    (by omega)
  obtain ⟨rel, sc, he, -⟩ := fires_arrive_at (L := L) (g := g) (A := asms) (cluster := true)
    (by simpa using hm) (rfl : readBits L g t 32 (.imm 0) = _) (readBits_b32' hcnt) hf
  exact ⟨_, _, rel, sc, by rw [he]; rfl⟩

/-- A store of the statistics word. -/
theorem ev_word {pc r src : Nat} {ik : IType} (hpre : Pre P L mem0)
    (hc : kernel.code[pc]? = some ⟨none, .mem
      { kind := .store, space := some (.shared .cta), sem := .weak, elem := .int ik 32,
        addr := ⟨.reg r 32, 332⟩, srcs := [.reg src] }⟩)
    (hr : t.regs r = some (Prologue.sb L (4 * tidOf L g))) (hs : t.sub = 0)
    (hins : kernel.code[pc]? = some ins)
    (hf : Fires pc (eventTmpl asms L g t ins.op) e (some u)) :
    ∃ sz acq rel sc el rx bs, e.kind = .wr ⟨statsWord L g, sz, acq, rel, sc, el, rx⟩ bs := by
  obtain rfl := Option.some.inj (hins.symm.trans hc)
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have ht : tidOf L g < 512 := by
    simp only [tidOf, hpre.block]; exact Nat.mod_lt _ (by decide)
  simp only [Prologue.sb] at hr
  obtain ⟨⟨loc, sz, acq, rel, sc, el, rx⟩, bs, he, hl⟩ :=
    fires_st_loc (off := 332) hr (by omega) hs hf
  simp only at hl
  subst hl
  refine ⟨sz, acq, rel, sc, el, rx, bs, by rw [he]; congr 3; simp only [sb]; omega⟩

/-- A score load of the stage's columns at `col`. -/
theorem ev_ld {d : D} {lp : Bool} {c : Fin 4} {ds : List Nat} {ta col : Nat}
    (hs : d.site = .ld lp c) (hw : warpOf L g < 8) (h : AtS L g d t)
    (hcode : kernel.code[d.site.pc]? = some ⟨none, .tcLd ds ta⟩)
    (hr : t.regs ta = some (b32 (tmem L g col))) (hcol : col = 32 * c.val)
    (hins : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    ∃ vals, e.kind = .tc (.ld (tmem L g (32 * c.val)) vals .s32x32b) := by
  obtain rfl := Option.some.inj (hins.symm.trans hcode)
  have hwt : asms.any (·.tcLdWait t.pc) = true := by
    rw [h.1, hs]; exact tcLdWait_ld lp c
  have hsub : t.sub = 0 := by rw [h.2.1, hs]; rfl
  subst hcol
  obtain ⟨vals, -, he, -⟩ := fires_tcLd_load (fun _ => by simp) hwt hsub hr
    (tmem_lt hw _ (by have := c.isLt; omega)) hf
  exact ⟨vals, by rw [he]⟩

theorem at_of {d : D} (h : AtS L g d t) (hs : d.site.sub = 0) : At t d.site.pc (facts L g d) :=
  ⟨h.1, h.2.1.trans hs, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

set_option maxHeartbeats 8000000 in
/-- **The event a state fires and continues after is the event of its site.** -/
theorem site_event (hpre : Pre P L mem0) (hg : g < L.threads) {d : D} (hi : Inv L g d)
    (h : AtS L g d t) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Ev L g d e := by
  have h4 := h.2.2.2.2
  have hw8 := hi.warp
  have hst : stOf L g < 2 := by simp only [stOf]; omega
  have hk : kOf L g < 4 := Nat.mod_lt _ (by decide)
  obtain ⟨s, i, tt, sc, m, l⟩ := d
  cases s with
  | setMaxReg =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_4)
    simp only [eventTmpl, SetMaxNReg.tmpl] at hf
    split_ifs at hf
    · obtain ⟨inst, rfl, -⟩ := hf
      exact ⟨inst, rfl⟩
    · simp [Fires] at hf
  | bar0 =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_2)
    obtain ⟨rfl, -⟩ := fires_barSync_imm (id := 2) (n := 416) (by decide) (by decide)
      (by decide) (by decide) (by rw [hpre.block]; decide) hf
    rfl
  | statsW w =>
    rcases fin4_cases w with rfl | rfl | rfl | rfl
    · exact ev_waitOwn hpre Flow.code_mbarWait_30 (regv h4 1006) (regv h4 3934) (by omega)
        (by omega) hc hf
    · exact ev_waitOwn hpre Flow.code_mbarWait_32 (regv h4 1974) (regv h4 1975) (by omega)
        (by omega) hc hf
    · exact ev_waitOwn hpre Flow.code_mbarWait_34 (regv h4 2687) (regv h4 3934) (by omega)
        (by omega) hc hf
    · exact ev_waitOwn hpre Flow.code_mbarWait_35 (regv h4 2700) (regv h4 3934) (by omega)
        (by omega) hc hf
  | sW lp =>
    cases lp
    · exact ev_waitOwn hpre Flow.code_mbarWait_31 (regv h4 1007) (regv h4 3935) (by omega)
        (by omega) hc hf
    · exact ev_waitOwn hpre Flow.code_mbarWait_33 (regv h4 1980) (regv h4 3935) (by omega)
        (by omega) hc hf
  | ld lp c =>
    cases lp <;> rcases fin4_cases c with rfl | rfl | rfl | rfl
    · exact ev_ld rfl hw8 h Flow.code_tmemLoad_0 (regv h4 1094) rfl hc hf
    · exact ev_ld rfl hw8 h Flow.code_tmemLoad_1 (regv h4 1096) rfl hc hf
    · exact ev_ld rfl hw8 h Flow.code_tmemLoad_2 (regv h4 1097) rfl hc hf
    · exact ev_ld rfl hw8 h Flow.code_tmemLoad_3 (regv h4 1095) rfl hc hf
    · exact ev_ld rfl hw8 h Flow.code_tmemLoad_4 (regv h4 2057) rfl hc hf
    · exact ev_ld rfl hw8 h Flow.code_tmemLoad_5 (regv h4 2059) rfl hc hf
    · exact ev_ld rfl hw8 h Flow.code_tmemLoad_6 (regv h4 2060) rfl hc hf
    · exact ev_ld rfl hw8 h Flow.code_tmemLoad_7 (regv h4 2058) rfl hc hf
  | ldW lp c =>
    obtain ⟨he, -⟩ := ldW_at (d := ⟨.ldW lp c, i, tt, sc, m, l⟩) rfl h hc hf
    show e.kind = _
    rw [he]
  | alphaSt =>
    exact ev_word hpre Flow.code_store_0 (regv h4 2395) h.2.1 hc hf
  | lSt =>
    exact ev_word hpre Flow.code_store_1 (regv h4 2699) h.2.1 hc hf
  | gen j =>
    rcases fin3_cases j with rfl | rfl | rfl
    · have hr : t.regs 1017 = some (b32 (kOf L g + 3 + 4 * stOf L g)) := regv h4 1017
      obtain rfl := Option.some.inj (hc.symm.trans Flow.code_barArrive_0)
      obtain ⟨rfl, -⟩ := fires_barArrive_reg hr (by omega) (by decide) (by decide) (by decide)
        (by rw [hpre.block]; decide) hf
      rfl
    · have hr : t.regs 1017 = some (b32 (kOf L g + 3 + 4 * stOf L g)) := regv h4 1017
      obtain rfl := Option.some.inj (hc.symm.trans Flow.code_barArrive_1)
      obtain ⟨rfl, -⟩ := fires_barArrive_reg hr (by omega) (by decide) (by decide) (by decide)
        (by rw [hpre.block]; decide) hf
      rfl
    · have hr : t.regs 1017 = some (b32 (kOf L g + 3 + 4 * stOf L g)) := regv h4 1017
      obtain rfl := Option.some.inj (hc.symm.trans Flow.code_barArrive_2)
      obtain ⟨rfl, -⟩ := fires_barArrive_reg hr (by omega) (by decide) (by decide) (by decide)
        (by rw [hpre.block]; decide) hf
      rfl
  | pst lp c =>
    have h0 := at_of (d := ⟨.pst lp c, i, tt, sc, m, l⟩) h rfl
    cases lp <;> rcases fin4_cases c with rfl | rfl | rfl | rfl
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemStore_0)
      obtain ⟨⟨vals, rfl⟩, -⟩ := fires_tcSt (reg_tmem 1097 64 h0 (by table_decide) rfl)
        (tmem_lt hw8 64 (by decide)) hf
      exact ⟨vals, rfl⟩
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemStore_1)
      obtain ⟨⟨vals, rfl⟩, -⟩ := fires_tcSt (reg_tmem 1099 80 h0 (by table_decide) rfl)
        (tmem_lt hw8 80 (by decide)) hf
      exact ⟨vals, rfl⟩
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemStore_2)
      obtain ⟨⟨vals, rfl⟩, -⟩ := fires_tcSt (reg_tmem 1095 96 h0 (by table_decide) rfl)
        (tmem_lt hw8 96 (by decide)) hf
      exact ⟨vals, rfl⟩
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemStore_3)
      obtain ⟨⟨vals, rfl⟩, -⟩ := fires_tcSt (reg_tmem 1098 112 h0 (by table_decide) rfl)
        (tmem_lt hw8 112 (by decide)) hf
      exact ⟨vals, rfl⟩
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemStore_4)
      obtain ⟨⟨vals, rfl⟩, -⟩ := fires_tcSt (reg_tmem 2060 64 h0 (by table_decide) rfl)
        (tmem_lt hw8 64 (by decide)) hf
      exact ⟨vals, rfl⟩
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemStore_5)
      obtain ⟨⟨vals, rfl⟩, -⟩ := fires_tcSt (reg_tmem 2062 80 h0 (by table_decide) rfl)
        (tmem_lt hw8 80 (by decide)) hf
      exact ⟨vals, rfl⟩
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemStore_6)
      obtain ⟨⟨vals, rfl⟩, -⟩ := fires_tcSt (reg_tmem 2058 96 h0 (by table_decide) rfl)
        (tmem_lt hw8 96 (by decide)) hf
      exact ⟨vals, rfl⟩
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemStore_7)
      obtain ⟨⟨vals, rfl⟩, -⟩ := fires_tcSt (reg_tmem 2061 112 h0 (by table_decide) rfl)
        (tmem_lt hw8 112 (by decide)) hf
      exact ⟨vals, rfl⟩
  | pwait lp hh =>
    have hop : ins.op = .tcWaitSt := by
      cases lp <;> rcases fin2_cases hh with rfl | rfl
      · exact congrArg Instr.op (Option.some.inj (hc.symm.trans Flow.code_tmemWait_0))
      · exact congrArg Instr.op (Option.some.inj (hc.symm.trans Flow.code_tmemWait_1))
      · exact congrArg Instr.op (Option.some.inj (hc.symm.trans Flow.code_tmemWait_2))
      · exact congrArg Instr.op (Option.some.inj (hc.symm.trans Flow.code_tmemWait_3))
    rw [hop] at hf
    obtain ⟨-, rfl⟩ := fires_tcWaitSt hf
    rfl
  | pArr lp =>
    cases lp
    · exact ev_arriveLead hpre hg Flow.code_mbarArrive_10 (regv h4 405) (regv h4 1955)
        (by omega) (by omega) hc hf
    · exact ev_arriveLead hpre hg Flow.code_mbarArrive_12 (regv h4 405) (regv h4 2668)
        (by omega) (by omega) hc hf
  | p2Arr lp =>
    cases lp
    · exact ev_arriveLead hpre hg Flow.code_mbarArrive_11 (regv h4 406) (regv h4 1973)
        (by omega) (by omega) hc hf
    · exact ev_arriveLead hpre hg Flow.code_mbarArrive_13 (regv h4 406) (regv h4 2686)
        (by omega) (by omega) hc hf
  | warpBar lp =>
    have hop : ins.op = .warp ⟨.barWarp, none, [], [], some (.imm (-1))⟩ := by
      cases lp
      · exact congrArg Instr.op (Option.some.inj (hc.symm.trans Flow.code_warpBar_0))
      · exact congrArg Instr.op (Option.some.inj (hc.symm.trans Flow.code_warpBar_1))
    rw [hop, eventTmpl, warpTmpl_barWarp] at hf
    simp only [warpBarTmpl] at hf
    split at hf
    · simp [Fires] at hf
    · split_ifs at hf
      · obtain ⟨inst, rfl, -⟩ := hf
        exact ⟨_, inst, rfl⟩
      · simp [Fires] at hf
  | el lp =>
    cases lp
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_52)
      obtain ⟨mk, inst, ld, rfl, -⟩ := fires_elect hf
      exact ⟨mk, inst, ld, rfl⟩
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_elect_53)
      obtain ⟨mk, inst, ld, rfl, -⟩ := fires_elect hf
      exact ⟨mk, inst, ld, rfl⟩
  | barEnd =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_barArrive_3)
    obtain ⟨rfl, -⟩ := fires_barArrive_imm (id := 2) (n := 416) (by decide) (by decide)
      (by decide) (by decide) (by rw [hpre.block]; decide) hf
    rfl
  | exit =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_exit_0)
    simp [eventTmpl, Fires] at hf

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
