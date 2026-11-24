-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionSound

@[expose] public section

/-! # The correction warps' events by site

The event a correction state fires (and continues after) is the event of its site (`Ev`),
read off its instruction and the site's register facts: the barriers name their ids and
counts, the arrivals their object in the thread's CTA or the leader CTA with no bytes and one
arrival, the polls their object and parity. The loads, stores, waits of the Tensor Memory and
the votes are the step lemmas' events. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {t u : TState} {e : Event}
  {ins : Instr}

theorem readBits_word {r x : Nat} (hr : t.regs r = some (b32 x)) (hx : x < 2 ^ 32) :
    readBits L g t 32 (.reg r) = .ok (BitVec.ofNat 64 x) := by
  rw [readBits_b32' hr, truncBits_ofNat hx (by decide)]

/-- `bar.sync r, 64` with `r` holding `id < 16`. -/
theorem ev_barReg {pc r id : Nat} (hpre : Pre P L mem0)
    (hc : kernel.code[pc]? = some ⟨none, .barSyncN (.reg r) (.imm 64) true⟩)
    (hr : t.regs r = some (b32 id)) (hid : id < 16) (hins : kernel.code[pc]? = some ins)
    (hf : Fires pc (eventTmpl asms L g t ins.op) e (some u)) :
    e = ⟨pc, .bar id (some 64) .sync⟩ := by
  obtain rfl := Option.some.inj (hins.symm.trans hc)
  have hf' : Fires pc (barTmpl L g t (.reg r) (some (.imm 64)) .sync) e (some u) := hf
  exact fires_barTmpl_at (n := 64) (readBits_word hr (by omega)) (by rfl) hid (by decide)
    (by decide) (by decide) (by rw [hpre.block]; decide) hf'

/-- An arrival of one on the leader CTA's barrier at `off`, through its `mapa` pointer. -/
theorem ev_arriveLead {pc r c off : Nat} (hpre : Pre P L mem0) (hg : g < L.threads)
    (hc : kernel.code[pc]? = some ⟨none, .mbarArrive r 0 (.imm 0) (.reg c) true true .cta none⟩)
    (hr : t.regs r = some (leadPtr L g off)) (hcnt : t.regs c = some (b32 1))
    (hoff : off < 1024) (h8 : off % 8 = 0) (hins : kernel.code[pc]? = some ins)
    (hf : Fires pc (eventTmpl asms L g t ins.op) e (some u)) :
    ∃ rel sc, e.kind = .arrive (leadLoc L g off) 0 1 rel sc := by
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
  obtain ⟨rel, sc, he⟩ := fires_arrive_at (L := L) (g := g) (A := asms) (cluster := true)
    (by simpa using hm) (rfl : readBits L g t 32 (.imm 0) = _) (readBits_word hcnt (by decide)) hf
  exact ⟨rel, sc, by rw [he.1]; rfl⟩

/-- An arrival of one on the thread's CTA's barrier at `off`, with a state destination. -/
theorem ev_arriveOwn {pc r c off : Nat} {st : Option Nat} (hpre : Pre P L mem0)
    (hc : kernel.code[pc]? = some ⟨none, .mbarArrive r 0 (.imm 0) (.reg c) false true .cta st⟩)
    (hr : t.regs r = some (b32 (sb L + off))) (hcnt : t.regs c = some (b32 1))
    (hoff : off < 1024) (h8 : off % 8 = 0) (hins : kernel.code[pc]? = some ins)
    (hf : Fires pc (eventTmpl asms L g t ins.op) e (some u)) :
    ∃ rel sc, e.kind = .arrive (ownLoc L g off) 0 1 rel sc := by
  obtain rfl := Option.some.inj (hins.symm.trans hc)
  have hbase := hpre.sharedRange
  have hal := hpre.sharedAlignment
  unfold sharedBytes at hbase
  have hm := mbarLoc_b32 (L := L) (g := g) hr (by simp only [sb]; omega)
    (by simp only [sb]; omega)
  obtain ⟨rel, sc, he⟩ := fires_arrive_state_at (L := L) (g := g) (A := asms) (cluster := false)
    (by simpa using hm) (rfl : readBits L g t 32 (.imm 0) = _) (readBits_word hcnt (by decide)) hf
  exact ⟨rel, sc, by rw [he]; rfl⟩

/-- A poll of the thread's CTA's barrier at `off` with the parity `x % 2` a register holds. -/
theorem ev_waitOwn {pc p r q off x : Nat} (hpre : Pre P L mem0)
    (hc : kernel.code[pc]? = some ⟨none, .mbarWait p r 0 (.reg q) true .cta⟩)
    (hr : t.regs r = some (b32 (sb L + off))) (hq : t.regs q = some (b32 (x % 2)))
    (hoff : off < 1024) (h8 : off % 8 = 0) (hins : kernel.code[pc]? = some ins)
    (hf : Fires pc (eventTmpl asms L g t ins.op) e (some u)) :
    ∃ ok acq sc, e.kind = .wait (ownLoc L g off) (x % 2) ok acq sc := by
  obtain rfl := Option.some.inj (hins.symm.trans hc)
  have hbase := hpre.sharedRange
  have hal := hpre.sharedAlignment
  unfold sharedBytes at hbase
  have hm := mbarLoc_b32 (L := L) (g := g) hr (by simp only [sb]; omega)
    (by simp only [sb]; omega)
  obtain ⟨ok, acq, sc, he, -⟩ := fires_wait_at (L := L) (g := g) (A := asms) hm
    (readBits_word hq (by omega)) hf
  refine ⟨ok, acq, sc, by rw [he]; simp only [BitVec.toNat_ofNat]; congr 1; omega⟩

theorem reg_val {d : D} (h : Holds t.regs (facts L g d)) {r : Nat}
    (hl : r ∈ Flow.live d.site.pc ++ d.site.extra) : t.regs r = some (valueOf L g d r) :=
  holds_mem h (mem_factsFrom hl)

/-- A register fact of the table, at a concrete site. -/
syntax "regv " term:max term:max : term
macro_rules
  | `(regv $h $r) => `((by
      have hh := reg_val (r := $r) $h (by table_decide)
      simp only [valueOf, values, chunkValues, loadValues, PTX.Flow.lookupLit, Option.getD_some,
        Nat.zero_add, Nat.reduceMod] at hh
      exact hh))

theorem kOf_lt (L : Launch) (g : Nat) : kOf L g < 4 := Nat.mod_lt _ (by decide)

set_option maxHeartbeats 8000000 in
/-- **The event a state fires and continues after is the event of its site.** -/
theorem site_event (hpre : Pre P L mem0) (hg : g < L.threads) {d : D} (hi : Inv L g d)
    (h : t.pc = d.site.pc ∧ t.sub = d.site.sub ∧ t.acc = [] ∧ t.fault = none ∧
      Holds t.regs (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Ev L g d e := by
  have hpc := fires_pc hf
  have h4 := h.2.2.2.2
  obtain ⟨s, i, tt, aw, a, o⟩ := d
  have hk := kOf_lt L g
  cases s with
  | rldW st j => exact (step_rldW hpre st j rfl hi h hc hf).1
  | fldW st j => exact (step_fldW hpre st j rfl hi h hc hf).1
  | fst st j hh el => exact (step_fst hpre st j hh el rfl hi h.1 h.2.1 h.2.2.1 h.2.2.2.1
      h.2.2.2.2 hc hf).1
  | rld st j => exact (step_rld st j rfl hi (at_of h rfl) hc hf).1
  | fld st j => exact (step_fld st j rfl hi (at_of h rfl) hc hf).1
  | rst st j => exact (step_rst hpre st j rfl hi (at_of h rfl) hc hf).1
  | barEnd => exact (step_barEnd hpre rfl hi (at_of h rfl) hc hf).1
  | exit => exact ev_exit rfl hc hf
  | ldA st =>
    fin_cases st
    · exact (step_ldA0 hpre rfl hi (at_of h rfl) hc hf).1
    · exact (step_ldA1 hpre rfl hi (at_of h rfl) hc hf).1
  | ldL st =>
    fin_cases st
    · exact (step_ldL0 hpre rfl hi (at_of h rfl) hc hf).1
    · exact (step_ldL1 hpre rfl hi (at_of h rfl) hc hf).1
  | vote st =>
    fin_cases st
    · obtain ⟨m, b, rfl⟩ := (step_vote0 hpre rfl hi (at_of h rfl) hc hf).1
      exact ⟨rfl, _, _, _, rfl⟩
    · obtain ⟨m, b, rfl⟩ := (step_vote1 hpre rfl hi (at_of h rfl) hc hf).1
      exact ⟨rfl, _, _, _, rfl⟩
  | setMaxReg =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_5)
    simp only [eventTmpl, SetMaxNReg.tmpl] at hf
    split_ifs at hf
    · obtain ⟨inst, rfl, -⟩ := hf
      exact ⟨rfl, inst, rfl⟩
    · simp [Fires] at hf
  | bar0 =>
    obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_3)
    obtain ⟨rfl, -⟩ := fires_barSync_imm (id := 2) (n := 416) (by decide) (by decide)
      (by decide) (by decide) (by rw [hpre.block]; decide) hf
    exact ⟨rfl, rfl⟩
  | tailWait => exact ⟨hpc, ev_waitOwn (x := i + 1) hpre Flow.code_mbarWait_40 (regv h4 3900)
      (regv h4 3939) (by decide) (by decide) hc hf⟩
  | free st =>
    obtain rfl : i = 0 := hi.start (.inr (.inr ⟨st, rfl⟩))
    fin_cases st
    · exact ⟨hpc, ev_arriveLead hpre hg Flow.code_mbarArrive_14 (regv h4 620) (regv h4 3939)
        (by decide) (by decide) hc hf⟩
    · exact ⟨hpc, ev_arriveLead hpre hg Flow.code_mbarArrive_15 (regv h4 621) (regv h4 3939)
        (by decide) (by decide) hc hf⟩
  | sync st gen =>
    fin_cases st <;> cases gen
    · exact ⟨hpc, by rw [ev_barReg hpre Flow.code_bar_4 (regv h4 622) (by omega) hc hf]; rfl⟩
    · exact ⟨hpc, by rw [ev_barReg hpre Flow.code_bar_6 (regv h4 622) (by omega) hc hf]; rfl⟩
    · exact ⟨hpc, by rw [ev_barReg hpre Flow.code_bar_8 (regv h4 622) (by omega) hc hf]; rfl⟩
    · exact ⟨hpc, by rw [ev_barReg hpre Flow.code_bar_5 (regv h4 623) (by omega) hc hf]; rfl⟩
    · exact ⟨hpc, by rw [ev_barReg hpre Flow.code_bar_7 (regv h4 623) (by omega) hc hf]; rfl⟩
    · exact ⟨hpc, by rw [ev_barReg hpre Flow.code_bar_9 (regv h4 623) (by omega) hc hf]; rfl⟩
  | credit c =>
    fin_cases c
    · exact ⟨hpc, ev_arriveOwn hpre Flow.code_mbarArrive_16 (regv h4 343) (regv h4 2733)
        (by decide) (by decide) hc hf⟩
    · exact ⟨hpc, ev_arriveOwn hpre Flow.code_mbarArrive_18 (regv h4 628) (regv h4 2991)
        (by decide) (by decide) hc hf⟩
    · exact ⟨hpc, ev_arriveOwn hpre Flow.code_mbarArrive_20 (regv h4 343) (regv h4 3249)
        (by decide) (by decide) hc hf⟩
    · exact ⟨hpc, ev_arriveOwn hpre Flow.code_mbarArrive_21 (regv h4 628) (regv h4 3253)
        (by decide) (by decide) hc hf⟩
    · exact ⟨hpc, ev_arriveOwn hpre Flow.code_mbarArrive_22 (regv h4 343) (regv h4 3253)
        (by decide) (by decide) hc hf⟩
    · exact ⟨hpc, ev_arriveOwn hpre Flow.code_mbarArrive_25 (regv h4 628) (regv h4 3253)
        (by decide) (by decide) hc hf⟩
  | oFree st fin =>
    fin_cases st <;> cases fin
    · exact ⟨hpc, ev_arriveLead hpre hg Flow.code_mbarArrive_17 (regv h4 620) (regv h4 2991)
        (by decide) (by decide) hc hf⟩
    · exact ⟨hpc, ev_arriveLead hpre hg Flow.code_mbarArrive_23 (regv h4 620) (regv h4 3253)
        (by decide) (by decide) hc hf⟩
    · exact ⟨hpc, ev_arriveLead hpre hg Flow.code_mbarArrive_19 (regv h4 621) (regv h4 3249)
        (by decide) (by decide) hc hf⟩
    · exact ⟨hpc, ev_arriveLead hpre hg Flow.code_mbarArrive_26 (regv h4 621) (regv h4 3253)
        (by decide) (by decide) hc hf⟩
  | oWait st =>
    fin_cases st
    · exact ⟨hpc, ev_waitOwn (x := i) hpre Flow.code_mbarWait_36 (regv h4 3250) (regv h4 3937)
        (by decide) (by decide) hc hf⟩
    · exact ⟨hpc, ev_waitOwn (x := i) hpre Flow.code_mbarWait_38 (regv h4 3252) (regv h4 3937)
        (by decide) (by decide) hc hf⟩
  | fWait st =>
    fin_cases st
    · exact ⟨hpc, ev_waitOwn (x := i + 1) hpre Flow.code_mbarWait_37 (regv h4 3251)
        (regv h4 3939) (by decide) (by decide) hc hf⟩
    · exact ⟨hpc, ev_waitOwn (x := i + 1) hpre Flow.code_mbarWait_39 (regv h4 3900)
        (regv h4 3939) (by decide) (by decide) hc hf⟩
  | staged st =>
    fin_cases st
    · exact ⟨hpc, ev_arriveOwn hpre Flow.code_mbarArrive_24 (regv h4 970) (regv h4 3253)
        (by decide) (by decide) hc hf⟩
    · exact ⟨hpc, ev_arriveOwn hpre Flow.code_mbarArrive_27 (regv h4 661) (regv h4 3253)
        (by decide) (by decide) hc hf⟩
  | rwait st =>
    fin_cases st
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemWait_4)
      exact ⟨hpc, by rw [(fires_tcWaitSt hf).2]⟩
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemWait_5)
      exact ⟨hpc, by rw [(fires_tcWaitSt hf).2]⟩
  | fence st =>
    fin_cases st
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceProxy_0)
      simp only [eventTmpl, Fires] at hf
      exact ⟨hpc, by rw [hf.1]; rfl⟩
    · obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceProxy_1)
      simp only [eventTmpl, Fires] at hf
      exact ⟨hpc, by rw [hf.1]; rfl⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
