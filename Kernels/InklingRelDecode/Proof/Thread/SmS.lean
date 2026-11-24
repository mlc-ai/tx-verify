-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmGen
public import Lemmas.Flow.TcLdUb

@[expose] public section

/-! # The S-tile stage: the poll, the broadcast and the Tensor Memory load (pcs 1257-1298)

The thread polls the `s_ready` barrier of the stage (pc 1257: `mbarrier.try_wait` into `%complete`,
and a branch back while it is not complete, pc 1258), computes the Tensor Memory address of its
warp's lanes (pcs 1259-1264: the stage's base `%r482`, plus the warp index, which the broadcast of
pc 1261 delivers, shifted to bit 21 and masked: `%r45`, `%r1215`), loads the 64 words of its row of
the S tile (pc 1265) and packs them in pairs (`mov.b64 %rd, {%r, %r}`, pcs 1266-1297) before the
wait for the load (pc 1298).

This file gives the steps of the sites `waitS`, `shfl4` and `ldS`. Where a word the load returns
is not four bytes the pack that reads it throws and the thread is dead (`none`); otherwise the
words are the machine's `sv`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.deprecated false

variable {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event} {ins : Instr}

/-! ### Tools -/

/-- A branch `@!p` on the fact `p = pick`: taken when `p` is false. -/
theorem run_nbra {t : TState} {pc target p : Nat} {F : List (Nat × Value)} {uni : Bool}
    (hc : kernel.code[pc]? = some ⟨some (p, true), .bra target uni⟩) (pick : Bool)
    (h : At t pc F) (hp : t.regs p = some (.pred pick)) (hA : Assumption.SegFreePc asms pc) :
    ∃ u, run kernel asms L g 1 t = some u ∧ At u (if pick then pc + 1 else target) F := by
  cases pick with
  | true =>
    refine ⟨skip t, ?_, by simp [skip, h.1], rfl, rfl, h.2.2.2.1, h.2.2.2.2⟩
    simp [run, tauStep, out, h.1, h.2.2.2.1, hc, guardHolds, readReg, hp, bind, Except.bind,
      pure, Except.pure]
  | false =>
    refine ⟨{ t with pc := target }, ?_, rfl, h.2⟩
    simp [run, tauStep, out, h.1, h.2.2.2.1, hc, guardHolds, readReg, hp, bind, Except.bind,
      pure, Except.pure, hA.exec, execLocalRule_of_none (localRule_bra (L := L) (g := g)
        (t := t) (target := target) (uni := uni)), execLocal, Op.rule, execBranch, Op.isLocal]

/-! ### The poll -/

theorem live_1257_p : 2511 ∉ Flow.live 1257 := by decide +kernel
theorem live_1259 : ∀ r ∈ Flow.live 1259, r ∈ Flow.live 1257 := by decide +kernel

/-- `shl.b32 %r481, %r43, 7` and `add.s32 %r482, %r481, %r2`: the stage's Tensor Memory base
(pcs 1259 and 1260). -/
theorem seg_1259 (d : D) (hT : g % L.block < 128) :
    Seg kernel asms L g 2 1259 (factsAt L g 1259 d) 1261 (factsAt L g 1261 d) := by
  intro t h
  sm_seg h

/-- **The poll of `s_ready`** (pc 1257): a failed poll polls again; a successful one continues to
the broadcast of the warp index. -/
theorem step_waitS (hi : Inv L g d) (hs : d.site = .waitS) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  have hpc : d.site.pc = 1257 := by rw [hs]; rfl
  have hc' : kernel.code[1257]? = some ins := hpc ▸ hc
  obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_mbarWait_0)
  have h' : At t 1257 (factsAt L g 1257 d) := hpc ▸ h
  have hf' : Fires t.pc (eventTmpl asms L g t (.mbarWait 2511 874 0 (.reg 875) true .cta)) e
      (some u) := by rw [h'.1]; exact hpc ▸ hf
  obtain ⟨m, par, ok, sc, rfl, rfl⟩ := fires_wait hf'
  have h1 := At.set (r := 2511) (v := .pred ok) h' (facts_ne live_1257_p)
  have hlate : LateSite d.site := by rw [hs]; trivial
  cases ok with
  | false =>
    obtain ⟨w, hr, hw⟩ := run_nbra (L := L) (g := g) Flow.code_1258 false h1
      (holds_mem h1.2.2.2.2 (List.mem_cons_self ..)) (segFree (by decide +kernel))
    simp only [Bool.false_eq_true, ↓reduceIte] at hw
    exact .inl (.inr ⟨d, w, by simp [next, hs], run_rtg hr,
      ⟨by rw [hpc]; exact hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1,
        by show Holds w.regs (factsAt L g d.site.pc d); rw [hpc]; exact hw.2.2.2.2.2⟩, hi⟩)
  | true =>
    obtain ⟨w, hr, hw⟩ := run_nbra (L := L) (g := g) Flow.code_1258 true h1
      (holds_mem h1.2.2.2.2 (List.mem_cons_self ..)) (segFree (by decide +kernel))
    simp only [↓reduceIte] at hw
    have hw' : At w 1259 (factsAt L g 1259 d) :=
      hw.mono (holds_live hw.2.2.2.2.2 rfl live_1259)
    obtain ⟨t', hr', ht'⟩ := (seg_1259 d hi.tid).rtg hw'
    exact .inl (.inr ⟨{ d with site := .shfl4 }, t', by simp [next, hs], (run_rtg hr).trans hr',
      ht', inv_late hi hlate (s := .shfl4) trivial (fun h => absurd h (by simp))⟩)

/-! ### The broadcast of the warp index -/

/-- The 64 destination registers of the load. -/
def ldRegs : List Nat := (List.range 64).map (876 + ·)

theorem code_ldS : kernel.code[1265]? = some ⟨none, .tcLd ldRegs 1676 (.s16x32bx2 64) none⟩ := by
  rw [Flow.code_1265]
  rfl


theorem live_1261' : 944 ∉ Flow.live 1261 := by decide +kernel
theorem live_1262 : 945 ∉ Flow.live 1261 := by decide +kernel

/-- `shl.b32 %r484, %r483, 21` (pc 1262) of a received word that reads as `m`. -/
theorem seg_shl (d : D) {recv : Value} {m : Nat} (hw : Raw.word32Of recv = some m) :
    Seg kernel asms L g 1 1262 ((944, recv) :: factsAt L g 1261 d) 1263
      ((945, b32 (m * 2097152 % 2 ^ 32)) :: factsAt L g 1261 d) := by
  refine Raw.seg_int1 (d := 945) (v := b32 (m * 2097152 % 2 ^ 32)) Flow.code_1262 rfl rfl
    (segFree (by decide +kernel)) (fun t h => ?_) (fun R hR => ?_)
  · exact Raw.execInt_shl21 (holds_mem h.2.2.2.2 (List.mem_cons_self ..)) hw
  · exact ⟨Function.update_self .., holds_update hR.2 (facts_ne live_1262)⟩

/-- `and.b32 %r45, %r484, 0x600000` and `add.s32 %r1215, %r482, %r45` (pcs 1263, 1264): the
address of the load, with the lane bits `m % 4` recorded. -/
theorem seg_lane (d : D) (hT : g % L.block < 128) (m : Nat) :
    Seg kernel asms L g 2 1263 ((945, b32 (m * 2097152 % 2 ^ 32)) :: factsAt L g 1261 d) 1265
      (factsAt L g 1265 { d with site := .ldS, stg := { d.stg with bw := m % 4 } }) := by
  intro t h
  sm_seg h [r45, Raw.and_lane]

/-- The lane field of the address `b · 2 ^ 21 + c` with a column `c < 2 ^ 16` is accepted only for
the lane bits 0 and the warp index. -/
theorem addr_bad {c b o : Nat} (hT : g % L.block < 128) (hc : c < 2 ^ 16) (hb4 : b < 4)
    (hb : ¬ (b = 0 ∨ b = g % L.block / 32)) :
    tcDataAddressOk L g (.s16x32bx2 o) ((b * 2097152 + c) % 2 ^ 32) = false := by
  have he : (b * 2097152 + c) % 2 ^ 32 / 2 ^ 16 = 32 * b := by omega
  simp only [tcDataAddressOk, TcShape.splitOk, tmemLaneFieldOk, laneBase, TcShape.lanes, he,
    Bool.and_eq_false_iff, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  right
  omega

/-- **The broadcast of the warp index** (pc 1261) follows every received word: where it reads as
`m` and `m % 4` is 0 or the warp index, the address arithmetic follows with the lane bits recorded
and the load is next; a word without bits faults at the shift, and other lane bits give a load
whose lane field leaves the warp's lanes (undefined behaviour): the thread is dead. -/
theorem step_shfl4 (hi : Inv L g d) (hs : d.site = .shfl4) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  have hpc : d.site.pc = 1261 := by rw [hs]; rfl
  have hc' : kernel.code[1261]? = some ins := hpc ▸ hc
  obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_shfl_4)
  have h' : At t 1261 (factsAt L g 1261 d) := hpc ▸ h
  have hf' := hpc ▸ hf
  obtain ⟨av, bv, cv, recv, ok, rfl, rfl⟩ := fires_shfl (p := none) hf'
  have hlate : LateSite d.site := by rw [hs]; trivial
  have h1 : At (PTX.next (setReg t 944 recv)) 1262 ((944, recv) :: factsAt L g 1261 d) :=
    At.set (r := 944) (v := recv) h' (facts_ne live_1261')
  have hT := hi.tid
  cases hm : Raw.word32Of recv with
  | none =>
    refine .inr ⟨by simp [next, hs, Raw.laneOk, hm], ?_⟩
    refine Raw.dead_int1 Flow.code_1262 rfl rfl (segFree (by decide +kernel))
      (fun t' h' => ?_) h1
    exact Raw.execInt_shl21_none (holds_mem h'.2.2.2.2 (List.mem_cons_self ..)) hm
  | some m =>
    obtain ⟨t2, hr2, ht2⟩ := (seg_shl (L := L) (g := g) d hm).rtg h1
    obtain ⟨t3, hr3, ht3⟩ := (seg_lane (L := L) (g := g) d hT m).rtg ht2
    have hm4 : m % 4 < 4 := Nat.mod_lt _ (by decide)
    by_cases hl : m % 4 = 0 ∨ m % 4 = g % L.block / 32
    · refine .inl (.inr ⟨{ d with site := .ldS, stg := { d.stg with bw := m % 4 } }, t3,
        by simp [next, hs, Raw.laneOk, hm, hl], hr2.trans hr3, ht3, ?_⟩)
      have hi' := inv_late hi hlate (s := .ldS) trivial (fun h => absurd h (by simp))
      exact ⟨hi'.tid, hi'.ok, hi'.i, hi'.cwPre, hi'.cwNxt, hi'.loop, hi'.wb, hi'.vb, hi'.start,
        hi'.late, hi'.lead, fun hr => let R := hi.re hr; ⟨R.al, R.m, R.mn, R.pv, R.sw⟩,
        hi'.lb, by exact ⟨hi.four.al, hi.four.cm1, hi.four.cm2,
          hi.four.cm3, hi.four.cm4, hi.four.ld, hi.four.m2, hi.four.sw⟩, hl, hi.wf, hi.vf⟩
    · refine .inr ⟨by simp [next, hs, Raw.laneOk, hm, hl], ?_⟩
      have hc0 := hi.ok.col
      have hr : t3.regs 1676 = some (b32 ((m % 4 * 2097152 + (d.i % 2 * 128 + d.e.tm)) %
          2 ^ 32)) := by
        have := holds_mem ht3.2.2.2.2 (Flow.mem_factsFrom
          (val := valueOf L g { d with site := .ldS, stg := { d.stg with bw := m % 4 } })
          (show 1676 ∈ Flow.live 1265 by decide +kernel))
        rw [this]
        sm_vals
        simp only [r45]
        congr 2
        omega
      obtain ⟨t4, f, h4, hf4⟩ := tcLd_dead (K := kernel) (A := asms) (L := L) (g := g)
        (hc := by rw [ht3.1]; exact code_ldS) ht3.2.2.2.1 hr (Nat.mod_lt _ (by decide))
        (addr_bad hT (by omega) hm4 hl) (by hooks_off)
      exact ⟨t4, f, (hr2.trans hr3).trans h4, hf4⟩

/-! ### The load and the packs of its words -/

/-- The invariant does not mention the S-tile words. -/
theorem inv_sv (hi : Inv L g d) (f : Nat → { v : Value // v.bytes = 4 }) :
    Inv L g { d with sv := f } :=
  ⟨hi.tid, hi.ok, hi.i, hi.cwPre, hi.cwNxt, hi.loop, hi.wb, hi.vb, hi.start, hi.late, hi.lead,
    hi.re, hi.lb, hi.four, hi.bw, hi.wf, hi.vf⟩

/-- A register outside the S words and their pairs has the same value in two states that agree on
everything but the S words (and the site). -/
theorem valueOf_frameSv {d d' : D} (h1 : d'.e = d.e) (h2 : d'.i = d.i) (h3 : d'.m = d.m)
    (h4 : d'.l = d.l) (hw : d'.wd = d.wd) (hv : d'.vd = d.vd) (h6 : d'.pf = d.pf) {r : Nat}
    (hr1 : ¬ (876 ≤ r ∧ r < 876 + 64)) (hr2 : ¬ (2447 ≤ r ∧ r < 2447 + 32))
    (hx : d'.stg = d.stg := by rfl) : valueOf L g d' r = valueOf L g d r := by
  have eS : valuesS L g d' = valuesS L g d := by simp only [valuesS, h1, h3, h4, hx]
  have eP : valuesP L g d' = valuesP L g d := by simp only [valuesP, h1]
  have eQ : valuesQ L g d' = valuesQ L g d := by simp only [valuesQ, h1]
  have eR : valuesR L g d' = valuesR L g d := by simp only [valuesR, D.n, h1, h2]
  have eI : valuesI L g d' = valuesI L g d := by simp only [valuesI, D.n, h1, h2, hx]
  have eW : valuesW d' = valuesW d := by simp only [valuesW, hw, hv]
  have eX : (valuesX L g d').lookup r = (valuesX L g d).lookup r := by
    simp only [valuesX, valuesXt, lookup_append', List.lookup, lookup_range_map, hr1, hr2, hx,
      D.pwV, D.pwE, ↓reduceIte, Option.none_or]
  simp only [valueOf, values, lookup_append', eI, eS, eP, eQ, eR, eW, eX]

theorem packS_code : ∀ m < 32, packAt (1266 + m) (2447 + (31 - m)) (876 + 2 * (31 - m))
    (876 + (2 * (31 - m) + 1)) 64 = true := by decide +kernel
theorem emu_packS : ∀ m < 32, Assumptions.emuSites.contains (1266 + m) = false := by
  decide +kernel
theorem live_packS_src : ∀ m < 32, (876 + 2 * (31 - m)) ∈ Flow.live (1266 + m) ∧
    (876 + (2 * (31 - m) + 1)) ∈ Flow.live (1266 + m) := by decide +kernel
theorem live_packS_next : ∀ m < 32, ∀ r ∈ Flow.live (1266 + m + 1),
    r = 2447 + (31 - m) ∨ r ∈ Flow.live (1266 + m) := by decide +kernel

/-- `mov.b64 %rd(530 - m), {%r(478 - 2 m), %r(477 - 2 m)}`: the pack of two words of the S tile
(pc `1266 + m`). -/
theorem seg_sword (d : D) {m : Nat} (hm : m < 32) :
    Seg kernel asms L g 1 (1266 + m) (factsAt L g (1266 + m) d) (1266 + m + 1)
      (factsAt L g (1266 + m + 1) d) := by
  obtain ⟨la, lb⟩ := live_packS_src m hm
  exact seg_pack1 (packAt_spec (packS_code m hm)) (Or.inr rfl) (emu_packS m hm)
    (valueOf_sv d (by omega : 2 * (31 - m) < 64))
    (valueOf_sv d (by omega : 2 * (31 - m) + 1 < 64)) (d.sv _).2 (d.sv _).2 la lb
    (valueOf_svp d (by omega : 31 - m < 32)) (live_packS_next m hm)

/-- **The 32 packs of the S tile's words** (pcs 1266 to 1297). -/
theorem seg_swords (d : D) : ∀ m, m ≤ 32 →
    Seg kernel asms L g m 1266 (factsAt L g 1266 d) (1266 + m) (factsAt L g (1266 + m) d) := by
  intro m
  induction m with
  | zero => exact fun _ => Seg.refl _ _
  | succ m ih => exact fun hm => (ih (by omega)).comp (seg_sword d (m := m) (by omega))


theorem ldRegs_nodup : ldRegs.Nodup := by decide
theorem ldRegs_length : ldRegs.length = 64 := by decide


theorem live_ld_cov : ∀ r ∈ Flow.live 1266, r ∈ ldRegs ∨ (r ∉ ldRegs ∧ r ∈ Flow.live 1265) := by
  decide +kernel
theorem live_ld_off : ∀ r ∈ Flow.live 1265, r ∉ ldRegs ∧ ¬ (876 ≤ r ∧ r < 876 + 64) ∧
    ¬ (2447 ≤ r ∧ r < 2447 + 32) := by decide +kernel

theorem svOf_val (vals : List Value) (hb : ∀ x ∈ vals, x.bytes = 4) {p : Nat}
    (hp : p < vals.length) : (svOf vals hb p).1 = vals.getD p (b32 0) := by
  simp [svOf, hp, List.getD_eq_getElem?_getD]

/-- The facts after the load: the destinations hold the words, the other registers keep their
values. -/
theorem holds_ld (d : D) (vals : List Value) (hb : ∀ x ∈ vals, x.bytes = 4)
    (hlen : vals.length = 64) (t : TState) (hh : Holds t.regs (factsAt L g 1265 d)) :
    Holds (setRegs t ldRegs vals).regs
      (factsAt L g 1266 { d with site := .waitLd, sv := svOf vals hb }) := by
  have hw := holds_setRegs t ldRegs vals
    (valueOf L g { d with site := .waitLd, sv := svOf vals hb }) ldRegs_nodup
    (by rw [hlen, ldRegs_length]) (fun p hp => by
      have hp' : p < 64 := by simpa [ldRegs_length] using hp
      have : ldRegs.getD p 0 = 876 + p := by
        simp [ldRegs, List.getD_eq_getElem?_getD, hp']
      rw [this, valueOf_sv _ hp']
      exact svOf_val vals hb (by omega))
  refine Flow.holds_of_pointwise fun r hr => ?_
  rcases live_ld_cov r hr with hd | ⟨hd, hl⟩
  · exact holds_mem hw (Flow.mem_factsFrom hd)
  · obtain ⟨-, hr1, hr2⟩ := live_ld_off r hl
    rw [setRegs_other t ldRegs vals r hd,
      valueOf_frameSv (L := L) (g := g) (d := d)
        (d' := { d with site := .waitLd, sv := svOf vals hb }) rfl rfl rfl rfl rfl rfl rfl hr1 hr2]
    exact holds_mem hh (Flow.mem_factsFrom hl)

/-! ### A word that is not four bytes: the pack that reads it throws -/

/-- The 32 packs of the S words after the load: destination, low and high word (pc `1266 + m`). -/
def packS : List (Nat × Nat × Nat) :=
  (List.range 32).map fun m => (2447 + (31 - m), 876 + 2 * (31 - m), 876 + (2 * (31 - m) + 1))

theorem packS_codeB : packCodeB kernel 1266 packS = true := by decide +kernel
theorem packS_reads : ∀ p ∈ packS, p.2.1 ∈ Flow.live 1266 ∧ p.2.2 ∈ Flow.live 1266 := by
  decide +kernel
theorem packS_dis : ∀ p ∈ packS, ∀ q ∈ packS, q.1 ≠ p.2.1 ∧ q.1 ≠ p.2.2 := by decide +kernel
theorem packS_nd : (packS.map Prod.fst).Nodup := by decide +kernel
theorem packS_cov : ∀ r ∈ Flow.live (1266 + packS.length),
    r ∈ packS.map Prod.fst ∨ (r ∉ packS.map Prod.fst ∧ r ∈ Flow.live 1266) := by decide +kernel
theorem packS_length : packS.length = 32 := by decide

theorem packS_free : ∀ i < packS.length, Assumption.SegFreePc asms (1266 + i) := fun i hi =>
  segFree (emu_packS i (by rw [packS_length] at hi; exact hi))

/-- No assumption of the kernel has a local rule for the pack of two words. -/
theorem asms_noPack : NoPack asms := fun _ _ _ _ _ _ => asms_none (by simp) (by simp)

/-- The words a load returned, as explicit values of their registers. -/
def ldEx (vals : List Value) : List (Nat × Value) :=
  (List.range 64).map fun k => (876 + k, vals.getD k (b32 0))

theorem ldEx_val (base : Nat → Value) (vals : List Value) {p : Nat} (hp : p < 64) :
    valueEx base (ldEx vals) (876 + p) = vals.getD p (b32 0) := by
  rw [valueEx, ldEx, lookup_range_map, if_pos (by omega), Option.getD_some,
    Nat.add_sub_cancel_left]

theorem ldEx_off (base : Nat → Value) (vals : List Value) {r : Nat}
    (hr : ¬ (876 ≤ r ∧ r < 876 + 64)) : valueEx base (ldEx vals) r = base r := by
  simp only [valueEx, ldEx, lookup_range_map, hr, ↓reduceIte, Option.getD_none]

/-- The facts after the load, with the loaded words as explicit values over the table. -/
theorem holds_ldEx (d : D) (vals : List Value) (hlen : vals.length = 64) (t : TState)
    (hh : Holds t.regs (factsAt L g 1265 d)) :
    Holds (setRegs t ldRegs vals).regs
      (Flow.factsFrom (Flow.live 1266) (valueEx (valueOf L g d) (ldEx vals))) := by
  have hw := holds_setRegs t ldRegs vals (valueEx (valueOf L g d) (ldEx vals)) ldRegs_nodup
    (by rw [hlen, ldRegs_length]) (fun p hp => by
      have hp' : p < 64 := by simpa [ldRegs_length] using hp
      have : ldRegs.getD p 0 = 876 + p := by
        simp [ldRegs, List.getD_eq_getElem?_getD, hp']
      rw [this, ldEx_val _ _ hp'])
  refine Flow.holds_of_pointwise fun r hr => ?_
  rcases live_ld_cov r hr with hd | ⟨hd, hl⟩
  · exact holds_mem hw (Flow.mem_factsFrom hd)
  · obtain ⟨-, hr1, -⟩ := live_ld_off r hl
    rw [setRegs_other t ldRegs vals r hd, ldEx_off _ _ hr1]
    exact holds_mem hh (Flow.mem_factsFrom hl)

/-- Where the packs of the S words do not throw, every loaded word has four bytes. -/
theorem bytes_of_packsOk (base : Nat → Value) {vals : List Value} (hlen : vals.length = 64)
    (h : packsOk (valueEx base (ldEx vals)) packS = true) : ∀ x ∈ vals, x.bytes = 4 := by
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
  rw [hlen] at hk
  have hm : (2447 + (31 - (31 - k / 2)), 876 + 2 * (31 - (31 - k / 2)),
      876 + (2 * (31 - (31 - k / 2)) + 1)) ∈ packS :=
    List.mem_map.mpr ⟨31 - k / 2, List.mem_range.mpr (by omega), rfl⟩
  have hp := List.all_eq_true.mp h _ hm
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  have e1 : 31 - (31 - k / 2) = k / 2 := by omega
  rw [e1] at hp
  have hv : vals[k] = vals.getD k (b32 0) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  rcases Nat.mod_two_eq_zero_or_one k with h0 | h1
  · have e2 : 876 + 2 * (k / 2) = 876 + k := by omega
    rw [e2, ldEx_val _ _ hk] at hp
    rw [hv]
    exact hp.1
  · have e2 : 876 + (2 * (k / 2) + 1) = 876 + k := by omega
    rw [e2, ldEx_val _ _ hk] at hp
    rw [hv]
    exact hp.2

/-- **The Tensor Memory load of the S tile** (pc 1265): the event returns the 64 words; where a
word is not four bytes the thread is dead (the pack that reads it throws). -/
theorem step_ldS (hi : Inv L g d) (hs : d.site = .ldS) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  have hpc : d.site.pc = 1265 := by rw [hs]; rfl
  have hc' : kernel.code[1265]? = some ins := hpc ▸ hc
  obtain rfl := Option.some.inj (hc'.symm.trans code_ldS)
  obtain ⟨a, vals, hl, rfl, hu⟩ := fires_tcLd (L := L) (g := g) (A := asms)
    (by intro s hs; cases hs) hf (by hooks_off)
  have hlen : vals.length = 64 := by rw [hl, ldRegs_length]
  have hlate : LateSite d.site := by rw [hs]; trivial
  by_cases hb : ∀ x ∈ vals, x.bytes = 4
  · have h' : At t 1265 (factsAt L g 1265 d) := hpc ▸ h
    obtain ⟨hpc', hsub, hacc, hfl⟩ := setRegs_skel (PTX.next t) ldRegs vals
    have hAt : At u 1266 (factsAt L g 1266 { d with site := .waitLd, sv := svOf vals hb }) := by
      rw [hu]
      refine ⟨by rw [hpc']; simp [PTX.next, h'.1], by rw [hsub]; exact h'.2.1,
        by rw [hacc]; exact h'.2.2.1, by rw [hfl]; exact h'.2.2.2.1, ?_⟩
      rw [setRegs_next_regs]
      exact holds_ld d vals hb hlen t h'.2.2.2.2
    obtain ⟨t', hr, ht'⟩ := (seg_swords { d with site := .waitLd, sv := svOf vals hb } 32
      (le_refl 32)).rtg hAt
    exact .inl (.inr ⟨{ d with site := .waitLd, sv := svOf vals hb }, t',
      by simp only [next, hs]; rw [dif_pos ⟨hlen, hb⟩], hr, ht',
      inv_sv (inv_late hi hlate (s := .waitLd) trivial (fun h => absurd h (by simp))) _⟩)
  · refine .inr ⟨by simp only [next, hs]; rw [dif_neg (fun h' => hb h'.2)], ?_⟩
    have h' : At t 1265 (factsAt L g 1265 d) := hpc ▸ h
    obtain ⟨hpc', hsub, hacc, hfl⟩ := setRegs_skel (PTX.next t) ldRegs vals
    have hAt : At u 1266
        (Flow.factsFrom (Flow.live 1266) (valueEx (valueOf L g d) (ldEx vals))) := by
      rw [hu]
      refine ⟨by rw [hpc']; simp [PTX.next, h'.1], by rw [hsub]; exact h'.2.1,
        by rw [hacc]; exact h'.2.2.1, by rw [hfl]; exact h'.2.2.2.1, ?_⟩
      rw [setRegs_next_regs]
      exact holds_ldEx d vals hlen t h'.2.2.2.2
    have hD := SegD.packs (K := kernel) (A := asms) (L := L) (g := g)
      (base := valueOf L g d) (ex := ldEx vals) asms_noPack packS_codeB packS_reads packS_dis
      packS_nd packS_free packS_cov
    exact (hD u hAt).2 (fun hok => hb (bytes_of_packsOk _ hlen hok))

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
