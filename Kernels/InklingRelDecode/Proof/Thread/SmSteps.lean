-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmSkip

@[expose] public section

/-! # The steps of the softmax region's load stage

The steps (`Step`, see `SmLoads`) of the machine's sites from the second `barrier.sync 1` (`bar0`)
to the `s_ready` poll:

* `step_nxt`: a loop load, the zero fill of the next destination and the arrival at the next load
  (or after the last, the six local instructions to the poll);
* `step_pre_last`: the last preload, then the stretch of `SmStretch` (or its skip, where the
  next block's loads are masked) to the first loop load (or the poll);
* `step_bar0`: the barrier, the setup before the preloads, and for a masked lane the skip of all
  64 preloads.

`contSetup` is the part the last two share: from the state after the preloads (the preloaded
words in the registers), the continuation `afterSetup` of the machine. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedVariables false

variable {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event}

/-! ### A loop load -/

/-- The thread after a load wrote its destination `x`: the facts of the machine's next state. -/
theorem nxt_cont_mid (hi : Inv L g d) {j : Fin 64} (hs : d.site = .nxt j) (hj : j.val + 1 < 64)
    (h : At t d.site.pc (facts L g d)) {x : Value} {u1 : TState} (hpc : u1.pc = t.pc + 1)
    (hsub : u1.sub = 0) (hacc : u1.acc = []) (hfl : u1.fault = none)
    (hreg : ∀ r, r ≠ nxtDst j.val → u1.regs r = t.regs r) (hx : u1.regs (nxtDst j.val) = some x) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) u1 t' ∧
      At t' (Site.nxt ⟨j.val + 1, hj⟩).pc
        (facts L g
          { d with site := .nxt ⟨j.val + 1, hj⟩, cv := j.val + 1, v := setW d.v j.val x }) := by
  have hpc0 : d.site.pc = 1124 + 2 * j.val := by rw [hs]; rfl
  have hd1 := holds_afterNxt hi hs (R := u1.regs) (x := x) (fun r hr hne => by
    have := holds_mem h.2.2.2.2 (Flow.mem_factsFrom (val := valueOf L g d)
      (show r ∈ Flow.live d.site.pc by rw [hpc0]; exact hr))
    rw [hreg r hne]
    exact this) hx
  have hAt : At u1 (1125 + 2 * j.val) (factsAt L g (1125 + 2 * j.val) (d.afterNxt j.val x)) :=
    ⟨by rw [hpc, h.1, hpc0]; omega, hsub, hacc, hfl, hd1⟩
  have hseg := seg_fillN (L := L) (g := g) (d.afterNxt j.val x) (j := j.val) (by omega)
    (by simp [D.afterNxt, D.vd])
  obtain ⟨t', hr', ht'⟩ := hseg.rtg hAt
  refine ⟨t', hr', ?_⟩
  have hpc' : (Site.nxt ⟨j.val + 1, hj⟩).pc = 1124 + 2 * (j.val + 1) := rfl
  refine ⟨by simp only [hpc', ht'.1]; omega, ht'.2.1, ht'.2.2.1, ht'.2.2.2.1, ?_⟩
  refine Flow.holds_factsFrom_mono ht'.2.2.2.2 (fun r hr => ?_)
  exact live_afterN j.val (by omega) r hr

/-- After the last loop load wrote its destination `x`: the six local instructions to the
`s_ready` poll. -/
theorem nxt_cont_last (hi : Inv L g d) {j : Fin 64} (hs : d.site = .nxt j)
    (hj : ¬ j.val + 1 < 64)
    (h : At t d.site.pc (facts L g d)) {x : Value} {u1 : TState} (hpc : u1.pc = t.pc + 1)
    (hsub : u1.sub = 0) (hacc : u1.acc = []) (hfl : u1.fault = none)
    (hreg : ∀ r, r ≠ nxtDst j.val → u1.regs r = t.regs r) (hx : u1.regs (nxtDst j.val) = some x) :
    ∃ t', Relation.ReflTransGen (Tau kernel asms L g) u1 t' ∧
      At t' (Site.waitS).pc
        (facts L g { d with site := .waitS, cv := 64, v := setW d.v j.val x }) := by
  have hpc0 : d.site.pc = 1124 + 2 * j.val := by rw [hs]; rfl
  have hj63 : j.val = 63 := by omega
  have hd1 := holds_afterNxt hi hs (R := u1.regs) (x := x) (fun r hr hne => by
    have := holds_mem h.2.2.2.2 (Flow.mem_factsFrom (val := valueOf L g d)
      (show r ∈ Flow.live d.site.pc by rw [hpc0]; exact hr))
    rw [hreg r hne]
    exact this) hx
  rw [show 1125 + 2 * j.val = 1251 by omega] at hd1
  have hAt : At u1 1251 (factsAt L g 1251 (d.afterNxt j.val x)) :=
    ⟨by rw [hpc, h.1, hpc0]; omega, hsub, hacc, hfl, hd1⟩
  obtain ⟨t', hr', ht'⟩ := (seg_toWaitS (L := L) (g := g) (d.afterNxt j.val x) hi.tid hi.ok
    hi.i).rtg hAt
  have hv : valueOf L g { d with site := .waitS, cv := 64, v := setW d.v j.val x } =
      valueOf L g (d.afterNxt j.val x) :=
    funext (valueOf_congr (L := L) (g := g) (d := d.afterNxt j.val x)
      (d' := { d with site := .waitS, cv := 64, v := setW d.v j.val x }) rfl rfl rfl rfl rfl
      (by funext k; simp [D.vd, D.afterNxt, hj63]) rfl rfl rfl)
  have hf : facts L g { d with site := .waitS, cv := 64, v := setW d.v j.val x } =
      factsAt L g 1257 (d.afterNxt j.val x) := by
    show factsAt L g (Site.waitS).pc _ = _
    exact factsAt_congr hv 1257
  refine ⟨t', hr', ?_⟩
  rw [hf]
  exact ht'

/-- **A loop bias load**: the load's event writes the destination of index `j`; the zero fill of
the next destination follows and the thread arrives at the next load, or, for the last load, at
the `s_ready` poll. -/
theorem step_nxt (hi : Inv L g d) {j : Fin 64} (hs : d.site = .nxt j)
    (h : At t d.site.pc (facts L g d)) {ins : Instr} (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  have hpc : d.site.pc = 1124 + 2 * j.val := by rw [hs]; rfl
  obtain ⟨a, hca, hk, hnc, hext, hregs, -⟩ := loadAt_spec (loadAt_nxt j.val j.isLt)
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hca)
  obtain ⟨r, bs, rfl, rfl⟩ := fires_load hk hnc hf hext
  rw [hregs]
  cases hv : rebuild 3 bs with
  | error f =>
    exact .inr ⟨by simp [next, hs, hv], Machine.dead_of_fault (f := f)
      (by simp [afterLoad, hv])⟩
  | ok x =>
    rw [afterLoad_ok h.2.1 h.2.2.1 hv]
    by_cases hb : isBf16 x = true
    · have hxb := isBf16_bytes hb
      by_cases hj : j.val + 1 < 64
      · have hn : next L g d ⟨1124 + 2 * j.val, .rd r bs⟩ = some (some
            { d with
              site := .nxt ⟨j.val + 1, hj⟩
              cv := j.val + 1
              v := setW d.v j.val x }) := by
          simp [next, hs, hv, hb, hj]
        obtain ⟨t', hr', ht'⟩ := nxt_cont_mid hi hs hj h (x := x)
          (u1 := have __src := setReg t (nxtDst j.val) x
            { pc := t.pc + 1, regs := __src.regs, cf := __src.cf, fault := __src.fault : TState })
          rfl rfl rfl h.2.2.2.1 (fun r hr => by simp [setReg, Function.update_of_ne hr])
          (by simp [setReg])
        exact .inl (.inr ⟨_, t', hn, hr', ht', inv_afterNxt hi hs hj x hxb (bfOk_of_isBf16 hb)⟩)
      · have hn : next L g d ⟨1124 + 2 * j.val, .rd r bs⟩ = some (some
            { d with site := .waitS, cv := 64, v := setW d.v j.val x }) := by
          simp [next, hs, hv, hb, hj]
        obtain ⟨t', hr', ht'⟩ := nxt_cont_last hi hs hj h (x := x)
          (u1 := have __src := setReg t (nxtDst j.val) x
            { pc := t.pc + 1, regs := __src.regs, cf := __src.cf, fault := __src.fault : TState })
          rfl rfl rfl h.2.2.2.1 (fun r hr => by simp [setReg, Function.update_of_ne hr])
          (by simp [setReg])
        exact .inl (.inr ⟨_, t', hn, hr', ht', inv_afterNxtLast hi hs x hxb
          (bfOk_of_isBf16 hb)⟩)
    · exact .inl (.inl (by simp [next, hs, hv, hb]))

/-! ### The setup after the preloads -/

/-- The continuation of the machine after the setup that follows the first block's bias, from a
state of the thread at pc 807. -/
def ContSetup (L : Launch) (g : Nat) (d1 : D) (u : TState) : Prop :=
  afterSetup L g d1 = some none ∨ ∃ d' t', afterSetup L g d1 = some (some d') ∧
    Relation.ReflTransGen (Tau kernel asms L g) u t' ∧ At t' d'.site.pc (facts L g d') ∧
      Inv L g d'

/-- **The setup after the preloads** (pcs 807 to 1124, or to the poll where the next block's loads
are masked): the thread arrives where `afterSetup` puts the machine. -/
theorem contSetup (d1 : D) (hT : g % L.block < 128) (hok : d1.e.Ok) (hi : d1.i ≤ d1.e.r26)
    (hi0 : d1.i = 0) (hm : d1.m = b32 4286578688) (hl : d1.l = b32 0) (hcw : d1.cw = 64)
    (hcv : d1.cv = 0) (hwb : ∀ k, (d1.w k).bytes = 2) (hvb : ∀ k, (d1.v k).bytes = 2)
    (hal : d1.stg.re = true → RealSt d1.stg d1.m d1.pf)
    (hlb : d1.l.bytes = 4) (h4 : d1.stg.Four)
    (hbw : d1.stg.bw = 0 ∨ d1.stg.bw = g % L.block / 32)
    (hwf : ∀ k, BfOk (d1.w k)) (hvf : ∀ k, BfOk (d1.v k))
    (hAt : At u 807 (factsAt L g 807 d1)) : ContSetup L g d1 u := by
  by_cases h1 : d1.e.r26 = d1.i
  · exact .inl (by simp [afterSetup, h1])
  have hlt : d1.i < d1.e.r26 := by omega
  by_cases hb : actB d1.e (g % L.block) d1.i = true
  · obtain ⟨t', hr, ht'⟩ := (seg_first d1 hT hok hwb hi0 hm hl hlt hcv).rtg hAt
    refine .inr ⟨{ d1 with site := .nxt 0 }, t', by simp [afterSetup, h1, hb], hr, ht', ?_⟩
    refine ⟨hT, hok, hi, fun k hk => absurd hk (by simp), ?_, ⟨fun k hk => absurd hk (by simp),
      fun hk => absurd hk (by simp)⟩, hwb, hvb, fun h => absurd h (by simp),
      fun h => absurd h (by simp [LateSite]), fun h => absurd h (by simp), hal, hlb, h4, hbw,
      hwf, hvf⟩
    intro k hk
    have : (0 : Fin 64) = k := by injection hk
    subst this
    exact ⟨hcw, hcv, hb, hlt⟩
  · have hb' : actB d1.e (g % L.block) d1.i = false := by simpa using hb
    have h92 : valueOf L g d1 92 = .pred false := by rw [valueOf_p92, hb']
    obtain ⟨t1, hr1, ht1⟩ := (seg_setupB d1 hT hok hwb hi0 hm hl).rtg hAt
    obtain ⟨t2, hr2, ht2⟩ := (seg_loopTop d1 hT hok hlt hcv).rtg ht1
    obtain ⟨t3, hr3, ht3⟩ := (seg_skipNxt d1 hT hok hi h92 hcv).rtg ht2
    have hf : facts L g { d1 with site := .waitS, cv := 64, v := fun _ => z16 } =
        factsAt L g 1257 d1 := by
      show factsAt L g (Site.waitS).pc _ = _
      exact factsAt_congr (valueOf_skipNxt d1 hcv) 1257
    refine .inr ⟨{ d1 with site := .waitS, cv := 64, v := fun _ => z16 }, t3,
      by simp [afterSetup, h1, hb], hr1.trans (hr2.trans hr3), ?_, ?_⟩
    · show At t3 (Site.waitS).pc (facts L g _)
      rw [hf]
      exact ht3
    · exact ⟨hT, hok, hi, fun k hk => absurd hk (by simp), fun k hk => absurd hk (by simp),
        ⟨fun k hk => absurd hk (by simp), fun hk => absurd hk (by simp)⟩, hwb, fun k => rfl,
        fun h => absurd h (by simp), fun _ => ⟨hcw, rfl, hlt⟩, fun h => absurd h (by simp),
        hal, hlb, h4, hbw, hwf, fun _ => bfOk_z16⟩

/-! ### The last preload -/

/-- After the last preload wrote its destination `x`: the stretch to where `afterSetup` puts the
machine. -/
theorem pre_cont_last (hi : Inv L g d) {j : Fin 64} (hs : d.site = .pre j)
    (hj : ¬ j.val + 1 < 64)
    (h : At t d.site.pc (facts L g d)) {x : Value} (hxb : x.bytes = 2) (hxf : BfOk x)
    {u1 : TState}
    (hpc : u1.pc = t.pc + 1) (hsub : u1.sub = 0) (hacc : u1.acc = []) (hfl : u1.fault = none)
    (hreg : ∀ r, r ≠ 263 + j.val → u1.regs r = t.regs r) (hx : u1.regs (263 + j.val) = some x) :
    ContSetup L g { d with cw := 64, w := setW d.w j.val x } u1 := by
  have hpc0 : d.site.pc = 680 + 2 * j.val := by rw [hs]; rfl
  have hj63 : j.val = 63 := by omega
  obtain ⟨hcw, hact⟩ := hi.cwPre j hs
  obtain ⟨hi0, hcv, hm, hl⟩ := hi.loop.1 j hs
  have hd1 := holds_afterLoad (R := u1.regs) hi hs (x := x) (fun r hr hne => by
    have := holds_mem h.2.2.2.2 (Flow.mem_factsFrom (val := valueOf L g d)
      (show r ∈ Flow.live d.site.pc by rw [hpc0]; exact hr))
    rw [hreg r hne]
    exact this) hx
  rw [show 681 + 2 * j.val = 807 by omega] at hd1
  have hv : valueOf L g { d with cw := 64, w := setW d.w j.val x } =
      valueOf L g (d.afterPre j.val x) :=
    funext (valueOf_congr (L := L) (g := g) (d := d.afterPre j.val x)
      (d' := { d with cw := 64, w := setW d.w j.val x }) rfl rfl rfl rfl
      (by funext k; simp [D.wd, D.afterPre, hj63]) rfl rfl rfl rfl)
  have hAt : At u1 807 (factsAt L g 807 { d with cw := 64, w := setW d.w j.val x }) := by
    rw [factsAt_congr hv]
    exact ⟨by rw [hpc, h.1, hpc0]; omega, hsub, hacc, hfl, hd1⟩
  have hwb : ∀ k, (setW d.w j.val x k).bytes = 2 := by
    intro k
    by_cases hk : k = j.val
    · subst hk; simpa [setW] using hxb
    · simpa [setW, Function.update_of_ne hk] using hi.wb k
  exact contSetup (L := L) (g := g) { d with cw := 64, w := setW d.w j.val x } hi.tid
    hi.ok hi.i hi0 hm hl rfl hcv hwb hi.vb hi.re hi.lb hi.four hi.bw (bfOk_setW hi.wf hxf) hi.vf
    hAt

/-- **The last preload** (`j = 63`): the load's event writes the last word; the stretch to the first
loop load follows (`contSetup`). -/
theorem step_pre_last (hi : Inv L g d) {j : Fin 64} (hs : d.site = .pre j)
    (hj : ¬ j.val + 1 < 64)
    (h : At t d.site.pc (facts L g d)) {ins : Instr} (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  have hpc : d.site.pc = 680 + 2 * j.val := by rw [hs]; rfl
  obtain ⟨a, hca, hk, hnc, hext, hregs, -⟩ := loadAt_spec (loadAt_pre j.val j.isLt)
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans hca)
  obtain ⟨r, bs, rfl, rfl⟩ := fires_load hk hnc hf hext
  rw [hregs]
  cases hv : rebuild 3 bs with
  | error f =>
    exact .inr ⟨by simp [next, hs, hv], Machine.dead_of_fault (f := f)
      (by simp [afterLoad, hv])⟩
  | ok x =>
    rw [afterLoad_ok h.2.1 h.2.2.1 hv]
    by_cases hb : isBf16 x = true
    · have hn : next L g d ⟨680 + 2 * j.val, .rd r bs⟩ =
          afterSetup L g { d with cw := 64, w := setW d.w j.val x } := by
        simp [next, hs, hv, hb, hj]
      have hc := pre_cont_last hi hs hj h (isBf16_bytes hb) (bfOk_of_isBf16 hb)
        (u1 := have __src := setReg t (263 + j.val) x
          { pc := t.pc + 1, regs := __src.regs, cf := __src.cf, fault := __src.fault : TState })
        rfl rfl rfl h.2.2.2.1 (fun r hr => by simp [setReg, Function.update_of_ne hr])
        (by simp [setReg])
      rcases hc with hc | ⟨d', t', hd, hr, ha, hinv⟩
      · exact .inl (.inl (hn.trans hc))
      · exact .inl (.inr ⟨d', t', hn.trans hd, hr, ha, hinv⟩)
    · exact .inl (.inl (by simp [next, hs, hv, hb]))

/-! ### The barrier before the preloads -/

/-- **The barrier before the preloads** (`bar0`, pc 575): the setup of pcs 576 to 679 and the first
preload; for a masked lane the skip of the preloads and the continuation of `contSetup`. -/
theorem step_bar0 (hi : Inv L g d) (hs : d.site = .bar0)
    (h : At t d.site.pc (facts L g d)) {ins : Instr} (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  have hpc : d.site.pc = 575 := by rw [hs]; rfl
  rw [hpc] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_19)
  obtain rfl := fires_async_next (show AsyncAdvancesOp (.barSync (.imm 1) false) from trivial) hf
  obtain ⟨hi0, hm, hl, hcw, hcv⟩ := hi.loop.2 hs
  have h1 : At (PTX.next t) 576 (factsAt L g 576 d) := by
    have hh : Holds t.regs (factsAt L g 575 d) := hpc ▸ h.2.2.2.2
    refine ⟨by simp [PTX.next, h.1, hpc], h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
    exact Flow.holds_factsFrom_mono hh (by decide +kernel)
  obtain ⟨t', hr', ht'⟩ := (seg_setupA d hi.tid hi.ok hcw).rtg h1
  by_cases ha : act0 d.e (g % L.block) = true
  · have hn : next L g d e = some (some { d with site := .pre 0 }) := by
      simp [next, hs, ha]
    refine .inl (.inr ⟨_, t', hn, hr', ?_, ?_⟩)
    · exact ht'
    · refine ⟨hi.tid, hi.ok, hi.i, ?_, fun k hk => absurd hk (by simp), ?_, hi.wb, hi.vb,
        fun h => absurd h (by simp), fun h => absurd h (by simp [LateSite]),
        fun h => absurd h (by simp), hi.re, hi.lb, hi.four, hi.bw, hi.wf, hi.vf⟩
      · intro k hk
        have : (0 : Fin 64) = k := by injection hk
        subst this
        exact ⟨hcw, ha⟩
      · exact ⟨fun k hk => ⟨hi0, hcv, hm, hl⟩, fun hk => absurd hk (by simp)⟩
  · have ha' : act0 d.e (g % L.block) = false := by simpa using ha
    have h85 : valueOf L g d 85 = .pred false := by rw [valueOf_p85, ha']
    obtain ⟨t2, hr2, ht2⟩ := (seg_skipPre d h85 hcw).rtg ht'
    have hn : next L g d e =
        afterSetup L g { d with cw := 64, w := fun _ => z16 } := by
      simp [next, hs, ha']
    have hAt : At t2 807 (factsAt L g 807 { d with cw := 64, w := fun _ => z16 }) := by
      rw [factsAt_congr (valueOf_skipPre d hcw)]
      exact ht2
    have hc := contSetup (L := L) (g := g) { d with cw := 64, w := fun _ => z16 } hi.tid hi.ok
      hi.i hi0 hm hl rfl hcv (fun k => rfl) hi.vb hi.re hi.lb hi.four hi.bw (fun _ => bfOk_z16)
      hi.vf hAt
    rcases hc with hc | ⟨d', t3, hd, hr, hf', hinv⟩
    · exact .inl (.inl (hn.trans hc))
    · exact .inl (.inr ⟨d', t3, hn.trans hd, (hr'.trans hr2).trans hr, hf', hinv⟩)

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
