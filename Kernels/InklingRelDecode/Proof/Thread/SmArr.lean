-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.SmGen

@[expose] public section

/-! # After the arrival on `p_ready`: the second round to the loop's bias loads (pcs 1014-1124)

After the P store of iteration `i` (the arrival at pc 1013, or its skip for the threads whose
guard is false) the code packs the bias words of the next block (`v`, the loop loads' half-words
`%rs151 …`) into `%r1455 …` (32 `mov.b32`, pcs 1014-1045), moves the next iteration's variables
into the loop's (`%r1452 = %r41`, `%r1451 = %r42`, `%rd498 = %rd45`, pcs 1046-1048) and tests the
loop (pc 1049). From there the code is the code of the first round, after its setup
(`SmStretch`): the loop test, the mask and the pointers of the next block, the bias loads.

The state of the second round is `d.toTop`: the iteration `i + 1`, the words `v` as the current
words, no word of the next block loaded. Between the packs, the registers hold the loaded
words in the `%rs` registers and the packed words in the `%r` registers: the state `d.mid`, in which
`w = v`, has both. The segment from pc 1014 starts from the facts of `d` (the packed words are
dead there) and its end is the facts of `d.toTop`. `afterArrive` is `afterSetup` of `d.toTop`, and
`contArrive` composes this segment with the first round's continuation `contTop`. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Sm
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option linter.unusedVariables false

variable {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event}

/-- The state between the packs and after them: the next block's words are the current words. -/
def D.mid (d : D) : D := { d with w := d.v, cw := 64 }

/-- The state of the second round's loop test: the next iteration, the words of the next block as
the current words, no word of the following block loaded. -/
def D.top (d : D) : D := { d with i := d.i + 1, w := d.v, cw := 64, cv := 0 }

/-! ### The packs of the next block's words -/

/-- The words of `v` are half-words as the table gives them. -/
theorem vd_bytes {d : D} (hvb : ∀ k, (d.v k).bytes = 2) (k : Nat) : (d.vd k).bytes = 2 := by
  unfold D.vd
  split
  · exact hvb k
  · rfl

theorem packV_code : ∀ m < 32, packAt (1014 + m) (1947 - m) (nxtDst (2 * (31 - m)))
    (nxtDst (2 * (31 - m) + 1)) 32 = true := by decide +kernel
theorem emu_packV : ∀ m < 32, Assumptions.emuSites.contains (1014 + m) = false := by
  decide +kernel
theorem live_packV_src : ∀ m < 32, nxtDst (2 * (31 - m)) ∈ Flow.live (1014 + m) ∧
    nxtDst (2 * (31 - m) + 1) ∈ Flow.live (1014 + m) := by decide +kernel
theorem live_packV_next : ∀ m < 32, ∀ r ∈ Flow.live (1014 + m + 1),
    r = 1947 - m ∨ r ∈ Flow.live (1014 + m) := by decide +kernel

/-- `mov.b32 %r(1486 - m), {…}`, the pack of two of the next block's words (pc `1014 + m`), in a
state whose current words are the next block's. -/
theorem seg_vword (d : D) (hwv : ∀ k, k < 64 → d.wd k = d.vd k) (hvb : ∀ k, (d.v k).bytes = 2)
    {m : Nat} (hm : m < 32) :
    Seg kernel asms L g 1 (1014 + m) (factsAt L g (1014 + m) d) (1014 + m + 1)
      (factsAt L g (1014 + m + 1) d) := by
  obtain ⟨la, lb⟩ := live_packV_src m hm
  have hq : 1947 - m = 1916 + (31 - m) := by omega
  refine seg_pack1 (packAt_spec (packV_code m hm)) (Or.inl rfl) (emu_packV m hm)
    (valueOf_nxt d (by omega : 2 * (31 - m) < 64))
    (valueOf_nxt d (by omega : 2 * (31 - m) + 1 < 64))
    (vd_bytes hvb _) (vd_bytes hvb _) la lb ?_ (live_packV_next m hm)
  rw [hq, valueOf_packed d (by omega : 31 - m < 32), hwv _ (by omega), hwv _ (by omega)]

/-- **The 32 packs of the next block's words** (pcs 1014 to 1045). -/
theorem seg_vwords (d : D) (hwv : ∀ k, k < 64 → d.wd k = d.vd k)
    (hvb : ∀ k, (d.v k).bytes = 2) : ∀ m, m ≤ 32 →
    Seg kernel asms L g m 1014 (factsAt L g 1014 d) (1014 + m) (factsAt L g (1014 + m) d) := by
  intro m
  induction m with
  | zero => exact fun _ => Seg.refl _ _
  | succ m ih => exact fun hm => (ih (by omega)).comp (seg_vword d hwv hvb (m := m) (by omega))

/-! ### The table at the second round's states -/

theorem lookup_valuesWf_offW (wd wd' vd : Nat → Value) {r : Nat}
    (h1 : ¬ (263 ≤ r ∧ r < 263 + 64)) (h2 : ¬ (1916 ≤ r ∧ r < 1916 + 32)) :
    (valuesWf wd' vd).lookup r = (valuesWf wd vd).lookup r := by
  simp only [valuesWf, lookup_append', List.lookup, lookup_range_map, h1, h2, ↓reduceIte]

/-- Two states that agree on everything but the current words give a register outside the words
and their packs the same value. -/
theorem valueOf_frameWd {d d' : D} (h1 : d'.e = d.e) (h2 : d'.i = d.i) (h3 : d'.m = d.m)
    (h4 : d'.l = d.l) (hv : d'.vd = d.vd) (h5 : d'.sv = d.sv) (h6 : d'.pf = d.pf) {r : Nat}
    (hr1 : ¬ (263 ≤ r ∧ r < 263 + 64)) (hr2 : ¬ (1916 ≤ r ∧ r < 1916 + 32))
    (hx : d'.stg = d.stg := by rfl) : valueOf L g d' r = valueOf L g d r := by
  have eS : valuesS L g d' = valuesS L g d := by simp only [valuesS, h1, h3, h4, hx]
  have eP : valuesP L g d' = valuesP L g d := by simp only [valuesP, h1]
  have eQ : valuesQ L g d' = valuesQ L g d := by simp only [valuesQ, h1]
  have eR : valuesR L g d' = valuesR L g d := by simp only [valuesR, D.n, h1, h2]
  have eX : valuesX L g d' = valuesX L g d := by
    simp only [valuesX, valuesXt, D.pwV, D.pwE, h5, hx]
  have eI : valuesI L g d' = valuesI L g d := by simp only [valuesI, D.n, h1, h2, hx]
  have eW : (valuesW d').lookup r = (valuesW d).lookup r := by
    simp only [valuesW, hv]
    exact lookup_valuesWf_offW _ _ _ hr1 hr2
  simp only [valueOf, values, lookup_append', eI, eS, eP, eQ, eR, eW, eX]

theorem live1014_off : ∀ r ∈ Flow.live 1014,
    ¬ (263 ≤ r ∧ r < 263 + 64) ∧ ¬ (1916 ≤ r ∧ r < 1916 + 32) := by decide +kernel

theorem holds_mid {R : Nat → Option Value} (d : D) (h : Holds R (factsAt L g 1014 d)) :
    Holds R (factsAt L g 1014 d.mid) := by
  refine Flow.holds_of_pointwise fun r hr => ?_
  obtain ⟨h1, h2⟩ := live1014_off r hr
  rw [valueOf_frameWd (L := L) (g := g) (d := d) (d' := d.mid) rfl rfl rfl rfl rfl rfl rfl h1 h2]
  exact holds_mem h (Flow.mem_factsFrom hr)

/-! ### The loop variables (pcs 1046-1048) -/

/-- `mov.b<w> d, a` of a register that holds a value of `w` bits. -/
theorem exec_movReg {t : TState} {w dst a : Nat} {x : Value}
    (hS : Assumption.SegFreePc asms t.pc) (hw : w = 32 ∨ w = 64) (ha : t.regs a = some x)
    (hx : x.bytes = w / 8) :
    execLocalA asms L g t (.move ⟨.scalar, .int .b w, [some dst], [.reg a]⟩) =
      .ok (PTX.next (setReg t dst x)) := by
  rw [hS.exec rfl, execLocalRule_of_none (asms_none (by simp) (by simp))]
  rcases hw with rfl | rfl <;>
  simp [execLocal, Op.rule, MoveInstr.rule, execMove, DType.width, readValue, readReg, ha, hx,
    bind, Except.bind, pure, Except.pure]

/-- A register move as a piece: the destination's fact is the source's. -/
theorem seg_mov {pc w dst a : Nat} {F : List (Nat × Value)} {x : Value}
    (hc : kernel.code[pc]? = some ⟨none, .move ⟨.scalar, .int .b w, [some dst], [.reg a]⟩⟩)
    (hw : w = 32 ∨ w = 64) (hno : Assumptions.emuSites.contains pc = false)
    (hx : (a, x) ∈ F) (hxb : x.bytes = w / 8) (hd : ∀ p ∈ F, p.1 ≠ dst) :
    Seg kernel asms L g 1 pc F (pc + 1) ((dst, x) :: F) := by
  intro t h
  have ha := holds_mem h.2.2.2.2 hx
  have hS : Assumption.SegFreePc asms t.pc := by rw [h.1]; exact segFree hno
  exact ⟨_, run_local hc rfl h (exec_movReg (L := L) (g := g) hS hw ha hxb), At.set h hd⟩

theorem live_1049_cov : ∀ r ∈ Flow.live 1049, r = 1913 ∨ r = 1912 ∨ r = 2446 ∨
    (r ∈ Flow.live 1046 ∧ ¬ IKey r ∧ ¬ RKey r ∧ ¬ (332 ≤ r ∧ r < 397)) := by decide +kernel

/-- **The loop variables**: `%r1452 = %r41`, `%r1451 = %r42`, `%rd498 = %rd45`: the facts of the
loop test of the next iteration. -/
theorem seg_1046 (d : D) (hok : d.e.Ok) (hlt : d.i < d.e.r26) :
    Seg kernel asms L g 3 1046 (factsAt L g 1046 d.mid) 1049 (factsAt L g 1049 d.top) := by
  have h1 := hok.split
  have h2 := hok.splits
  have h3 := hok.blk
  have h4 := Nat.mul_le_mul_right d.e.splits (show d.i + 1 ≤ d.e.r26 from hlt)
  have h5 : (d.i + 1) * d.e.splits = d.i * d.e.splits + d.e.splits := by ring
  have m503 := Flow.mem_factsFrom (val := valueOf L g d.mid)
    (show 502 ∈ Flow.live 1046 by decide +kernel)
  have m504 := Flow.mem_factsFrom (val := valueOf L g d.mid)
    (show 503 ∈ Flow.live 1046 by decide +kernel)
  have m1994 := Flow.mem_factsFrom (val := valueOf L g d.mid)
    (show 1993 ∈ Flow.live 1046 by decide +kernel)
  have v503 : valueOf L g d.mid 502 = b32 ((d.n + d.e.splits) % 2 ^ 32) := by
    sm_vals
    rfl
  have v504 : valueOf L g d.mid 503 = b32 ((d.e.splits * 128 + d.n * 128) % 2 ^ 32) := by
    sm_vals
    rfl
  have v1994 : valueOf L g d.mid 1993 = b64 (d.i + 1) := by
    sm_vals
    rfl
  have p1 := seg_mov (L := L) (g := g) (pc := 1046) (w := 32) (dst := 1913) (a := 502)
    Flow.code_1046 (Or.inl rfl) (by decide +kernel) m503 (by rw [v503]; rfl)
    (facts_ne (by decide +kernel))
  have p2 := seg_mov (L := L) (g := g) (pc := 1047) (w := 32) (dst := 1912) (a := 503)
    (F := (1913, valueOf L g d.mid 502) :: factsAt L g 1046 d.mid) Flow.code_1047
    (Or.inl rfl) (by decide +kernel) (List.mem_cons_of_mem _ m504)
    (by rw [v504]; rfl) (fun p hp => by
      rcases List.mem_cons.mp hp with rfl | hp
      · simp
      · exact facts_ne (by decide +kernel) p hp)
  have p3 := seg_mov (L := L) (g := g) (pc := 1048) (w := 64) (dst := 2446) (a := 1993)
    (F := (1912, valueOf L g d.mid 503) :: (1913, valueOf L g d.mid 502) ::
      factsAt L g 1046 d.mid) Flow.code_1048 (Or.inr rfl) (by decide +kernel)
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ m1994)) (by rw [v1994]; rfl)
    (fun p hp => by
      rcases List.mem_cons.mp hp with rfl | hp
      · simp
      · rcases List.mem_cons.mp hp with rfl | hp
        · simp
        · exact facts_ne (by decide +kernel) p hp)
  refine Seg.of_len (((p1.comp p2).comp p3).weaken_end fun R hR => ?_) rfl
  refine Flow.holds_of_pointwise fun r hr => ?_
  rcases live_1049_cov r hr with rfl | rfl | rfl | ⟨hl, hI, hRk, hv⟩
  · rw [holds_mem hR (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))),
      v503]
    sm_vals
    simp only [D.top, D.n, blkOf]
    congr 2
    omega
  · rw [holds_mem hR (List.mem_cons_of_mem _ (List.mem_cons_self ..)), v504]
    sm_vals
    simp only [D.top, D.n, key, blkOf]
    congr 2
    omega
  · rw [holds_mem hR (List.mem_cons_self ..), v1994]
    sm_vals
    rfl
  · rw [holds_mem hR (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (Flow.mem_factsFrom hl))))]
    rw [valueOf_frameI (L := L) (g := g) (d := d.mid) (d' := d.top) rfl rfl rfl rfl rfl rfl hI
      hRk hv]

/-- **The packs and the loop variables** (pcs 1014 to 1048): from the facts after the arrival to
the facts of the loop test of the second round. -/
theorem seg_top (d : D) (hok : d.e.Ok) (hlt : d.i < d.e.r26) (hcw : d.cw = 64)
    (hcv : d.cv = 64) (hvb : ∀ k, (d.v k).bytes = 2) :
    Seg kernel asms L g 35 1014 (factsAt L g 1014 d) 1049 (factsAt L g 1049 d.top) := by
  have hwv : ∀ k, k < 64 → d.mid.wd k = d.mid.vd k := fun k hk => by
    simp [D.mid, D.wd, D.vd, hcv, hk]
  have hvb' : ∀ k, (d.mid.v k).bytes = 2 := hvb
  have h1 := seg_vwords (L := L) (g := g) d.mid hwv hvb' 32 (le_refl 32)
  have h2 := (h1.weaken_start (fun R h => holds_mid d h)).comp (seg_1046 d hok hlt)
  exact Seg.of_len h2 rfl

/-! ### The loop test and the next block's loads -/

/-- **From the loop test**: the loop test of a state with no word of the next block loaded, as
after the first round's setup (`contSetup`), without the setup. -/
theorem contTop (d1 : D) (hT : g % L.block < 128) (hok : d1.e.Ok) (hi : d1.i ≤ d1.e.r26)
    (hcw : d1.cw = 64) (hcv : d1.cv = 0) (hwb : ∀ k, (d1.w k).bytes = 2)
    (hvb : ∀ k, (d1.v k).bytes = 2)
    (hal : d1.stg.re = true → RealSt d1.stg d1.m d1.pf)
    (hlb : d1.l.bytes = 4) (h4 : d1.stg.Four)
    (hbw : d1.stg.bw = 0 ∨ d1.stg.bw = g % L.block / 32)
    (hwf : ∀ k, BfOk (d1.w k)) (hvf : ∀ k, BfOk (d1.v k))
    (hAt : At u 1049 (factsAt L g 1049 d1)) : ContSetup L g d1 u := by
  by_cases h1 : d1.e.r26 = d1.i
  · exact .inl (by simp [afterSetup, h1])
  have hlt : d1.i < d1.e.r26 := by omega
  by_cases hb : actB d1.e (g % L.block) d1.i = true
  · obtain ⟨t', hr, ht'⟩ := (seg_loopTop d1 hT hok hlt hcv).rtg hAt
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
    obtain ⟨t2, hr2, ht2⟩ := (seg_loopTop d1 hT hok hlt hcv).rtg hAt
    obtain ⟨t3, hr3, ht3⟩ := (seg_skipNxt d1 hT hok hi h92 hcv).rtg ht2
    have hf : facts L g { d1 with site := .waitS, cv := 64, v := fun _ => z16 } =
        factsAt L g 1257 d1 := by
      show factsAt L g (Site.waitS).pc _ = _
      exact factsAt_congr (valueOf_skipNxt d1 hcv) 1257
    refine .inr ⟨{ d1 with site := .waitS, cv := 64, v := fun _ => z16 }, t3,
      by simp [afterSetup, h1, hb], hr2.trans hr3, ?_, ?_⟩
    · show At t3 (Site.waitS).pc (facts L g _)
      rw [hf]
      exact ht3
    · exact ⟨hT, hok, hi, fun k hk => absurd hk (by simp), fun k hk => absurd hk (by simp),
        ⟨fun k hk => absurd hk (by simp), fun hk => absurd hk (by simp)⟩, hwb, fun k => rfl,
        fun h => absurd h (by simp), fun _ => ⟨hcw, rfl, hlt⟩, fun h => absurd h (by simp),
        hal, hlb, h4, hbw, hwf, fun _ => bfOk_z16⟩

/-- **After the arrival**: from the facts at pc 1014 of a late state, the machine's continuation
`afterArrive`. -/
theorem contArrive (hi : Inv L g d) (hl : LateSite d.site) (hAt : At u 1014 (factsAt L g 1014 d)) :
    ContSetup L g d.top u := by
  obtain ⟨hcw, hcv, hlt⟩ := hi.late hl
  obtain ⟨t', hr, ht'⟩ := (seg_top d hi.ok hlt hcw hcv hi.vb).rtg hAt
  rcases contTop (u := t') d.top hi.tid hi.ok (by simp [D.top]; omega) rfl rfl hi.vb hi.vb
      hi.re hi.lb hi.four hi.bw hi.vf hi.vf ht'
    with h | ⟨d', t'', hd, hr', ha, hinv⟩
  · exact .inl h
  · exact .inr ⟨d', t'', hd, hr.trans hr', ha, hinv⟩

/-! ### The barrier and the arrival -/

theorem live_1012 : ∀ r ∈ Flow.live 1013, r ∈ Flow.live 1012 := by decide +kernel
theorem live_1013 : ∀ r ∈ Flow.live 1014, r ∈ Flow.live 1013 := by decide +kernel

/-- **The barrier before the arrival** (pc 1012): thread 0 goes on to arrive; for any other thread
the guard of the arrival (`%p177`) is false, so it is skipped, and the thread continues with the
packs of the next block's words and the next iteration's loop test. -/
theorem step_bar21 (hi : Inv L g d) (hs : d.site = .bar21) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  have hpc : d.site.pc = 1012 := by rw [hs]; rfl
  have hc' : kernel.code[1012]? = some ins := hpc ▸ hc
  obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_bar_21)
  obtain rfl := fires_async_next (show AsyncAdvancesOp (.barSyncN _ _ _) from trivial) hf
  have hlate : LateSite d.site := by rw [hs]; trivial
  have h1 : At (PTX.next t) 1013 (factsAt L g 1013 d) :=
    at_next_live (pc := 1012) (pc' := 1013) (hpc ▸ h) rfl rfl live_1012
  by_cases hT : g % L.block = 0
  · have hn : next L g d e = some (some { d with site := .arrive }) := by
      simp [next, hs, hT]
    exact .inl (.inr ⟨{ d with site := .arrive }, PTX.next t, hn, .refl, h1,
      inv_late hi hlate (s := .arrive) trivial (fun _ => hT)⟩)
  · have h178 : valueOf L g d 177 = .pred false := by
      have : g % L.block % 128 ≠ 0 := by
        rw [Nat.mod_eq_of_lt hi.tid]; exact hT
      sm_vals
      simp [this]
    have hm : (177, Value.pred false) ∈ factsAt L g 1013 d := by
      have := Flow.mem_factsFrom (val := valueOf L g d) (show 177 ∈ Flow.live 1013 by
        decide +kernel)
      rwa [h178] at this
    obtain ⟨t', hr', ht'⟩ := (seg_off Flow.code_mbarArrive_3 hm).rtg h1
    have ht'' : At t' 1014 (factsAt L g 1014 d) :=
      ht'.mono (holds_live ht'.2.2.2.2 rfl (by decide +kernel))
    have hn : next L g d e = afterSetup L g d.top := by
      simp [next, hs, hT, afterArrive]
      rfl
    rcases contArrive hi hlate ht'' with hc | ⟨d', t'', hd, hr, ha, hinv⟩
    · exact .inl (.inl (hn.trans hc))
    · exact .inl (.inr ⟨d', t'', hn.trans hd, hr'.trans hr, ha, hinv⟩)

/-- **The arrival on `p_ready`** (pc 1013, thread 0): the packs of the next block's words and the
next iteration's loop test follow. -/
theorem step_arrive (hi : Inv L g d) (hs : d.site = .arrive) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  have hpc : d.site.pc = 1013 := by rw [hs]; rfl
  have hc' : kernel.code[1013]? = some ins := hpc ▸ hc
  obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_mbarArrive_3)
  have hf' := hpc ▸ hf
  obtain ⟨hu, m, tx', c, rel, sc, hk, -⟩ := fires_arrive_state hf'
  have hu' : u = PTX.next t := by simpa [mbarStateDest] using hu
  subst hu'
  have hlate : LateSite d.site := by rw [hs]; trivial
  have h1 : At (PTX.next t) 1014 (factsAt L g 1014 d) :=
    at_next_live (pc := 1013) (pc' := 1014) (hpc ▸ h) rfl rfl live_1013
  have hn : next L g d e = afterSetup L g d.top := by
    simp [next, hs, hk, afterArrive]
    rfl
  rcases contArrive hi hlate h1 with hc | ⟨d', t'', hd, hr, ha, hinv⟩
  · exact .inl (.inl (hn.trans hc))
  · exact .inl (.inr ⟨d', t'', hn.trans hd, hr, ha, hinv⟩)

/-! ### The register increase -/

theorem live_574 : ∀ r ∈ Flow.live 575, r ∈ Flow.live 574 := by decide +kernel

/-- **`setmaxnreg.inc`** (pc 574): the machine's first site; the barrier follows. -/
theorem step_setMaxReg (hi : Inv L g d) (hs : d.site = .setMaxReg)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step L g d e u := by
  have hpc : d.site.pc = 574 := by rw [hs]; rfl
  have hc' : kernel.code[574]? = some ins := hpc ▸ hc
  obtain rfl := Option.some.inj (hc'.symm.trans Flow.code_setMaxReg_1)
  obtain ⟨hi0, hm, hl, hcw, hcv⟩ := hi.start hs
  refine step_adv (dn := { d with site := .bar0 })
    (fun hf' => fires_next (show AdvancesOp (.setMaxReg _ _) from trivial) hf')
    (by simp [next, hs]) (by rw [hpc]; rfl) rfl (by rw [hpc]; exact live_574) ?_ h hf
  refine ⟨hi.tid, hi.ok, hi.i, fun k hk => absurd hk (by simp), fun k hk => absurd hk (by simp),
    ⟨fun k hk => absurd hk (by simp), fun _ => ⟨hi0, hm, hl, hcw, hcv⟩⟩, hi.wb, hi.vb,
    fun h => absurd h (by simp), fun h => absurd h (by simp [LateSite]),
    fun h => absurd h (by simp), hi.re, hi.lb, hi.four, hi.bw, hi.wf, hi.vf⟩

end
end PTX.Kernels.InklingRelDecode.Proof.Sm
