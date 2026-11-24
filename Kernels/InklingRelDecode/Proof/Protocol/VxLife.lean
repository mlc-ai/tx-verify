-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Protocol.HsLife
public import Kernels.InklingRelDecode.Proof2.Safety.Bar1Exit
public import Kernels.InklingRelDecode.Proof.Interface.FrTcData
public import Kernels.InklingRelDecode.Proof.Progress.WuPost

@[expose] public section

/-!
# The exit generation of barrier 0, and the rest of `SO.TmemLife`

The last `bar.sync 0` of a thread (no count, after two barrier-0 events; the epilogue's `bar3`,
the exit role's `bar`, the worker dispatch's `toExit`) is fired at a final site; after it the
thread only deallocates and exits (`Progress.Wt.post_all`). So a thread has at most one such event
(`final_unique`), and every event fired from a state that is neither a final nor a post site is
before it (`before_final`).

**The exit generation** (`final_sync`): when the last `bar.sync 0` of a thread `g` has returned,
every thread `h` of the CTA has its last `bar.sync 0`, and every event of `h` before it precedes,
in base causality (`CtaBarSync`), every event of `g` after `g`'s. The generation of `g`'s event
counts `h` by an arrival or by an exit (`final_key`: the proof of `Interface.final_witness`, with
the generation's key kept). In the first case the arrival is `h`'s last `bar.sync 0`, in the
generation of `g`'s. In the second case `h`'s exit follows its own last `bar.sync 0`
(`Proof2.exit_final_bar`), which was passed; its generation counts `g` by `g`'s last
`bar.sync 0` (then the two are in one generation) or by `g`'s exit, and two exits that are
witnesses of each other's last `bar.sync 0` close a cycle of the dependency order
(`Consistent.no_exit_cycle`).

`ldst_before_dealloc`, `dealloc_after_epilogue` (`Hs.TmemLifeRest`) follow: a deallocation is
fired at a post site, after the thread's last `bar.sync 0` (`Wu.post_seen`); the epilogue's poll
of `o_final`, a `tcgen05.ld` and its `tcgen05.wait::ld`, a `tcgen05.st` and its
`tcgen05.wait::st` are before the last `bar.sync 0` of their thread.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Vx
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof
open PTX.Kernels.InklingRelDecode.Proof.Interface
open PTX.Kernels.InklingRelDecode.Proof.Progress.Wt (FinalSite PostSite)
open CtaBarrier

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

section
variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
  (hS : ∀ g < L.threads, (threadCode L g Q).Sound) (ht : Frame.Tracked (code L Q) X)
include hpre hX hS ht

/-! ### The last `bar.sync 0` of a thread -/

/-- **Every event fired from a state that is neither a final nor a post site is before the last
`bar.sync 0` of its thread.** -/
theorem before_final {h jZ pcZ j : Nat} {m : BarMode} {s : TSt}
    (hZ : X.get (h, jZ) = some ⟨pcZ, .bar 0 none m⟩)
    (h2 : 2 ≤ ((X.tr h).take jZ).countP (Execution.isBarId 0))
    (hσ : St Q L X h j = some (some s)) (hnf : ¬ FinalSite s) (hnp : ¬ PostSite s) :
    j < jZ := by
  obtain ⟨sZ, hσZ, hfZ⟩ := Progress.Wt.final_site hpre hX hS ht hZ h2
  by_contra hle
  rcases Nat.lt_or_ge jZ j with hlt | hge
  · rcases Progress.Wt.post_all hZ hσZ hfZ j (by omega) with h0 | h0 | ⟨s', h', hp⟩
    · rw [hσ] at h0
      cases h0
    · rw [hσ] at h0
      cases h0
    · rw [hσ] at h'
      obtain rfl := Option.some.inj (Option.some.inj h')
      exact hnp hp
  · have hj : j = jZ := by omega
    subst hj
    rw [hσ] at hσZ
    obtain rfl := Option.some.inj (Option.some.inj hσZ)
    exact hnf hfZ

/-- **A thread has one last `bar.sync 0`.** -/
theorem final_unique {h a b pa pb : Nat} {ma mb : BarMode}
    (ha : X.get (h, a) = some ⟨pa, .bar 0 none ma⟩)
    (ha2 : 2 ≤ ((X.tr h).take a).countP (Execution.isBarId 0))
    (hb : X.get (h, b) = some ⟨pb, .bar 0 none mb⟩)
    (hb2 : 2 ≤ ((X.tr h).take b).countP (Execution.isBarId 0)) : a = b := by
  have key : ∀ {a b pa pb : Nat} {ma mb : BarMode},
      X.get (h, a) = some ⟨pa, .bar 0 none ma⟩ →
      2 ≤ ((X.tr h).take a).countP (Execution.isBarId 0) →
      X.get (h, b) = some ⟨pb, .bar 0 none mb⟩ →
      2 ≤ ((X.tr h).take b).countP (Execution.isBarId 0) → ¬ a < b := by
    intro a b pa pb ma mb ha ha2 hb hb2 hlt
    obtain ⟨sb, hσb, hfb⟩ := Progress.Wt.final_site hpre hX hS ht hb hb2
    have := before_final hpre hX hS ht ha ha2 hσb
    obtain ⟨sa, hσa, hfa⟩ := Progress.Wt.final_site hpre hX hS ht ha ha2
    rcases Progress.Wt.post_all ha hσa hfa b (by omega) with h0 | h0 | ⟨s', h', hp⟩
    · rw [hσb] at h0
      cases h0
    · rw [hσb] at h0
      cases h0
    · rw [hσb] at h'
      obtain rfl := Option.some.inj (Option.some.inj h')
      exact Progress.Wt.not_final_of_post hp hfb
  rcases Nat.lt_trichotomy a b with h1 | h1 | h1
  · exact absurd h1 (key ha ha2 hb hb2)
  · exact h1
  · exact absurd h1 (key hb hb2 ha ha2)

/-! ### The generation of a last `bar.sync 0` -/

/-- **The generation of a passed last `bar.sync 0` counts every thread of the CTA**, by its exit
(a witness of the return) or by its own last `bar.sync 0`, an arrival of the same generation. -/
theorem final_key {g jW pcW : Nat} (hW : X.get (g, jW) = some ⟨pcW, .bar 0 none .sync⟩)
    (hp : jW + 1 < (X.tr g).length) (h2 : 2 ≤ ((X.tr g).take jW).countP (Execution.isBarId 0))
    {h : Nat} (hcta : h / L.block = g / L.block) :
    (∃ y pcx, X.get (h, y) = some ⟨pcx, .exit⟩ ∧ Witness L X (.thread (h, y)) (g, jW)) ∨
      ∃ jZ pcZ m key, X.get (h, jZ) = some ⟨pcZ, .bar 0 none m⟩ ∧
        2 ≤ ((X.tr h).take jZ).countP (Execution.isBarId 0) ∧
        CtaBarArrivalK L X (h, jZ) key ∧ CtaBarK L X (g, jW) key := by
  have hb : L.block = 256 := hpre.block
  have hWbar : X.IsBarrier (g, jW) 0 none pcW := hW
  obtain ⟨key, hk, hdone⟩ := ctaBarDone_of_returned hX hWbar hp
  have hgth : g < L.threads := hk.1
  have hc : g / L.block < L.grid := NamedBar.cta_lt hgth
  have hkid : key % 16 = 0 := by
    obtain ⟨count', pc', he'⟩ := hk.2.1
    exact (Kind.bar.inj (Event.mk.inj (Option.some.inj (he'.symm.trans hW))).2).1
  have hgen : CtaBarrier.GenerationOf L.block (X.barriers (g / L.block)) (g, jW) 0 (key / 16) := by
    have := hk.2.2
    rwa [hkid] at this
  have hG2 : 2 ≤ key / 16 := le_trans h2 (NamedBar.ordinal_le_generation hX hc hgen)
  obtain ⟨ic, hic⟩ := hdone
  have hic0 : CtaBarrier.CompletesAt L.block (X.barriers (g / L.block)) ic 0 (key / 16) := by
    have := hic
    rwa [hkid] at this
  obtain ⟨-, -, last, hlast⟩ := hX.ctaBar.2 _ hc
  obtain ⟨jr, sW, warpW, cntW, lanesW, lW, hjr, hatW, hmW, hgW, tW, hpW⟩ := hgen
  have hcntW : cntW = none := by
    obtain ⟨-, -, pc'', mode, hbar''⟩ :=
      ((hX.ctaBar.2 _ hc).2.1 _ (List.mem_of_getElem? hjr)) (lW, (g, jW)) hmW
    have := hbar''.symm.trans hW
    simp only [Option.some.injEq, Event.mk.injEq, Kind.bar.injEq] at this
    exact this.2.2.1
  subst hcntW
  have hjric : jr ≤ ic := by
    by_contra hlt
    obtain ⟨r, s, t, hr, hs, htt, hg0, hg1⟩ := hic0
    have hat := NamedBar.at_succ hr hs htt
    have := NamedBar.at_gen_mono (id := 0) (show ic + 1 ≤ jr by omega) hat hatW
    omega
  have hl : h % L.block < L.block := Nat.mod_lt _ (by omega)
  have hthr : g / L.block * L.block + h % L.block = h := by
    rw [← hcta, Nat.mul_comm]
    exact Nat.div_add_mod h L.block
  rcases NamedBar.completes_counts hic0 hjr hatW hpW hgW (by simp [CtaBarrier.target]) hjric hl
    with ⟨i, y, hi, hy⟩ | ⟨i, cnt', lanes', Z, si, ti, hi, hri, hZm, hsi, hti, hgi, htg⟩
  · left
    obtain ⟨-, hy1, pcx, hget⟩ := (hX.ctaBar.2 _ hc).2.1 _ (List.mem_of_getElem? hy)
    have hcnt : CtaBarCounted L X (g, jW) y :=
      ⟨key, ic, hk, hic, i, .exit (h % L.block) y, hy, by simp [CtaBarrier.Record.refs], hi,
        .inr ⟨h % L.block, rfl⟩⟩
    have hy' : y ∈ (X.barriers (g / L.block)).flatMap CtaBarrier.Record.refs :=
      List.mem_flatMap.mpr ⟨_, List.mem_of_getElem? hy, by simp [CtaBarrier.Record.refs]⟩
    obtain ⟨y1, y2⟩ := y
    simp only at hy1
    have hy1' : y1 = h := hy1.trans hthr
    subst hy1'
    exact ⟨y2, pcx, hget, Witness.of_need L (ctaBarCounted_witnessed L X (g, jW) _ hW hy' hcnt)
      ⟨_, hget⟩ rfl⟩
  · right
    obtain ⟨-, hZ1, pcZ, mZ, hZbar⟩ :=
      ((hX.ctaBar.2 _ hc).2.1 _ (List.mem_of_getElem? hri)) (h % L.block, Z) hZm
    have hZh : Z.1 = h := hZ1.trans hthr
    have hcnt' : cnt' = none := by
      rcases (bar_event_static hX (by omega) hZbar).2 with ⟨h1, -⟩ | ⟨-, h1⟩
      · exact h1
      · subst h1
        simp [CtaBarrier.target, CtaBarrier.warps, hb] at htg
    subst hcnt'
    have hstart := NamedBar.start_le_ordinal (Bar.loopGroup_sub hpre) Bar.loopGroup_card
      (Bar.loopGroup_ne hpre) Bar.loopGroup_target
      ((Bar.bar0_sources hpre hX hS ht).protocol hX hc) hsi hti (by omega)
    obtain ⟨-, -, -, -, hord, -⟩ := NamedBar.record_ordinal hX hc hlast hri hsi hZm
    obtain ⟨z1, z2⟩ := Z
    simp only at hZh
    subst hZh
    have hZc : z1 / L.block = g / L.block := hcta
    refine ⟨z2, pcZ, mZ, key, hZbar, by simp only at hord; omega, ?_, hk⟩
    refine ⟨by rw [← hthr]; exact NamedBar.cta_thread_lt hc hl,
      ⟨none, pcZ, mZ, by rw [hkid]; exact hZbar⟩, ?_⟩
    rw [hZc, hkid]
    exact ⟨i, si, _, none, lanes', _, hri, hsi, hZm, hgi, ti, hti⟩

/-- **The exit generation of barrier 0.** When the last `bar.sync 0` of `g` has returned, a
thread `h` of the CTA has its last `bar.sync 0`, and each of `h`'s events before it precedes, in
base causality, each event of `g` after `g`'s last `bar.sync 0`. -/
theorem final_sync {g jW pcW h : Nat} (hW : X.get (g, jW) = some ⟨pcW, .bar 0 none .sync⟩)
    (hp : jW + 1 < (X.tr g).length) (h2 : 2 ≤ ((X.tr g).take jW).countP (Execution.isBarId 0))
    (hh : h < L.threads) (hcta : h / L.block = g / L.block) :
    ∃ jZ pcZ m, X.get (h, jZ) = some ⟨pcZ, .bar 0 none m⟩ ∧
      2 ≤ ((X.tr h).take jZ).countP (Execution.isBarId 0) ∧
      ∀ before after, before < jZ → jW < after → after < (X.tr g).length →
        baseCausality L X (h, before) (g, after) := by
  have hg : g < L.threads := event_thread_lt hX hW
  have hsame : SameCta L h g := ⟨hh, hg, hcta⟩
  have sync : ∀ {jZ key : Nat}, CtaBarArrivalK L X (h, jZ) key → CtaBarK L X (g, jW) key →
      ∀ before after, before < jZ → jW < after → after < (X.tr g).length →
        baseCausality L X (h, before) (g, after) :=
    fun ha hk before after h1 h2 h3 =>
      .single (Or.inr (Or.inl ⟨hsame, _, _, _, ha, hk, h1, h2, h3⟩))
  rcases final_key hpre hX hS ht hW hp h2 hcta with ⟨y, pcx, hy, hwit⟩ |
      ⟨jZ, pcZ, m, key, hZ, hZ2, harr, hk⟩
  · obtain ⟨jZ, pcZ, hjy, hZ, hZ2⟩ := Proof2.exit_final_bar hpre hX hy
    have hyl : y < (X.tr h).length := len_of_get hy
    refine ⟨jZ, pcZ, .sync, hZ, hZ2, ?_⟩
    rcases final_key hpre hX hS ht hZ (by omega) hZ2 hcta.symm with ⟨y', pcx', hy', hwit'⟩ |
        ⟨jZ', pcZ', m', key', hZ', hZ2', harr', hk'⟩
    · exfalso
      obtain ⟨jW', pcW', hjy', hW', hW2'⟩ := Proof2.exit_final_bar hpre hX hy'
      have hjj : jW' = jW := final_unique hpre hX hS ht hW' hW2' hW h2
      subst hjj
      exact hX.no_exit_cycle (E := (h, y)) (f := (g, jW')) (Z := (g, y')) (W := (h, jZ))
        hwit ⟨_, false, hW, rfl⟩ ⟨rfl, hjy', len_of_get hy'⟩ hwit'
        ⟨_, false, hZ, rfl⟩ ⟨rfl, hjy, hyl⟩
    · have hjj : jZ' = jW := final_unique hpre hX hS ht hZ' hZ2' hW h2
      subst hjj
      have hkid : key' % 16 = 0 := by
        obtain ⟨count', pc', mode', he'⟩ := harr'.2.1
        exact (Kind.bar.inj (Event.mk.inj (Option.some.inj (he'.symm.trans hW))).2).1
      have hkW : CtaBarK L X (g, jZ') key' :=
        ⟨harr'.1, ⟨none, pcW, by rw [hkid]; exact hW⟩, harr'.2.2⟩
      exact sync (CtaBarK.arrival hk') hkW
  · exact ⟨jZ, pcZ, m, hZ, hZ2, sync harr hk⟩

end

/-! ### The deallocation, the loads, the stores and the polls -/

section
variable (hpre : Pre Q L mem0) (hX : Consistent L kernel asms mem0 X)
  (hf : ThreadFacts Q L mem0 X)
include hpre hX hf

/-- **A deallocation follows its thread's last `bar.sync 0`.** -/
theorem dealloc_final {g k pc a n : Nat} {grp : CtaGroup} {dst : Option Loc}
    (he : X.get (g, k) = some ⟨pc, .tc (.resource grp dst (.dealloc a n))⟩) :
    ∃ jW pcW, jW < k ∧ X.get (g, jW) = some ⟨pcW, .bar 0 none .sync⟩ ∧
      2 ≤ ((X.tr g).take jW).countP (Execution.isBarId 0) := by
  obtain ⟨-, h | h | ⟨d, hσ, hs, -, -⟩⟩ := res_event_state hpre hX hf he
  · obtain ⟨tm, -, -, hact⟩ := h
    cases hact
  · obtain ⟨tm, -, -, hact⟩ := h
    cases hact
  · have hk : k < (X.tr g).length := len_of_get he
    obtain ⟨j, hj, pcj, m, hget, h2⟩ := Progress.Wu.post_seen hX hf.sound k _ hk.le hσ
      (by simp [PostSite, hs])
    have hbar := hX.isBarrier_of_arrival Interface.noBarArrive ⟨m, hget⟩
    exact ⟨j, pcj, hj, hbar, h2⟩

omit hpre hX hf in
/-- The state after an event of a softmax state that does not leave the region. -/
theorem st_succ_sm {g k : Nat} {d : Sm.D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : St Q L X g k = some (some (.d (.sm d)))) (hl : ¬ DComp.leaves L g d e) :
    St Q L X g (k + 1) =
      ((Sm.next L g d e).map (Option.map DComp.St.sm)).map (Option.map TSt.d) := by
  have he' : (X.tr g)[k]? = some e := he
  have : Frame.stateAt (code L Q) X g k = some (some (.d (.sm d))) := hσ
  show Frame.stateAt (code L Q) X g (k + 1) = _
  rw [Frame.stateAt_succ he', this]
  show (threadCode L g Q).next (.d (.sm d)) e = _
  rw [next_d]
  show (DComp.smNext L g d e).map (Option.map TSt.d) = _
  unfold DComp.smNext
  simp only [hl, ↓reduceIte]

omit hpre hX hf in
/-- The state after an event of an epilogue state. -/
theorem st_succ_epi {g k : Nat} {d : Epi.D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : St Q L X g k = some (some (.d (.epi d)))) :
    St Q L X g (k + 1) =
      ((Epi.next d e).map (Option.map DComp.St.epi)).map (Option.map TSt.d) := by
  have he' : (X.tr g)[k]? = some e := he
  have : Frame.stateAt (code L Q) X g k = some (some (.d (.epi d))) := hσ
  show Frame.stateAt (code L Q) X g (k + 1) = _
  rw [Frame.stateAt_succ he', this]
  rfl

/-- **The `tcgen05.wait::ld` after a Tensor Memory load**: the event after a load at `ldS`,
`ldO` or the epilogue's `ld` is the wait at `waitLd`, `waitLdO` or the epilogue's `waitLd`, when
the thread has a later event that is not undefined behaviour (at `ldS` the machine is dead where a
loaded word is not four bytes, and every later event is then undefined behaviour). -/
theorem ld_wait_after {g k pc a : Nat} {vals : List Value} {sh : TcShape} (hg : g < L.threads)
    (hlater : ∃ j pcj kd, k < j ∧ X.get (g, j) = some ⟨pcj, kd⟩ ∧ ∀ f, kd ≠ .ub f)
    (he : X.get (g, k) = some ⟨pc, .tc (.ld a vals sh)⟩) :
    ∃ pcw, X.get (g, k + 1) = some ⟨pcw, .tc .waitLd⟩ := by
  obtain ⟨j, pcj, kd, hkj, hej, hub⟩ := hlater
  have hjl : j < (X.tr g).length := len_of_get hej
  have hk : k + 1 < (X.tr g).length := by omega
  have hb : L.block % 32 = 0 := by rw [hpre.block]
  obtain ⟨ew, hew⟩ : ∃ ew, X.get (g, k + 1) = some ew := ⟨_, List.getElem?_eq_getElem hk⟩
  have htr : St Q L X g (k + 1) ≠ some none := hf.tracked g (k + 1) hg
  rcases (Lk.tcld_event hpre hX hf hg he).2.2 with ⟨d, hσ, ⟨hs, -⟩ | ⟨hs, -⟩⟩ | ⟨d, hσ, hs, -⟩
  · have hst := st_succ_sm he hσ (by simp [DComp.leaves, hs])
    by_cases hc : vals.length = 64 ∧ ∀ x ∈ vals, x.bytes = 4
    · have hn : Sm.next L g d ⟨pc, .tc (.ld a vals sh)⟩ =
          some (some { d with site := .waitLd, sv := Sm.svOf vals hc.2 }) := by
        simp only [Sm.next, hs]
        rw [dite_eq_left hc]
      rw [hn] at hst
      obtain ⟨u1, hF1⟩ := fired_cont hX hf hg hew hst (by simp [ExitState])
      rw [Sm.shape_waitLd hb (fired_sm hF1) rfl] at hew
      exact ⟨_, hew⟩
    · have hn : Sm.next L g d ⟨pc, .tc (.ld a vals sh)⟩ = none := by
        simp only [Sm.next, hs]
        rw [dite_eq_right hc]
      rw [hn] at hst
      have hj : St Q L X g j = none := Frame.stateAt_none_mono hst (by omega)
      rcases Frame.fired hf.sound hX hej with ⟨σ, o, hσj, -⟩ | ⟨-, pc', f, he'⟩
      · have hj' : Frame.stateAt (fun g => threadCode L g Q) X g j = none := hj
        rw [hj'] at hσj
        cases hσj
      · simp only [Event.mk.injEq] at he'
        exact absurd he'.2 (hub f)
  · have hst := st_succ_sm he hσ (by simp [DComp.leaves, hs])
    have hn : Sm.next L g d ⟨pc, .tc (.ld a vals sh)⟩ = some (some
        { d with site := .waitLdO, stg := { d.stg with ow := Sm.owOf vals } }) := by
      simp only [Sm.next, hs]
    rw [hn] at hst
    obtain ⟨u1, hF1⟩ := fired_cont hX hf hg hew hst (by simp [ExitState])
    rw [Sm.shape_waitLdO hb (fired_sm hF1) rfl] at hew
    exact ⟨_, hew⟩
  · have hst := st_succ_epi he hσ
    have hl : vals.length = 64 := (Lk.tcld_event hpre hX hf hg he).2.1
    have hn : Epi.next d ⟨pc, .tc (.ld a vals sh)⟩ =
        some (some { d with site := .waitLd, o := vals }) := by
      simp [Epi.next, hs, hl]
    rw [hn] at hst
    obtain ⟨u1, hF1⟩ := fired_cont hX hf hg hew hst (by simp [ExitState])
    rw [Epi.shape_waitLd hb (fired_epi hF1) rfl] at hew
    exact ⟨_, hew⟩

/-- **`SO.TmemLife.dealloc_after_epilogue`.** -/
theorem dealloc_after_epilogue {d : EvId} {h j : Nat} {pc pc' p : Nat} {grp : CtaGroup}
    {dst : Option Loc} {da n : Nat} {acq : Bool} {sc : MbarScope} {c : Nat}
    (hd : X.get d = some ⟨pc, .tc (.resource grp dst (.dealloc da n))⟩)
    (hcta : h / L.block = d.1 / L.block)
    (hw : X.get (h, j) = some ⟨pc', .wait (EvW.oFinal L c) p true acq sc⟩) :
    baseCausality L X (h, j) d := by
  obtain ⟨g, k⟩ := d
  simp only at hcta
  obtain ⟨jW, pcW, hjk, hW, h2⟩ := dealloc_final hpre hX hf hd
  have hkl : k < (X.tr g).length := len_of_get hd
  have hh : h < L.threads := event_thread_lt hX hw
  obtain ⟨jZ, pcZ, m, hZ, hZ2, hcaus⟩ :=
    final_sync hpre hX hf.sound hf.tracked hW (by omega) h2 hh hcta
  have hjZ : j < jZ := by
    rcases (Hs.poll_class hpre hX hf hw).2.2 with
      ⟨d', hσ, -⟩ | ⟨d', hσ, -⟩ | ⟨d', P, hσ, -⟩ | ⟨d', P, hσ, -⟩ | ⟨d', P, hσ, -⟩ |
      ⟨d', hσ, hs, -⟩
    all_goals
      refine before_final hpre hX hf.sound hf.tracked hZ hZ2 hσ ?_ ?_
    all_goals simp [FinalSite, PostSite]
    all_goals simp [hs]
  exact hcaus j k hjZ hjk hkl

/-- **`SO.TmemLife.ldst_before_dealloc`.** -/
theorem ldst_before_dealloc {e d : EvId} {a : Nat} {vals : List Value} {sh : TcShape} {pc : Nat}
    {grp : CtaGroup} {dst : Option Loc} {da n : Nat}
    (hd : X.get d = some ⟨pc, .tc (.resource grp dst (.dealloc da n))⟩)
    (hcta : (d.1 / L.block) = (e.1 / L.block)) :
    (X.TLd e a vals sh → TcMma.WaitBefore L X .waitLd e d) ∧
      (X.TSt e a vals sh → TcMma.WaitBefore L X .waitSt e d) := by
  obtain ⟨g, k⟩ := d
  obtain ⟨h, i⟩ := e
  simp only at hcta
  obtain ⟨jW, pcW, hjk, hW, h2⟩ := dealloc_final hpre hX hf hd
  have hkl : k < (X.tr g).length := len_of_get hd
  -- the thread's last `bar.sync 0`, and the causality from its earlier events
  have key : ∀ {ev : Event}, X.get (h, i) = some ev →
      ∃ jZ pcZ m, X.get (h, jZ) = some ⟨pcZ, .bar 0 none m⟩ ∧
        2 ≤ ((X.tr h).take jZ).countP (Execution.isBarId 0) ∧
        ∀ before, before < jZ → baseCausality L X (h, before) (g, k) := by
    intro ev hev
    have hh : h < L.threads := event_thread_lt hX hev
    obtain ⟨jZ, pcZ, m, hZ, hZ2, hcaus⟩ :=
      final_sync hpre hX hf.sound hf.tracked hW (by omega) h2 hh hcta.symm
    exact ⟨jZ, pcZ, m, hZ, hZ2, fun before hb => hcaus before k hb hjk hkl⟩
  refine ⟨fun ⟨pcl, hl⟩ => ?_, fun ⟨pcs, hs⟩ => ?_⟩
  · have hh : h < L.threads := event_thread_lt hX hl
    obtain ⟨jZ, pcZ, m, hZ, hZ2, hcaus⟩ := key hl
    have hiZ : i < jZ := by
      rcases (Lk.tcld_event hpre hX hf hh hl).2.2 with ⟨d', hσ, ⟨hs', -⟩ | ⟨hs', -⟩⟩ |
        ⟨d', hσ, hs', -⟩
      all_goals
        refine before_final hpre hX hf.sound hf.tracked hZ hZ2 hσ ?_ ?_
      all_goals simp [FinalSite, PostSite]
      all_goals simp [hs']
    have hZl : jZ < (X.tr h).length := len_of_get hZ
    obtain ⟨pcw, hwt⟩ := ld_wait_after hpre hX hf hh ⟨jZ, pcZ, _, hiZ, hZ, fun f h => by cases h⟩ hl
    have hne : i + 1 ≠ jZ := by
      intro heq
      rw [heq, hZ] at hwt
      cases hwt
    exact ⟨(h, i + 1), ⟨pcw, hwt⟩, rfl, by simp, .inl (hcaus _ (by omega))⟩
  · have hh : h < L.threads := event_thread_lt hX hs
    obtain ⟨jZ, pcZ, m, hZ, hZ2, hcaus⟩ := key hs
    obtain ⟨d', hσ, hsite⟩ := Lk.tcst_event hX hf hh hs
    have hiZ : i < jZ := by
      refine before_final hpre hX hf.sound hf.tracked hZ hZ2 hσ ?_ ?_ <;>
        simp [FinalSite, PostSite]
    have hZl : jZ < (X.tr h).length := len_of_get hZ
    obtain ⟨pcw, hwt⟩ := Hs.wait_after hX hf hh (by omega) hσ
      (by rcases hsite with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h1])
    have hne : i + 1 ≠ jZ := by
      intro heq
      rw [heq, hZ] at hwt
      cases hwt
    exact ⟨(h, i + 1), ⟨pcw, hwt⟩, rfl, by simp, .inl (hcaus _ (by omega))⟩

/-- **`Hs.TmemLifeRest`**, proved. -/
theorem tmemLifeRest_of : Hs.TmemLifeRest L X :=
  ⟨fun hd hcta => ldst_before_dealloc hpre hX hf hd hcta,
    fun hd hcta hw => dealloc_after_epilogue hpre hX hf hd hcta hw⟩

/-- **`SO.TmemLife`**, proved. -/
theorem tmemLife_of : SO.TmemLife L X :=
  Hs.tmemLife_of hpre hX hf (tmemLifeRest_of hpre hX hf)

end

end
end PTX.Kernels.InklingRelDecode.Proof.Vx
