-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.InklingRelDecode.Proof.Softmax.Export.SumEv
public import Kernels.InklingRelDecode.Proof.Lib.KStD
public import Kernels.InklingRelDecode.Proof.Lib.ExitBack
import Kernels.InklingRelDecode.Proof.Common.BarPc
import Kernels.InklingRelDecode.Proof.Softmax.Soft.EntGlue
import Kernels.InklingRelDecode.Proof.Common.SoftmaxEntry
import Kernels.InklingRelDecode.Proof.Common.ValueSound
import Kernels.InklingRelDecode.Proof.Common.ValueFollow
import Kernels.InklingRelDecode.Proof.Softmax.Export.WordsEv
import Kernels.InklingRelDecode.Proof.Softmax.Soft.LInv
import Lemmas.Flow.StrictWindow
import Kernels.InklingRelDecode.Proof.Softmax.Data.ScaleEv
import Kernels.InklingRelDecode.Proof.Softmax.Data.LKeep
import Kernels.InklingRelDecode.Proof.Softmax.Data.LEmpty
import Kernels.InklingRelDecode.Proof.Lib.EmptyBack
import Kernels.InklingRelDecode.Proof.Lib.EpiNext

@[expose] public section

/-! # The sum, the maximum and the scale at the epilogue's first local code

The last softmax event before a state at pc 2562 is the barrier of pc 1012 or the arrival of
pc 1013 of the last round. The registers 1915, 1914 and 498 stay to pc 2562 as the value machine
has them there: the row's `kState` sum, its finite maximum when the sum is positive, and the
scale. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Flow PTX.Proof Control Data Soft

variable {Q : Params} {L : Launch} {g : Nat}

private theorem next_epi {ent : Entry} {L : Launch} {g : Nat} {d d' : Control.D} {ev : Event}
    (hn : Control.next ent L g d ev = some (some d')) (he : d'.site = .epilogue) :
    (d.i = ent.limit ∧ (d.site = .bar0 ∨ d.site = .pre 63)) ∨
      (d.i + 1 = ent.limit ∧ (d.site = .bar21 ∨ d.site = .arrive)) := by
  obtain ⟨site, i, held⟩ := d
  cases site <;> simp only [Control.next] at hn
  all_goals (try simp only [Control.loopSite, Control.advance] at hn)
  all_goals (try split at hn)
  all_goals (try split at hn)
  all_goals (try (simp only [Option.some.injEq] at hn; rw [← hn] at he))
  all_goals (try split_ifs at he)
  all_goals (simp_all; try (apply Fin.ext; simp; omega))

/-- The last event before the epilogue's wait is, in a launch with no block, the barrier or a
preload at the loop's end; with blocks, the barrier or arrival of the last round. -/
private theorem last_site_gen {m : Mem0} {X : Execution} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) {k : Nat} {e ev : Event}
    (he : X.get (g, k) = some e) (hnx : X.get (g, k + 1) = some ev) (hev : ev.pc = 2565)
    (hu : ∀ f, ev.kind ≠ .ub f) (hue : ∀ f, e.kind ≠ .ub f) (lo : 574 < e.pc) (hi : e.pc < 2331)
    : ∃ w ent d n, Frame.stateAt (thread Q L) X g k = some (some (softState w ent d n)) ∧
      ((d.i = ent.limit ∧ (d.site = .bar0 ∨ d.site = .pre 63)) ∨
        (d.i + 1 = ent.limit ∧ (d.site = .bar21 ∨ d.site = .arrive))) ∧
      Control.Inv ent (g % L.block) d ∧ e.pc = d.site.pc ∧
      ent.limit = Q.numIters ((L.ctaidOf (g / L.block)).get .z)
        ((L.ctaidOf (g / L.block)).get .x) ∧
      ∃ d', Control.next ent L g d e = some (some d') ∧ d'.site = .epilogue := by
  obtain ⟨w, ent, d, n, t, ins, u, hsc, -, inv, atpc, -, -⟩ :=
    softmax_event_entry hp hX hf he hue lo hi
  have hg := Frame.lt_of_get hX he
  have len := (List.getElem?_eq_some_iff.mp he).1.le
  obtain ⟨-, -, lim, -⟩ := ent_glue hp hX hg len hsc
  obtain ⟨σ, hs, -⟩ := event_table hf hX hp hnx hu
  have pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX hnx hs hu
  have step := Frame.stateAt_succ (C := thread Q L) (X := X) (show (X.tr g)[k]? = some e from he)
  rw [hsc] at step
  simp only [softState, thread, Code.roleThread, Code.counted, Code.toMachine, Code.glue,
    Option.bind_some] at step
  rcases hd : Control.next ent L g d e with _ | _ | d'
  · rw [hd] at step
    simp only [Option.map_none] at step
    rw [step] at hs
    cases hs
  · rw [hd] at step
    simp only [Option.map_some, Option.map_none] at step
    rw [step] at hs
    cases hs
  · have hx : d'.site = .epilogue := by
      by_contra hxd
      have en : (Control.code ent L g).enter
          (fun _ : Unit => Epilogue.Control.code (epiEntry ent (g % L.block)) L g) epiExit d' =
          .inl d' := Code.enter_none (by simp [epiExit, hxd])
      rw [hd] at step
      simp only [Option.map_some, en] at step
      rw [step] at hs
      obtain rfl := Option.some.inj (Option.some.inj hs)
      change ev.pc = d'.site.pc at pc
      rcases d'.site.pc_range with h | h
      · omega
      · exact hxd h
    exact ⟨w, ent, d, n, hsc, next_epi hd hx, inv, atpc, by rw [← lim], d', hd, hx⟩

private theorem last_site {m : Mem0} {X : Execution} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X) {k : Nat} {e ev : Event}
    (he : X.get (g, k) = some e) (hnx : X.get (g, k + 1) = some ev) (hev : ev.pc = 2565)
    (hu : ∀ f, ev.kind ≠ .ub f) (hue : ∀ f, e.kind ≠ .ub f) (lo : 574 < e.pc) (hi : e.pc < 2331)
    (hn : 0 < Q.numIters ((L.ctaidOf (g / L.block)).get .z) ((L.ctaidOf (g / L.block)).get .x)) :
    ∃ w ent d n, Frame.stateAt (thread Q L) X g k = some (some (softState w ent d n)) ∧
      (d.site = .bar21 ∨ d.site = .arrive) ∧ d.i + 1 = ent.limit ∧
      Control.Inv ent (g % L.block) d ∧ e.pc = d.site.pc := by
  obtain ⟨w, ent, d, n, hsc, hs, inv, atpc, lim, -⟩ :=
    last_site_gen hp hX hf he hnx hev hu hue lo hi
  rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exfalso
    have : d.i = 0 := by
      rcases h2 with h | h
      · exact inv.init (Or.inr h)
      · exact (inv.pre 63 h).1
    omega
  · exact ⟨w, ent, d, n, hsc, h2, h1, inv, atpc⟩

private theorem at_pre {m : Mem0} {X : Execution} (hp : Pre Q L m) {k : Nat}
    {u s t0 : TState} {e : Event} {sd : (threadD Q L g).D} (hg : g < L.threads)
    (hr : Run kernel Assumptions.all L g {} ((X.tr g).take k) (some u))
    (hus : Relation.ReflTransGen (Tau kernel Assumptions.all L g) u s)
    (hes : EStep kernel Assumptions.all L g s e (some t0))
    (hs : Frame.stateAt (threadD Q L) X g k = some (some sd)) (hu : ∀ f, e.kind ≠ .ub f) :
    (threadD Q L g).AtD sd s := by
  have hC := threadD_sound hp hg
  obtain ⟨s', h1, h2⟩ := Code.end_siteU hC hr hs
  rcases h2 with h2 | ⟨f, hf⟩
  · obtain rfl := stop_unique hus h1 (stops_of_estep hes) (Code.stops_of_good hC h2)
    exact h2.1
  · obtain rfl := stop_unique hus h1 (stops_of_estep hes) ⟨_, hf⟩
    obtain ⟨mm, ho, hfire⟩ := hes
    obtain rfl := Out.ev.inj (ho.symm.trans hf)
    exact absurd (congrArg Event.kind hfire.1) (hu f)

/-- **The registers at pc 2562**: after the rounds of a row the sum (register 1915) is the row's
`kState` sum for every output dimension, the maximum (1914) its finite maximum when the sum is
positive, and register 498 holds the scale. A state of the lane at pc 2562 whose next event is
at pc 2565. -/
public theorem epi_sum_entry {m : Mem0} {X : Execution} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hB : ∀ g, Lib.BiasEv Q L g X) (hS : ∀ g, Lib.ScoreEv Q L g X) (lane : g % L.block < 128)
    (hv : Lib.QRowValid Q L (g / L.block) (Lib.softRow (g % L.block)))
    (hn : 0 < Q.numIters ((L.ctaidOf (g / L.block)).get .z) ((L.ctaidOf (g / L.block)).get .x))
    {k : Nat} {t0 t : TState} {ev : Event}
    (hr : Run kernel Assumptions.all L g {} ((X.tr g).take k) (some t0))
    (ht : Lib.TauPath L g t0 t) (hpc : t.pc = 2562) (nxt : X.get (g, k) = some ev)
    (hev : ev.pc = 2565) (hu : ∀ f, ev.kind ≠ .ub f) :
    ∃ l : ℝ, t.regs 1915 = some (.float .f32 l) ∧ 0 ≤ l ∧
      (∀ d, l = (Lib.SoftRow.kState Q ((L.ctaidOf (g / L.block)).get .z)
        ((L.ctaidOf (g / L.block)).get .x) (Lib.softRow (g % L.block) / 6)
        (Lib.laneHead L g) d).l) ∧
      (0 < l → ∃ mr : ℝ, t.regs 1914 = some (.float .f32 mr) ∧
        (∀ d, mr = (Lib.SoftRow.kState Q ((L.ctaidOf (g / L.block)).get .z)
          ((L.ctaidOf (g / L.block)).get .x) (Lib.softRow (g % L.block) / 6)
          (Lib.laneHead L g) d).m.toReal) ∧
        t.regs 498 = some (.float .f32 (Q.scale * log2eF32))) := by
  have hg := Frame.lt_of_get hX nxt
  have hlen : _ < (X.tr g).length := (List.getElem?_eq_some_iff.mp nxt).1
  cases k with
  | zero =>
    rw [List.take_zero] at hr
    cases hr
    have := Lib.back_in Lib.ex_bwd ht (by rw [hpc]; decide)
    simp [Lib.ex_zero] at this
  | succ k' =>
    have hk' : k' < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, X.get (g, k') = some e := ⟨_, List.getElem?_eq_getElem hk'⟩
    obtain ⟨u, s, hu', hus, hes⟩ := Lib.pre_idx he hr
    have hue : ∀ f, e.kind ≠ .ub f := Frame.noUbBefore_of_get hX nxt k' (by omega) e he
    have pcs : e.pc = s.pc := EventFrame.estep_source_pc hes
    obtain ⟨lo, hi⟩ := Lib.exit_range hes ht hpc
    obtain ⟨w, ent, d, n, hsc, hsite, hlim, inv, atpc⟩ :=
      last_site hp hX hf he nxt hev hu hue (pcs ▸ lo) (pcs ▸ hi) hn
    have len : k' ≤ (X.tr g).length := by omega
    obtain ⟨sv, hs, hshape⟩ := value_state hsc
    obtain ⟨y, hy, rfl⟩ := softD_shape hshape
    obtain ⟨-, -, lim, -⟩ := ent_glue hp hX hg len hsc
    obtain ⟨Mx, J⟩ := soft_lex hp hX (words_ev hp hX hf hB hS lane hv)
      (sum_ev hp hX hf hB hS lane hv) k' len _ hs (Frame.noUbBefore_of_get hX he) w ent y n rfl
      inv.entry
    have hat := at_pre hp hg hu' hus hes hs hue
    change (Data.codeS ent L g).AtD y s at hat
    obtain ⟨-, -, -, -, regs⟩ := id hat
    have hys : y.c.site = .bar21 ∨ y.c.site = .arrive := by rw [hy]; exact hsite
    have hpcs : s.pc = 1012 ∨ s.pc = 1013 := by
      rw [← pcs, atpc]
      rcases hsite with h | h <;> rw [h] <;> simp [Site.pc]
    have kp := Lib.exit_regs hes hpcs ht
    have u1 : (updS y.c.site).toNat = 1 := by rcases hys with h | h <;> rw [h] <;> rfl
    have hN : y.c.i + (updS y.c.site).toNat = Q.numIters ((L.ctaidOf (g / L.block)).get .z)
        ((L.ctaidOf (g / L.block)).get .x) := by rw [u1, ← lim, ← hlim, hy]
    have r1 : s.regs 1915 = some y.v.l := by
      have := atS_lF regs
      rcases hys with h | h <;> simp [lF, lFS, h, psB] at this <;> exact this
    obtain ⟨-, -, -, -, r0⟩ := atS_code hat
    have r2 : Holds s.regs (dF L y) := ((holds_append _ _ _).mp r0).2
    have r3 : s.regs 498 = some (scaleW L) ∧ s.regs 1914 = some y.v.m := by
      rcases hys with h | h <;> simp [dF, dFS, h, inRound, Holds] at r2 <;> exact r2
    have jl := J.l
    have jm := Mx.m
    rw [hN] at jl jm
    have hlev := jl.2 hn
    have hs0 : 0 < Q.scale * log2eF32 := mul_pos hp.scalePos (by unfold log2eF32; norm_num)
    obtain ⟨hnn, hpos⟩ := Lib.SoftRow.kSt_l_pos Q hs0 ((L.ctaidOf (g / L.block)).get .z)
      ((L.ctaidOf (g / L.block)).get .x) (Lib.softRow (g % L.block) / 6) (Lib.laneHead L g) 0
      (Q.numIters ((L.ctaidOf (g / L.block)).get .z) ((L.ctaidOf (g / L.block)).get .x))
    refine ⟨_, ?_, hnn, fun d => ?_, fun hlp => ?_⟩
    · rw [kp 1915 (by simp [Lib.exR]), r1, hlev.1, erealValue_coe]
      rfl
    · rw [Lib.SoftRow.kState_eq]
      exact (Lib.SoftRow.kSt_ml_d Q _ _ _ _ 0 d _).2
    · obtain ⟨Mv, hM⟩ := hpos hlp
      refine ⟨Mv, ?_, fun d => ?_, ?_⟩
      · have : (Lib.laneSt Q L g (Q.numIters ((L.ctaidOf (g / L.block)).get .z)
            ((L.ctaidOf (g / L.block)).get .x))).m = (Mv : EReal) := hM
        rw [kp 1914 (by simp [Lib.exR]), r3.2, jm.1, this, erealValue_coe]
      · rw [Lib.SoftRow.kState_eq, ← (Lib.SoftRow.kSt_ml_d Q _ _ _ _ 0 d _).1, hM]
        exact (EReal.toReal_coe Mv).symm
      · rw [kp 498 (by simp [Lib.exR]), r3.1, scaleW_eq hp]

/-- **The sum register at pc 2562 of a launch without a block**: the zero bits. -/
public theorem epi_empty_entry {m : Mem0} {X : Execution} (hp : Pre Q L m)
    (hX : Consistent L kernel Assumptions.all m X) (hf : Follow Q L X)
    (hn : Q.numIters ((L.ctaidOf (g / L.block)).get .z) ((L.ctaidOf (g / L.block)).get .x) = 0)
    {k : Nat} {t0 t : TState} {ev : Event}
    (hr : Run kernel Assumptions.all L g {} ((X.tr g).take k) (some t0))
    (ht : Lib.TauPath L g t0 t) (hpc : t.pc = 2562) (nxt : X.get (g, k) = some ev)
    (hev : ev.pc = 2565) (hu : ∀ f, ev.kind ≠ .ub f) :
    t.regs 1915 = some (b32 0) := by
  have hg := Frame.lt_of_get hX nxt
  cases k with
  | zero =>
    rw [List.take_zero] at hr
    cases hr
    have := Lib.back_in Lib.ex_bwd ht (by rw [hpc]; decide)
    simp [Lib.ex_zero] at this
  | succ k' =>
    have hlen : k' + 1 < (X.tr g).length := (List.getElem?_eq_some_iff.mp nxt).1
    have hk' : k' < (X.tr g).length := by omega
    obtain ⟨e, he⟩ : ∃ e, X.get (g, k') = some e := ⟨_, List.getElem?_eq_getElem hk'⟩
    obtain ⟨u, s, hu', hus, hes⟩ := Lib.pre_idx he hr
    have hue : ∀ f, e.kind ≠ .ub f := Frame.noUbBefore_of_get hX nxt k' (by omega) e he
    have pcs : e.pc = s.pc := EventFrame.estep_source_pc hes
    obtain ⟨lo, hi⟩ := Lib.exit_range hes ht hpc
    obtain ⟨w, ent, d, n, hsc, hs, inv, atpc, lim, d', hd, hx⟩ :=
      last_site_gen hp hX hf he nxt hev hu hue (pcs ▸ lo) (pcs ▸ hi)
    have hg' := Frame.lt_of_get hX he
    obtain ⟨sv, hsv, hshape⟩ := value_state hsc
    obtain ⟨y, hy, rfl⟩ := softD_shape hshape
    have hat := at_pre hp hg' hu' hus hes hsv hue
    change (Data.codeS ent L g).AtD y s at hat
    have hsite : y.c.site = .bar0 ∨ y.c.site = .pre 63 := by
      rw [hy]
      rcases hs with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · omega
    obtain ⟨ins, hci, -, hfire⟩ := EventFrame.estep_event_source hes
    have hpcd : (Data.codeS ent L g).pc y = s.pc := hat.1.symm
    have step : (Data.codeS ent L g).next y e = some (some ⟨d', Data.record L y e d'.site⟩) := by
      show Data.succ ent L g y e = _
      unfold Data.succ
      rw [hy, hd]
      rfl
    have DS : PTX.Flow.Code.DataStep (Data.codeS ent L g) Data.lEmptyF y := by
      rcases hsite with h | h
      · exact Data.l_bar0_empty h
      · exact Data.l_pre63_empty h
    have hres := DS ins hat (by rw [← hy] at inv; exact inv) (by rw [hpcd]; exact hci)
      (by rw [hpcd]; exact hfire) step
    obtain ⟨s', o, hts, hes'⟩ := Lib.next_state hX hg hr nxt
    have hs'pc : s'.pc = 2565 := by rw [← EventFrame.estep_source_pc hes']; exact hev
    have hreg : Holds s'.regs (Data.lEmptyF ⟨d', Data.record L y e d'.site⟩) := by
      rcases hres with h | hd'
      · exact h s' hts (stops_of_estep hes')
      · obtain ⟨f, hf'⟩ := hd'.all hts (stops_of_estep hes')
        obtain ⟨m', ho, hfm⟩ := hes'
        obtain rfl := Out.ev.inj (ho.symm.trans hf')
        exact absurd (congrArg Event.kind hfm.1) (hu f)
    have hzero : s'.regs 1915 = some (b32 0) :=
      holds_mem hreg (r := 1915) (v := b32 0) (by simp [Data.lEmptyF, hx])
    have hts' : Relation.ReflTransGen (Tau kernel Assumptions.all L g) t s' := by
      rcases rtg_tau_total ht hts with h | h
      · exact h
      · rcases Relation.ReflTransGen.cases_head h with rfl | ⟨_, hTau, _⟩
        · rw [hpc] at hs'pc
        · exact (not_tau_of_stops (stops_of_estep hes') hTau).elim
    rw [← Lib.em_keep hts' hpc]
    exact hzero

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
