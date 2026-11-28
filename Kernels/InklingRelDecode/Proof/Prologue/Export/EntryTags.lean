-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Iface.BaseRead
public import Lemmas.Flow.TypedG
public import Lemmas.Flow.TauStar
public import Kernels.InklingRelDecode.Proof.Iface.EntryEnv
import Kernels.InklingRelDecode.Proof.Prologue.Export.NoUbWfG
import Kernels.InklingRelDecode.Proof.Prologue.Export.NoUbWf
import Kernels.InklingRelDecode.Proof.Prologue.Strict.OkNext
import Kernels.InklingRelDecode.Proof.Lib.RegionTop
import Kernels.InklingRelDecode.Proof.Prologue.Strict.Window
import Kernels.InklingRelDecode.Proof.Prologue.Strict.WinSteps
import Kernels.InklingRelDecode.Proof.Prologue.Strict.Entry
import Kernels.InklingRelDecode.Proof.Prologue.Strict.QTail
import Kernels.InklingRelDecode.Proof.Common.ValueSound
import Kernels.InklingRelDecode.Proof.Common.ValueFollow
import Kernels.InklingRelDecode.Proof.Common.Sound
import Kernels.InklingRelDecode.Proof.Common.StartupEvents
import Lemmas.Flow.StepForQRun
import Lemmas.Flow.ReachFrame
import Lemmas.Flow.Determinism
import Lemmas.Flow.BarSyncNone
import Kernels.InklingRelDecode.Flow.Code.Part008
import Lemmas.Kernel.NoUbStrictQLane
import Lemmas.Kernel.FrameU
import Lemmas.Execution.EventFrameSource

@[expose] public section

/-! # The tags the softmax entry takes over from the prologue

A lane that has run its prologue strictly, without undefined behaviour, and then fires the barrier
before the softmax (pc 573), is at program counter 574 in a state whose registers have the tags
the softmax's typed windows start from (`Strict.entryEnv`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
open PTX PTX.Flow PTX.Flow.TyG PTX.Proof Strict

noncomputable section

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

private theorem not_573 (hX : Consistent L kernel Assumptions.all m X) (hg : g < L.threads)
    {i j : Nat} {ei ej : Event} (hij : i < j) (hei : X.get (g, i) = some ei)
    (hej : X.get (g, j) = some ej) (h : ej.pc = 573) : ei.pc ≠ 573 := by
  intro h573
  obtain ⟨o, hr⟩ := hX.thr g hg
  have := Run.pc_ge_later (Lib.loClosed (L := L)) hr hij hei (by omega) hej
  omega

private theorem site_573 (s : Site) (h : s.pc = 573) : s = .bar18 := by
  revert h
  cases s <;> try (intro _; rfl)
  all_goals (repeat' (rename_i j; revert j))
  all_goals decide +kernel

/-- **The registers of the softmax's entry are typed** in the state after the barrier before the
softmax (which is at 574 and without a fault): the lane's prefix up to and including that
barrier has no undefined behaviour. -/
theorem entry_tags (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (base : Iface.BaseRead L X) {j : Nat} {e : Event}
    (hlane : g % L.block < 128) (he : X.get (g, j) = some e) (h573 : e.pc = 573)
    (nu : Frame.NoUbBefore X g (j + 1)) {t0 t1 u : TState}
    (hr : Run kernel Assumptions.all L g {} ((X.tr g).take j) (some t0))
    (hs : TauStar kernel Assumptions.all L g t0 t1)
    (hes : EStep kernel Assumptions.all L g t1 e (some u)) :
    u.pc = 574 ∧ u.fault = none ∧ TypedF Iface.entryEnv u := by
  have hg := Frame.lt_of_get hX he
  have clean : ∀ f, e.kind ≠ .ub f := fun f => nu j (by omega) e he f
  obtain ⟨o, hrun⟩ := hX.thr g hg
  have hC : ∀ g < L.threads, (threadD Q L g).SoundU := fun g hg => threadD_sound hp hg
  obtain ⟨dn, hdn, -⟩ := Frame.good_stateU (C := threadD Q L)
    (J := fun g σ => guardedTable Q L g (eraseThread Q L g σ)) hC hX he
    (fun pc f h => clean f (congrArg Event.kind h)) (followedD hf hg j)
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · exfalso
    have pos := Frame.event_pcU hC hX he hdn clean
    rw [Frame.stateAt_zero] at hdn
    obtain rfl := Option.some.inj (Option.some.inj hdn)
    rw [init_eq, h573] at pos
    revert pos
    unfold Startup.init
    split <;> intro h <;> cases h
  obtain ⟨m', rfl⟩ : ∃ m', j = m' + 1 := ⟨j - 1, by omega⟩
  have hdn' := Frame.stateAt_window (Frame.stateAt_zero) (by rw [Nat.zero_add]; exact hdn)
  simp only [List.drop_zero] at hdn'
  have hW : ∀ e' ∈ (X.tr g).take (m' + 1), WfG Q L g e' := by
    intro e' hm
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
    rw [List.getElem?_take] at hi
    split_ifs at hi with hi'
    exact wfg_event hp hX hf base hg hi (fun f => nu i (by omega) e' hi f)
      (not_573 hX hg (by omega) hi he h573)
  obtain ⟨hok, t0', t1', o', hr', hs', hgd, hq, hes'⟩ := Code.strictQ_fromInit
    (C := threadD Q L g) (hC g hg) (fun d e hd => win_step hp hg hlane d e hd)
    (fun d e d' hk hw hpc' hn => okG_next hp hlane hk hw hpc' hn) hrun win_init win_q0
    (n := m' + 1) (Nat.succ_pos _) hW hdn' (e' := e) he
  obtain rfl := Option.some.inj (Run.det hr' hr)
  obtain rfl := stop_unique hs' hs (stops_of_estep hes') (stops_of_estep hes)
  have ho : o' = some u := estep_det hes' hes
  subst ho
  have pos : e.pc = (threadD Q L g).pc dn := by
    have h1 := EventFrame.estep_source_pc hes
    rw [h1]
    exact hgd.1.1
  rcases hok with ⟨s, n, rfl, -⟩ | ⟨d', n, rfl, hok'⟩
  · exfalso
    have hx : Startup.enterOf s = none := Code.gatedExit_none.mp hgd.2.2
    have hlt : s.site.pc < 27 := by
      obtain ⟨site, tm, x, w⟩ := s
      cases site <;> first | (simp [Startup.enterOf] at hx; done) | (dsimp only; decide)
    change e.pc = s.site.pc at pos
    omega
  · have hsite : d'.c.site = .bar18 := site_573 d'.c.site (by
      change e.pc = d'.c.site.pc at pos
      omega)
    have hw := wf_event hp hX hf hg he clean
    obtain ⟨ins, hc, hfire⟩ := Code.fired_of_good (hC g hg) hgd hes'
    have hstep := @step_bar18 Q L g (b32 0) d' hsite e t1' u
    rcases hstep ins hgd.1 hgd.2.1 hc hq hw hfire with ⟨d1, t', hn, hl, hg1, hq1⟩ | ⟨hn, -⟩
    · obtain ⟨⟨s0, a, b, c0, won, bc⟩, vs⟩ := d'
      change s0 = .bar18 at hsite
      subst hsite
      have hn' := hn
      simp only [Data.code, Data.succ, Control.next, Option.map_some, Option.some.injEq] at hn'
      subst hn'
      have hok1 := ok_next hok' hw (by change e.pc = Site.bar18.pc at pos; exact pos) hn
      have hpc574 : t'.pc = 574 := hg1.1.1
      have hty := entry_typed (w := b32 0) rfl hok1 rfl hg1.1 hq1 hpc574
      have hu574 : u.pc = 574 := by
        obtain ⟨ins2, hc2, -, hf2⟩ := EventFrame.estep_event_source hes
        have h1 : t1'.pc = 573 := by rw [← EventFrame.estep_source_pc hes]; exact h573
        rw [h1, Flow.code_573] at hc2
        obtain rfl := Option.some.inj hc2
        have := fires_barSync_next hf2
        rw [this]
        simp [PTX.next, h1]
      have hut : u = t' := by
        rcases Relation.ReflTransGen.cases_head hl with h | ⟨v, hv, -⟩
        · exact h
        · exact absurd hv (Flow.Code.no_tau_evAt (by rw [hu574]; decide +kernel))
      subst hut
      obtain ⟨-, -, -, hflt, -⟩ := hg1.1
      exact ⟨hu574, hflt, hty⟩
    · exfalso
      obtain ⟨⟨s0, a, b, c0, won, bc⟩, vs⟩ := d'
      change s0 = .bar18 at hsite
      subst hsite
      simp [Data.code, Data.succ, Control.next] at hn

end
end PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
