-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Iface.BaseRead
public import Lemmas.Flow.TypedG
public import Lemmas.Flow.TauStar
public import Kernels.InklingRelDecode.Proof.Iface.EntryEnv
import Kernels.InklingRelDecode.Proof.Prologue.Export.NoUbLane
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

/-! # A data lane's event from 574 on has an event at 573 before it

Without an event at 573 before the event, the states of the lane up to it are the startup's and
the prologue's (the strict window of `noUb_no573`, the clean event by `strictQ_fromInit`), whose
pcs are below 574. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
open PTX PTX.Flow PTX.Flow.TyG PTX.Proof Strict

noncomputable section

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

private theorem site_lt (s : Site) (h : s ≠ .exit) : s.pc < 574 := by
  revert h
  cases s <;> try (intro h; exact absurd rfl h)
  all_goals (repeat' (rename_i j; revert j))
  all_goals decide +kernel

/-- **The first event of a data lane at 574 or above is preceded by an event at 573.** -/
theorem soft_start (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (base : Iface.BaseRead L X) {k : Nat} {e : Event}
    (hlane : g % L.block < 128) (he : X.get (g, k) = some e) (hpc : 574 ≤ e.pc)
    (nu : Frame.NoUbBefore X g k) : ∃ j < k, ∃ ej, X.get (g, j) = some ej ∧ ej.pc = 573 := by
  by_contra hcon
  have hno : ∀ j, j < k → ∀ ej, X.get (g, j) = some ej → ej.pc ≠ 573 :=
    fun j hj ej hej h => hcon ⟨j, hj, ej, hej, h⟩
  have hg := Frame.lt_of_get hX he
  obtain ⟨pc, kd⟩ := e
  dsimp only at hpc
  by_cases hub : ∃ f, kd = .ub f
  · obtain ⟨f, rfl⟩ := hub
    exact noUb_no573 hp hX hf base he hlane hno
  have clean : ∀ f, kd ≠ .ub f := fun f h => hub ⟨f, h⟩
  have hC : ∀ g < L.threads, (threadD Q L g).SoundU := fun g hg => threadD_sound hp hg
  obtain ⟨o, hrun⟩ := hX.thr g hg
  obtain ⟨dn, hdn, -⟩ := Frame.good_stateU (C := threadD Q L)
    (J := fun g σ => guardedTable Q L g (eraseThread Q L g σ)) hC hX he
    (fun pc' f h => clean f (congrArg Event.kind h)) (followedD hf hg k)
  have pos := Frame.event_pcU hC hX he hdn clean
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [Frame.stateAt_zero] at hdn
    obtain rfl := Option.some.inj (Option.some.inj hdn)
    rw [init_eq] at pos
    revert pos
    unfold Startup.init
    split <;> intro h <;> (have : pc < 27 := by
                             change pc = _ at h
                             rw [h]
                             first | (change Startup.Site.alloc.pc < 27; decide) |
                               (change Startup.Site.bar0.pc < 27; decide)
                           omega)
  obtain ⟨m', rfl⟩ : ∃ m', k = m' + 1 := ⟨k - 1, by omega⟩
  have hdn' := Frame.stateAt_window (Frame.stateAt_zero) (by rw [Nat.zero_add]; exact hdn)
  simp only [List.drop_zero] at hdn'
  have hW : ∀ e' ∈ (X.tr g).take (m' + 1), WfG Q L g e' := by
    intro e' hm
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
    rw [List.getElem?_take] at hi
    split_ifs at hi with hi'
    exact wfg_event hp hX hf base hg hi (fun f => nu i (by omega) e' hi f)
      (hno i (by omega) e' hi)
  obtain ⟨hok, t0', t1', o', hr', hs', hgd, hq, hes'⟩ := Code.strictQ_fromInit
    (C := threadD Q L g) (hC g hg) (fun d e hd => win_step hp hg hlane d e hd)
    (fun d e d' hk hw hpc' hn => okG_next hp hlane hk hw hpc' hn) hrun win_init win_q0
    (n := m' + 1) (Nat.succ_pos _) hW hdn' (e' := ⟨pc, kd⟩) he
  rcases hok with ⟨s, n, rfl, -⟩ | ⟨d', n, rfl, -⟩
  · have hx : Startup.enterOf s = none := Code.gatedExit_none.mp hgd.2.2
    have hlt : s.site.pc < 27 := by
      obtain ⟨site, tm, x, w⟩ := s
      cases site <;> first | (simp [Startup.enterOf] at hx; done) | (dsimp only; decide)
    change pc = s.site.pc at pos
    omega
  · have hs : d'.c.site ≠ .exit := by
      intro h
      have := hgd.2.2
      simp [dataExit, prologueErase, h] at this
    have := site_lt _ hs
    change pc = d'.c.site.pc at pos
    omega

end
end PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
