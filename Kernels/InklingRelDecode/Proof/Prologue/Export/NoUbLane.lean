-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Common.Follow
public import Kernels.InklingRelDecode.Proof.Iface.BaseRead
import Kernels.InklingRelDecode.Proof.Prologue.Export.NoUbWfG
import Kernels.InklingRelDecode.Proof.Prologue.Strict.Window
import Kernels.InklingRelDecode.Proof.Prologue.Strict.WinSteps
import Kernels.InklingRelDecode.Proof.Prologue.Strict.Live
import Kernels.InklingRelDecode.Proof.Lib.RegionTop
import Kernels.InklingRelDecode.Proof.Common.ValueSound
import Kernels.InklingRelDecode.Proof.Common.ValueFollow
import Kernels.InklingRelDecode.Proof.Common.LaneNoUb
import Kernels.InklingRelDecode.Proof.Common.Sound
import Kernels.InklingRelDecode.Proof.Common.StartupEvents
import Kernels.InklingRelDecode.Proof.Common.Staged.Early
import Lemmas.Kernel.NoUbStrictQLane
import Lemmas.Kernel.FrameU

@[expose] public section

/-! # No undefined behaviour in the prologue of a data lane

A lane's first undefined-behaviour event at a pc below 574, in a lane that has an event at pc 27
or above, is not one. The window of the strict steps starts at the thread's first state: its
states are the startup's with the zero base word and the prologue's well-typed ones. No event
before it is at the barrier before the softmax, since after that barrier the lane never returns
below the softmax region (`Lib.loClosed`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
open PTX PTX.Flow PTX.Flow.Havoc PTX.Flow.Tagged PTX.Proof Control Strict

noncomputable section

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- No event of the window is at the barrier before the softmax. -/
private theorem not_573 (hX : Consistent L kernel Assumptions.all m X) (hg : g < L.threads)
    {j k : Nat} {ej : Event} {pc : Nat} {f : Fault} (hjk : j < k) (hej : X.get (g, j) = some ej)
    (he : X.get (g, k) = some ⟨pc, .ub f⟩) (hpc : pc < 574) : ej.pc ≠ 573 := by
  intro h573
  obtain ⟨o, hr⟩ := hX.thr g hg
  have := Run.pc_ge_later (Lib.loClosed (L := L)) hr hjk (e := ej) (e' := ⟨pc, .ub f⟩) hej
    (by omega) he
  change 574 ≤ pc at this
  omega

theorem noUb_window (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (base : Iface.BaseRead L X) {k pc : Nat} {f : Fault}
    (he : X.get (g, k) = some ⟨pc, .ub f⟩) (hk : 1 ≤ k) (hlane : g % L.block < 128)
    (hno : ∀ j, j < k → ∀ ej, X.get (g, j) = some ej → ej.pc ≠ 573) : False := by
  have hg := Frame.lt_of_get hX he
  have nu := Frame.noUbBefore_of_get hX he
  have hW : ∀ j, 0 ≤ j → j < 0 + (k - 1 + 1) → ∀ ej, X.get (g, j) = some ej →
      WfG Q L g ej := by
    intro j _ hj ej hej
    have hjk : j < k := by omega
    exact wfg_event hp hX hf base hg hej (fun f' => nu j hjk ej hej f') (hno j hjk ej hej)
  have he' : X.get (g, 0 + (k - 1 + 1)) = some ⟨pc, .ub f⟩ := by
    rw [show 0 + (k - 1 + 1) = k by omega]; exact he
  refine absurd rfl (Frame.noUb_strictQ_lane (C := threadD Q L)
    (J := fun g σ => guardedTable Q L g (eraseThread Q L g σ)) (Q := QT proQt)
    (Wf := WfG Q L g) (Ok := OkG Q L g) (fun g hg => threadD_sound hp hg) hX
    (followedD hf hg) ?_ ?_ (k0 := 0) (m := k - 1) Frame.stateAt_zero ?_ ?_ he' hW ?_ ?_ f)
  · exact fun d e hd => win_step hp hg hlane d e hd
  · intro d e d' hk hw hpc' hn
    exact okG_next hp hlane hk hw hpc' hn
  · exact win_init
  · exact win_q0
  · intro σ t ins _ hok _ hpc' hgd hq hc f'
    rcases hok with ⟨s, n, rfl, -⟩ | ⟨d', n, rfl, hk⟩
    · obtain ⟨hat, hinv⟩ := hgd
      have hx : Startup.enterOf s = none := Code.gatedExit_none.mp hinv.2
      exact Startup.safe_site (by rw [hp.block]) (Startup.sharedOk_of_pre hp) hat
        (fun r h => by simp [Startup.enterOf, h] at hx) hc f'
    · obtain ⟨hat, hinv⟩ := hgd
      have hs : d'.c.site ≠ .exit := by
        intro h
        have := hinv.2
        simp [dataExit, prologueErase, h] at this
      exact safe_pro hp hg hlane hat hk hs hc f'
  · intro i d v _ _ hok hv hd _ nui hn
    have hu : ∀ f, v.kind ≠ .ub f := fun f => nui i (by omega) v hv f
    obtain ⟨t, ins, o, hat, hi, hc, hfi⟩ := Frame.fired_siteU
      (fun g hg => threadD_sound hp hg) hX hv hd hu
    exfalso
    rcases hok with ⟨s, n, rfl, -⟩ | ⟨d', n, rfl, -⟩
    · have hx : Startup.enterOf s = none := Code.gatedExit_none.mp hi.2
      have ev := Startup.shape hp hat hi.1 hc hfi hu
      have hs : Startup.succ L g s v = none := by
        rcases h : Startup.succ L g s v with _ | _ | s'
        · rfl
        · simp [threadD, Code.roleThread, Code.counted, Code.glue, Startup.code, h] at hn
        · simp [threadD, Code.roleThread, Code.counted, Code.glue, Startup.code, h] at hn
      refine Startup.live_site (fun r h => by simp [Startup.enterOf, h] at hx) ev ?_ hs
      intro hl ac bs hvv hloc hsz
      subst hvv
      exact base hv hloc hsz
    · have hs : Data.succ Q L g d' v = none := by
        rcases h : Data.succ Q L g d' v with _ | _ | c
        · rfl
        · simp [threadD, Code.roleThread, Code.counted, Code.glue, Code.withStubs, fragD,
            dataDCode, prologueDCode, Data.code, h] at hn
        · simp [threadD, Code.roleThread, Code.counted, Code.glue, Code.withStubs, fragD,
            dataDCode, prologueDCode, Data.code, h] at hn
      exact live_pro hc hfi hu hs

/-- **A data lane's undefined-behaviour event has an event at 573 before it**: without one, the
lane's states up to it are the startup's and the prologue's, which are strict and safe. -/
theorem noUb_no573 (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (base : Iface.BaseRead L X) {k pc : Nat} {f : Fault}
    (he : X.get (g, k) = some ⟨pc, .ub f⟩) (hlane : g % L.block < 128)
    (hno : ∀ j, j < k → ∀ ej, X.get (g, j) = some ej → ej.pc ≠ 573) : False := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine absurd rfl (lane_noUb hp hX hf base (Frame.lt_of_get hX he) he
      (Rest := fun _ => False) (fun j d hj => absurd hj (Nat.not_lt_zero j)) ?_
      (fun _ _ _ h => h.elim) (fun _ _ _ h => h.elim) (fun _ _ _ h => h.elim) f)
    intro σ hσ _
    rw [Frame.stateAt_zero] at hσ
    obtain rfl := Option.some.inj (Option.some.inj hσ)
    refine Or.inl ⟨Startup.init L g, fun _ => 0, ?_⟩
    show (Code.enter (Startup.code Q L g) (Code.withStubs (frag Q L g) Startup.Entry.pc)
      (Code.gatedExit Startup.enterOf (sel L g)) (Startup.init L g), fun _ => (0 : Nat)) = _
    rw [enter_inl enterOf_init]
  · exact noUb_window hp hX hf base he hk hlane hno

/-- **No data lane has undefined behaviour at a pc of the prologue.** -/
theorem noUb_prologue (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    (hf : Follow Q L X) (base : Iface.BaseRead L X) {k pc : Nat} {f : Fault}
    (he : X.get (g, k) = some ⟨pc, .ub f⟩) (hlane : g % L.block < 128) (hpc : pc < 574) :
    False :=
  noUb_no573 hp hX hf base he hlane fun _ hj _ hej =>
    not_573 hX (Frame.lt_of_get hX he) hj hej he hpc

end
end PTX.Kernels.InklingRelDecode.Proof.Prologue.Export
