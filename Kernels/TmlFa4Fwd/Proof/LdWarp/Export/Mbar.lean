-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.Export
import Kernels.TmlFa4Fwd.Proof.Common.Frame
import Kernels.TmlFa4Fwd.Proof.LdWarp.Open
import Kernels.TmlFa4Fwd.Proof.Loader.Facts.QAcq
import Kernels.TmlFa4Fwd.Proof.Loader.Export.MbarSite
import Kernels.TmlFa4Fwd.Proof.Startup.Export.MbarSite
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader warps' mbarrier uses

`ld_mbar_use`: every event of a lane of warp 14 or 15 that names an mbarrier and is no
initialization is a poll of an empty barrier (Q 16, 24; K/V 56 to 72; bias 336, 344), the arrival
of a packet's `cp.async`s on a K/V full barrier (32 to 48), or an expect-tx arrival on or a tensor
copy into a Q (0, 8) or bias (320, 328) full barrier. `ld_qe0_par`: the parity of a poll of the
first Q stage's empty barrier. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Frame (MbarOf)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {h k : Nat} {e : Event} {l : Loc}

/-- The empty barriers the loader polls. -/
def LdPollOff (o : Nat) : Prop :=
  o = 16 ∨ o = 24 ∨ o = 56 ∨ o = 64 ∨ o = 72 ∨ o = 336 ∨ o = 344
/-- The full barriers of the loader's tensor copies. -/
def LdTmaOff (o : Nat) : Prop := o = 0 ∨ o = 8 ∨ o = 320 ∨ o = 328

/-- The loader state an event is fired from, with its use. -/
private theorem ld_state (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L h = 14 ∨ Prologue.warpIndex L h = 15)
    (he : X.get (h, k) = some e) (hm : MbarOf e l) (hni : ∀ c, e.kind ≠ .mbInit l c) :
    ∃ b d n kk A, Frame.stateAt (thread p L) X h k = some (some (LdWarp.linj p L h b d n)) ∧
      n .ub = 0 ∧ LdUse p L h (Loader.wOf b) kk A d e l := by
  have hub : ∀ f, e.kind ≠ .ub f := by
    obtain ⟨pc, kd⟩ := e
    rintro f rfl
    simp only [MbarOf] at hm
  rcases LdWarp.open_ev hp hX hFw hw he hub with ⟨s, n, -, -, -, hi, hev⟩ |
    ⟨b, d, n, hσ, h0, hR, -, hev⟩
  · exact absurd (start_mbar hev hi.2 hm) (fun ⟨c, hc⟩ => hni c hc)
  have hJl := (hR.2 h0).1
  rw [← hR.1] at hJl
  obtain ⟨kk, A, hRing, -⟩ := hJl.refE
  exact ⟨b, d, n, kk, A, hσ, h0, ld_use hp hRing hev hm⟩

/-- **Every mbarrier use of a loader lane.** -/
theorem ld_mbar_use (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L h = 14 ∨ Prologue.warpIndex L h = 15)
    (he : X.get (h, k) = some e) (hm : MbarOf e l) (hni : ∀ c, e.kind ≠ .mbInit l c) :
    (∃ o par ok, LdPollOff o ∧ l = obj L h o ∧ e.kind = .wait l par ok true .cta) ∨
      (∃ o, (o = 32 ∨ o = 40 ∨ o = 48) ∧ l = obj L h o ∧ e.kind = .asyncArrive l true) ∨
      (∃ o tx, LdTmaOff o ∧ l = obj L h o ∧ e.kind = .arrive l tx 1 true .cta) ∨
      ∃ o a s, LdTmaOff o ∧ l = obj L h o ∧ e.kind = .tensorIssue a s ∧ s.mbar = l := by
  have h3 : ∀ j, LdPollOff (56 + 8 * (j % 3)) := fun j => by unfold LdPollOff; omega
  obtain ⟨b, d, n, kk, A, -, -, hu⟩ := ld_state hp hX hFw hw he hm hni
  cases hu with
  | slot per vv ok _ hl hk => exact .inl ⟨_, _, ok, h3 _, hl, hk⟩
  | dw j ok _ hl hk => exact .inl ⟨_, _, ok, h3 _, hl, hk⟩
  | dq ok _ hl hk => exact .inl ⟨_, _, ok, by simp [LdPollOff], hl, hk⟩
  | tw t ok _ hl hk =>
    exact .inl ⟨_, _, ok, by have := twOff_mem t; unfold LdPollOff; omega, hl, hk⟩
  | arrive per vv _ hl hk => exact .inr (.inl ⟨_, by omega, hl, hk⟩)
  | ta t tx _ hl hk =>
    exact .inr (.inr (.inl ⟨_, tx, taOff_mem t, hl, hk⟩))
  | da tx _ hl hk => exact .inr (.inr (.inl ⟨_, tx, by simp [LdTmaOff], hl, hk⟩))
  | tc t c a s _ hl hk hb => exact .inr (.inr (.inr ⟨_, a, s, taOff_mem t, hl, hk, hb⟩))

/-- **A successful poll of Q stage 0's empty barrier by a loader lane** has the parity of the lane's
successful polls of it plus one: it is the wait of TMA group 0, whose parity word is 1, before which
the lane has polled the barrier successfully no time. -/
theorem ld_qe0_poll (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : Prologue.warpIndex L h = 14 ∨ Prologue.warpIndex L h = 15)
    {pc par : Nat} {ok acq : Bool} {sc : MbarScope}
    (he : X.get (h, k) = some ⟨pc, .wait (obj L h 16) par ok acq sc⟩) :
    par % 2 = (okPolls (obj L h 16) ((X.tr h).take k) + 1) % 2 := by
  obtain ⟨b, d, n, kk, A, hσ, hub, hu⟩ := ld_state hp hX hFw hw he (l := obj L h 16) rfl
    (fun _ h => by cases h)
  cases hu with
  | slot _ _ _ _ hl _ | dw _ _ _ hl _ | dq _ _ hl _ => have := (obj_off hl).2; omega
  | arrive _ _ _ _ hk | ta _ _ _ _ hk | da _ _ _ hk | tc _ _ _ _ _ _ hk _ => cases hk
  | tw t ok hs hl hk =>
    have h1 := (obj_off hl).2
    have ht : t = 0 := by rcases twOff_mem t with h' | h' | h' | h' <;> omega
    subst ht
    simp only [Kind.wait.injEq] at hk
    obtain ⟨-, hpar, -, -, -⟩ := hk
    obtain ⟨site, v, k'⟩ := d
    simp only at hs
    subst hs
    have hq := Loader.q_acq hp hX (Frame.lt_of_get hX he) hw hσ hub 16 (by simp)
    rw [show okPolls (obj L h 16) ((X.tr h).take k) = n (.load (.acquire (obj L h 16)))
      from count hσ (.load (.acquire (obj L h 16))),
      show n (.load (.acquire (obj L h 16))) = _ from hq, hpar]
    simp only [Loader.qAcq]
    split_ifs <;> first | rfl | omega

end
end PTX.Kernels.TmlFa4Fwd.Proof
