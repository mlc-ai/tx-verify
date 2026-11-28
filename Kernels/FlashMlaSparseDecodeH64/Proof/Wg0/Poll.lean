-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Ev

@[expose] public section

/-! # Warpgroup 0's polls by state

A state's event is a poll only at the three wait sites (`evK_wait_site`: `wv`, `wq`, `wsv`), two
polls of one state name the same object with the same parity (`evK_wait_det`), and only the exit
site fires the exit (`evK_exit`): the progress rows of the role (`Common/Export.lean`) read the
blocker of a waiting lane from its next event. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
open PTX PTX.Proof PTX.Flow Control

noncomputable section

variable {P : Params} {L : Launch} {g : Nat} {w : BitVec 64}

/-- **A poll is fired only at a wait site.** -/
theorem evK_wait_site {d : D} {e : Event} {l : Loc} {q : Nat} {ok a : Bool} {sc : MbarScope}
    (h : EvK P L g w d e) (hk : e.kind = .wait l q ok a sc) :
    d.site = .wv ∨ d.site = .wq ∨ d.site = .wsv := by
  obtain ⟨site, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  obtain ⟨pc, kd⟩ := e
  simp only at hk
  subst hk
  cases site <;> simp [EvK, PollEv, ArrEv, GWrAt, RdAt, WrAt, GenWrAt, NcEv, TcLdEv, TcStEv] at h ⊢

/-- **Two polls of one state name one object with one parity.** -/
theorem evK_wait_det {d : D} {e e' : Event} {l l' : Loc} {q q' : Nat} {ok ok' a a' : Bool}
    {sc sc' : MbarScope} (h : EvK P L g w d e) (h' : EvK P L g w d e')
    (hk : e.kind = .wait l q ok a sc) (hk' : e'.kind = .wait l' q' ok' a' sc') :
    l' = l ∧ q' = q := by
  have hs := evK_wait_site h hk
  obtain ⟨site, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  obtain ⟨pc, kd⟩ := e
  obtain ⟨pc', kd'⟩ := e'
  simp only at hk hk' hs
  subst hk hk'
  rcases hs with rfl | rfl | rfl <;> simp [EvK, PollEv] at h h' ⊢ <;>
    exact ⟨h'.1.trans h.1.symm, h'.2.1.trans h.2.1.symm⟩

/-- **Only the exit site fires the exit.** -/
theorem evK_exit {d : D} {e : Event} (h : EvK P L g w d e) (hk : e.kind = .exit) :
    d.site = .exit := by
  obtain ⟨site, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  obtain ⟨pc, kd⟩ := e
  simp only at hk
  subst hk
  cases site <;> simp [EvK, PollEv, ArrEv, GWrAt, RdAt, WrAt, GenWrAt, NcEv, TcLdEv, TcStEv] at h ⊢

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0
