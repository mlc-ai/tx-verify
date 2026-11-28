-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0BarCnt
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowStep
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Control.Machine

@[expose] public section

/-! # The state before a state of warpgroup 0

A followed lane of warps 0-3 that is in warpgroup 0's machine at a position `t` came from a state
at the position before it, by the machine's step at that position's event (`wg0_pred`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 MbarRow

noncomputable section

variable {P : Params} {L : Launch} {X : Execution}

/-- **The predecessor of a state of warpgroup 0**: the state at the position before it, and the
machine's step at that position's event; or the machine's first state (`smr`), entered from the
startup. -/
theorem wg0_pred_pre (hFw : Follow P L X) {y : Nat} {t : Nat} (hal : LaneUbFree X y t)
    (hw : warp L y < 4) (hy : y < L.threads) (ht : t ≤ (X.tr y).length) {d : Wg0.Control.D}
    {n : Cls → Nat}
    (hσ : Frame.stateAt (thread P L) X y t = some (some (.inr ⟨.inl .wg0, d⟩, n))) :
    (∃ t', t = t' + 1 ∧ ∃ (d' : Wg0.Control.D) (n' : Cls → Nat) (e : Event),
      (X.tr y)[t']? = some e ∧
      Frame.stateAt (thread P L) X y t' = some (some (.inr ⟨.inl .wg0, d'⟩, n')) ∧
      Wg0.Control.succ P L y (warpW L y) d' e = some (some d)) ∨ d.site = .smr := by
  rcases t with _ | t
  · rw [Frame.stateAt_zero, thread_init] at hσ
    cases hσ
  obtain ⟨e, he⟩ : ∃ e, (X.tr y)[t]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  rw [Frame.stateAt_succ he] at hσ
  rcases hs : Frame.stateAt (thread P L) X y t with _ | _ | σ
  · rw [hs] at hσ; cases hσ
  · rw [hs] at hσ; simp [Code.toMachine] at hσ
  rw [hs] at hσ
  rcases w0_bst_pre hFw (hal.mono (by omega)) hw hy hs with ⟨dS, n0, rfl, -⟩ | ⟨d0, n0, rfl, -⟩
  · change (thread P L y).next (.inl dS, n0) e = _ at hσ
    rw [next_startup] at hσ
    rcases hS : Startup.succ L y dS e with _ | _ | d1 <;> rw [hS] at hσ <;>
      simp only [Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq] at hσ
    obtain ⟨hσ1, -⟩ := Prod.mk.inj hσ
    unfold Code.enter at hσ1
    split at hσ1
    · simp only [Sum.inr.injEq, Sigma.mk.inj_iff] at hσ1
      obtain ⟨rfl, h2⟩ := hσ1
      cases eq_of_heq h2
      exact .inr rfl
    · cases hσ1
  · change (thread P L y).next (.inr ⟨.inl .wg0, d0⟩, n0) e = _ at hσ
    rw [next_frag] at hσ
    rcases hS : (frag P L y .wg0).next d0 e with _ | _ | d1 <;> rw [hS] at hσ <;>
      simp only [Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq] at hσ
    obtain ⟨hσ1, -⟩ := Prod.mk.inj hσ
    simp only [Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hσ1
    subst hσ1
    exact .inl ⟨t, rfl, d0, n0, e, he, hs, hS⟩


theorem wg0_pred (hFw : Follow P L X) (hnu : NoUbWg0 L X) {y : Nat} (hw : warp L y < 4)
    (hy : y < L.threads) {t : Nat} (ht : t ≤ (X.tr y).length) {d : Wg0.Control.D}
    {n : Cls → Nat}
    (hσ : Frame.stateAt (thread P L) X y t = some (some (.inr ⟨.inl .wg0, d⟩, n))) :
    (∃ t', t = t' + 1 ∧ ∃ (d' : Wg0.Control.D) (n' : Cls → Nat) (e : Event),
      (X.tr y)[t']? = some e ∧
      Frame.stateAt (thread P L) X y t' = some (some (.inr ⟨.inl .wg0, d'⟩, n')) ∧
      Wg0.Control.succ P L y (warpW L y) d' e = some (some d)) ∨ d.site = .smr :=
  wg0_pred_pre hFw (LaneUbFree.of_noUbWg0 hnu hw t) hw hy ht hσ

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
