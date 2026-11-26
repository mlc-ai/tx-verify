-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MemRows.Wg0
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0BarCnt
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Pred
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowStep
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Measure
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Class
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Objs
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.RefCount
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Lane
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
public import Lemmas.Protocol.UnitHandoff
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.OutSeq

@[expose] public section

/-! # The place of warpgroup 0's machine along a lane's trace

The step of a state of warpgroup 0 is the machine's successor (`wg0_fwd`), the place grows along the
lane (`place_mono`) and strictly at an event that counts (`place_lt`): two events of one lane at
one site and element are one event. Role-internal; the exports of `Wg0/Export/` use it. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.MbarRing MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {y : Nat}

/-- **The step of a state of warpgroup 0**: the state after an event is the machine's successor. -/
theorem wg0_fwd {t : Nat} {e : Event} {d : Wg0.Control.D} {n : Cls → Nat}
    (he : (X.tr y)[t]? = some e)
    (hσ : Frame.stateAt (thread P L) X y t = some (some (.inr ⟨.inl .wg0, d⟩, n)))
    {σ' : (thread P L y).D} (hσ' : Frame.stateAt (thread P L) X y (t + 1) = some (some σ')) :
    ∃ d1 n1, σ' = (.inr ⟨.inl .wg0, d1⟩, n1) ∧
      Wg0.Control.succ P L y (warpW L y) d e = some (some d1) := by
  rw [Frame.stateAt_succ he, hσ] at hσ'
  change (thread P L y).next (.inr ⟨.inl .wg0, d⟩, n) e = _ at hσ'
  rw [next_frag] at hσ'
  rcases hS : (frag P L y .wg0).next d e with _ | _ | d1 <;> rw [hS] at hσ' <;>
    simp only [Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq] at hσ'
  exact ⟨d1, _, hσ'.symm, hS⟩

/-- A state of warpgroup 0 at a prefix is not `none` before a later live state. -/
theorem live_le (hFw : Follow P L X) (hy : y < L.threads) {a b : Nat} (hab : a ≤ b)
    {σ : (thread P L y).D}
    (hσ : Frame.stateAt (thread P L) X y b = some (some σ)) :
    ∃ σ', Frame.stateAt (thread P L) X y a = some (some σ') := by
  have h1 := (follow_iff.mp hFw y hy a).1
  rcases hs : Frame.stateAt (thread P L) X y a with _ | _ | σ'
  · rw [Frame.stateAt_none_mono hs hab] at hσ
    cases hσ
  · exact absurd hs h1
  · exact ⟨σ', rfl⟩

/-- The reference invariant of a state of warpgroup 0 at the prefix's counts. -/
theorem refcore_at (hFw : Follow P L X) (hw : warp L y < 4)
    (hy : y < L.threads) {t : Nat} (hal : LaneUbFree X y t) {d : Wg0.Control.D} {n : Cls → Nat}
    (hσ : Frame.stateAt (thread P L) X y t = some (some (.inr ⟨.inl .wg0, d⟩, n))) :
    Wg0.RefCore L y d (fun c => ((X.tr y).take t).countP (Wg0.cls c)) := by
  rcases w0_bst_pre hFw hal hw hy hσ with ⟨d0, n0, h0, -⟩ | ⟨d0, n0, h0, hC, -⟩
  · simp at h0
  · simp only [Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h0
    obtain ⟨rfl, -⟩ := h0
    exact hC

/-- **The place grows along the lane**: between two states of warpgroup 0. -/
theorem place_mono (hFw : Follow P L X) (hw : warp L y < 4)
    (hy : y < L.threads) : ∀ (k t : Nat), LaneUbFree X y (t + k) →
    ∀ {d : Wg0.Control.D} {n : Cls → Nat},
    Frame.stateAt (thread P L) X y t = some (some (.inr ⟨.inl .wg0, d⟩, n)) →
    ∀ {d' : Wg0.Control.D} {n' : Cls → Nat},
    Frame.stateAt (thread P L) X y (t + k) = some (some (.inr ⟨.inl .wg0, d'⟩, n')) →
    Wg0.place d ≤ Wg0.place d'
  | 0, t, _, d, n, hσ, d', n', hσ' => by
    rw [Nat.add_zero, hσ] at hσ'
    simp only [Option.some.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and,
      Prod.mk.injEq] at hσ'
    obtain ⟨rfl, -⟩ := hσ'
    exact Nat.le_refl _
  | k + 1, t, hal, d, n, hσ, d', n', hσ' => by
    by_cases hl : t < (X.tr y).length
    · obtain ⟨e, he⟩ : ∃ e, (X.tr y)[t]? = some e := ⟨_, List.getElem?_eq_getElem hl⟩
      obtain ⟨σ1, hσ1⟩ := live_le hFw hy (a := t + 1) (b := t + (k + 1)) (by omega) hσ'
      obtain ⟨d1, n1, rfl, hS⟩ := wg0_fwd he hσ hσ1
      have hC := refcore_at hFw hw hy (hal.mono (by omega)) hσ
      have h1 : Wg0.place d ≤ Wg0.place d1 := by
        rcases Wg0.place_next hC hS with ⟨rfl, -⟩ | h
        · exact Nat.le_refl _
        · exact h.le
      have h2 := place_mono hFw hw hy k (t + 1) (by rwa [show t + 1 + k = t + (k + 1) by omega])
        hσ1 (by rwa [show t + 1 + k = t + (k + 1) by omega])
      omega
    · rw [Frame.stateAt_of_le (by omega), ← Frame.stateAt_of_le (k := t) (by omega)] at hσ'
      rw [hσ] at hσ'
      simp only [Option.some.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and,
        Prod.mk.injEq] at hσ'
      obtain ⟨rfl, -⟩ := hσ'
      exact Nat.le_refl _

/-- **The place grows strictly at an event that counts.** -/
theorem place_lt (hFw : Follow P L X) (hw : warp L y < 4)
    (hy : y < L.threads) {i i' : Nat} (hal : LaneUbFree X y i') {e : Event}
    (he : X.get (y, i) = some e)
    (hc : e.counts = true) (hii : i < i') {d d' : Wg0.Control.D} {n n' : Cls → Nat}
    (hσ : Frame.stateAt (thread P L) X y i = some (some (.inr ⟨.inl .wg0, d⟩, n)))
    (hσ' : Frame.stateAt (thread P L) X y i' = some (some (.inr ⟨.inl .wg0, d'⟩, n'))) :
    Wg0.place d < Wg0.place d' := by
  obtain ⟨σ1, hσ1⟩ := live_le hFw hy (a := i + 1) (b := i') (by omega) hσ'
  obtain ⟨d1, n1, rfl, hS⟩ := wg0_fwd he hσ hσ1
  have hC := refcore_at hFw hw hy (hal.mono (by omega)) hσ
  have h1 : Wg0.place d < Wg0.place d1 := by
    rcases Wg0.place_next hC hS with ⟨-, h⟩ | h
    · rw [hc] at h
      cases h
    · exact h
  have h2 := place_mono hFw hw hy (i' - (i + 1)) (i + 1)
    (by rwa [show i + 1 + (i' - (i + 1)) = i' by omega]) hσ1
    (by rwa [show i + 1 + (i' - (i + 1)) = i' by omega])
  omega

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
