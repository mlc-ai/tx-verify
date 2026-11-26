-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Dequant
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowStep
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowView
public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Roles
public import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Ev
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.DequantLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Dequant.Objs
import Lemmas.Kernel.UbLast

@[expose] public section

/-! # The predecessor of a warpgroup-2 state

A warpgroup-2 state past the set-up follows a warpgroup-2 state on the event between
(`deq_pred`: the startup enters the role at its first site). Shared by the proofs that walk a
lane's states backwards (`Dequant/Export/Use.lean`, `Dequant/Export/QPoll.lean`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- **The state before a warpgroup-2 state past the set-up** is a warpgroup-2 state that steps to
it on the event between. -/
theorem deq_pred (hFw : Follow P L X) (hg : g < L.threads) {i : Nat} {f : Event}
    {d : Dequant.Control.D} {n : Cls → Nat} (hf : X.get (g, i) = some f)
    (hs1 : Frame.stateAt (thread P L) X g (i + 1) = some (some (.inr ⟨.inl .dequant, d⟩, n)))
    (hsite : d.site ≠ .smr) :
    ∃ d' n', Frame.stateAt (thread P L) X g i = some (some (.inr ⟨.inl .dequant, d'⟩, n')) ∧
      Dequant.Control.succ P L g d' f = some (some d) := by
  rw [Frame.stateAt_succ hf] at hs1
  rcases hs : Frame.stateAt (thread P L) X g i with _ | _ | ⟨q, n'⟩
  · rw [hs] at hs1; cases hs1
  · rw [hs] at hs1; cases hs1
  · rw [hs] at hs1
    change (thread P L g).next (q, n') f = _ at hs1
    rcases q with b | ⟨e | r, d'⟩
    · rw [next_startup] at hs1
      obtain ⟨x, -, hx⟩ := Option.map_eq_some_iff.mp hs1
      obtain ⟨y, -, hy⟩ := Option.map_eq_some_iff.mp hx
      simp only [Prod.mk.injEq] at hy
      obtain ⟨hy, -⟩ := hy
      unfold Code.enter at hy
      split at hy
      · simp only [Sum.inr.injEq, Sigma.mk.inj_iff] at hy
        obtain ⟨rfl, hy⟩ := hy
        cases eq_of_heq hy
        exact absurd rfl hsite
      · cases hy
    · rw [next_frag] at hs1
      obtain ⟨x, hx1, hx⟩ := Option.map_eq_some_iff.mp hs1
      obtain ⟨y, rfl, hy⟩ := Option.map_eq_some_iff.mp hx
      simp only [Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, Sum.inl.injEq] at hy
      obtain ⟨⟨rfl, hy⟩, -⟩ := hy
      cases eq_of_heq hy
      exact ⟨d', n', rfl, hx1⟩
    · exact ((follow_iff.mp hFw g hg i).2 _ hs).elim

/-- A state of a later index is not the first one. -/
theorem deq_pred_index {i : Nat} {d : Dequant.Control.D} {n : Cls → Nat}
    (hs : Frame.stateAt (thread P L) X g i = some (some (.inr ⟨.inl .dequant, d⟩, n))) :
    ∃ i', i = i' + 1 := by
  cases i with
  | zero => rw [Frame.stateAt_zero, thread_init] at hs; cases hs
  | succ i' => exact ⟨i', rfl⟩

/-- An earlier event of a lane with an event at `k`, which is not undefined behaviour. -/
theorem deq_earlier_ev (hX : Consistent L kernel Assumptions.all m X) {i k : Nat} {e : Event}
    (he : X.get (g, k) = some e) (hik : i < k) :
    ∃ f, X.get (g, i) = some f ∧ ∀ fl, f.kind ≠ .ub fl := by
  have hk := len_of_get he
  refine ⟨(X.tr g)[i]'(by simp only at hk; omega), List.getElem?_eq_getElem _, fun fl h => ?_⟩
  have hf : X.get (g, i) = some ⟨((X.tr g)[i]'(by simp only at hk; omega)).pc, .ub fl⟩ := by
    rw [← h]
    exact List.getElem?_eq_getElem _
  have := ub_last hX hf he
  omega

/-- The warpgroup-2 state at an event fires it. -/
theorem deq_ev (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {i : Nat} {f : Event} {d : Dequant.Control.D} {n : Cls → Nat}
    (hf : X.get (g, i) = some f) (hub : ∀ fl, f.kind ≠ .ub fl)
    (hs : Frame.stateAt (thread P L) X g i = some (some (.inr ⟨.inl .dequant, d⟩, n))) :
    Dequant.Ev L g d f := by
  obtain ⟨σ, hσ, -, -, hev, -⟩ := ev_at hp hX hFw hf hub
  rw [hs] at hσ
  cases hσ
  exact hev

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
