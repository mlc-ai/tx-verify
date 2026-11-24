-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.Protocol.Sync
public import Lemmas.Protocol.CountNth
public import Kernels.RmsNorm.Proof.NoBarArrive

@[expose] public section

/-! # The order the barriers give

An event of a thread before its `n`-th arrival on a barrier happens before an event of a thread
of its CTA after that thread's `n`-th arrival (`bar_order`). With the counts of the states, an
event happens before an event of its CTA whose state has passed more arrivals on barrier `0` or
`1` (`baseCausality_of_counts`); two events of one thread are in program order (`po_baseCausality`).
-/

namespace PTX.Kernels.RmsNorm.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealArith, Assumptions.exactApprox]

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

theorem countP_take_mono {α : Type} (p : α → Bool) (l : List α) {m n : Nat} (h : m ≤ n) :
    (l.take m).countP p ≤ (l.take n).countP p :=
  (List.take_sublist_take_left h).countP_le

theorem countP_take_succ {α : Type} (p : α → Bool) {l : List α} {j : Nat} {x : α}
    (h : l[j]? = some x) : (l.take (j + 1)).countP p =
      (l.take j).countP p + if p x then 1 else 0 := by
  have hj : j < l.length := (List.getElem?_eq_some_iff.mp h).1
  rw [List.take_succ_eq_append_getElem hj, List.countP_append]
  rw [List.getElem?_eq_getElem hj] at h
  cases Option.some.inj h
  simp

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts P L X)
include hpre hX ht

/-- **An event before a thread's `n`-th arrival happens before an event after the `n`-th
arrival** of a thread of its CTA. -/
theorem bar_order {x y kx ky id n : Nat} {ex : Event} (hx : X.get (x, kx) = some ex)
    (hnb : Execution.isBarId id ex = false)
    (hcx : ((X.tr x).take kx).countP (Execution.isBarId id) ≤ n) (hy : ky < (X.tr y).length)
    (hcy : n < ((X.tr y).take ky).countP (Execution.isBarId id)) (hc : x / 256 = y / 256) :
    baseCausality L X (x, kx) (y, ky) := by
  have hxg := Frame.lt_of_get hX hx
  obtain ⟨iy, ev, hget, hbar, hcnt⟩ :=
    MbarRing.Slot.exists_nth_countP (Execution.isBarId id) (c := n) hcy
  have hiy : iy < ky := by
    have := (List.getElem?_eq_some_iff.mp hget).1
    simp only [List.length_take] at this
    omega
  rw [List.getElem?_take, ite_eq_left_iff.mpr (fun h => absurd hiy h)] at hget
  rw [List.take_take, Nat.min_eq_left hiy.le] at hcnt
  obtain ⟨pc, k⟩ := ev
  cases k <;> simp only [Execution.isBarId, Bool.false_eq_true] at hbar
  rename_i id' cnt mode
  simp only [beq_iff_eq] at hbar
  subst hbar
  cases mode
  case arrive => exact (hX.noBarArrive Fact.out (y, iy) _ _ _ hget).elim
  have hyb : X.IsBarrier (y, iy) id' cnt pc := hget
  obtain ⟨-, rfl, -⟩ := bar_facts hpre hX ht hyb
  obtain ⟨j, pc', hxb, hord, hhb⟩ := bar_baseCausality hpre hX ht hyb (by omega) hxg hc
  refine hhb kx ky ?_ hiy hy
  rw [hcnt] at hord
  by_contra hle
  rcases Nat.lt_or_eq_of_le (Nat.not_lt.mp hle) with hlt | rfl
  · have h1 := countP_take_mono (Execution.isBarId id') (X.tr x) (show j + 1 ≤ kx by omega)
    rw [countP_take_succ _ hxb] at h1
    simp [Execution.isBarId] at h1
    omega
  · cases Option.some.inj (hx.symm.trans hxb)
    simp [Execution.isBarId] at hnb

/-- **An event happens before an event of its CTA whose state passed more arrivals.** -/
theorem baseCausality_of_counts {x y kx ky : Nat} {dx dy : D} {ex ey : Event}
    (hx : X.get (x, kx) = some ex) (hAx : At P L X x kx dx ex) (hy : X.get (y, ky) = some ey)
    (hAy : At P L X y ky dy ey) (hnb : ∀ pc id c, ex ≠ ⟨pc, .bar id c⟩) (hc : x / 256 = y / 256)
    (h : dx.bc0 < dy.bc0 ∨ dx.bc1 < dy.bc1) : baseCausality L X (x, kx) (y, ky) := by
  have hyl := len_of_get hy
  have hnb' : ∀ id, Execution.isBarId id ex = false := by
    intro id
    obtain ⟨pc, k⟩ := ex
    cases k <;> simp only [Execution.isBarId]
    rename_i id' c' m'
    cases m'
    · exact absurd rfl (hnb _ _ _)
    · exact (hX.noBarArrive Fact.out _ _ _ _ hx).elim
  rcases h with h | h
  · exact bar_order hpre hX ht hx (hnb' 0) (hAx.bc0.le) hyl (by rw [hAy.bc0]; omega) hc
  · exact bar_order hpre hX ht hx (hnb' 1) (hAx.bc1.le) hyl (by rw [hAy.bc1]; omega) hc

end
end PTX.Kernels.RmsNorm.Proof
