-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedBarId

@[expose] public section

/-! # The named-barrier schedules of each role against the site tables

* A statistics barrier's `c`-th event of a softmax warp (its arrivals at `gen`, band `S st`,
  `+22`) and of a correction warp (its syncs, band `C st`, `+0`, the item's last `+2`) are in
  global slot `c`: an item has `n + 1` of them, one per slot (`statS`, offset `a`, plus `b` in the
  item's last slot); past the cluster's items the schedule is in the tail (`+2500`). A state is at
  its event's time or before: in an earlier slot (`lt_statS`), or earlier in the slot
  (`lt_same`).
* Barrier 2's events: the start barrier at `bar0T` for all participants; then the softmax and
  correction warps' end arrival at `tailTime … 2000` (`b2S`), the MMA warp's second `bar.sync` at
  `mmaTail … 10` (`b2M`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Sched
open PTX PTX.Proof PTX.Flow Cross Progress.Time

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-! ### The statistics barriers' schedule -/

/-- The time of the `c`-th event on a statistics barrier: global slot `c` at offset `a` (`a + b`
in an item's last slot), past the `T` items in the tail. -/
def statS (n T a b c : Nat) : Nat :=
  base + span * c + (if c < (n + 1) * T then a + (if c % (n + 1) = n then b else 0) else 2500)

theorem statS_ge (n T a b c : Nat) : base + span * c ≤ statS n T a b c := by
  unfold statS; omega

theorem statS_mono {n T a b : Nat} (hab : a + b < span) (c : Nat) :
    statS n T a b c < statS n T a b (c + 1) := by
  have h := statS_ge n T a b (c + 1)
  have : statS n T a b c < base + span * c + span := by
    unfold statS; split_ifs <;> simp only [span] at * <;> omega
  rw [Nat.mul_succ] at h
  omega

/-- A time in an earlier slot is before the event. -/
theorem lt_statS {n T a b i s p o : Nat} (hsp : s < p) (ho : o < span) :
    slotTime n i s o < statS n T a b ((n + 1) * i + p) := by
  have h := statS_ge n T a b ((n + 1) * i + p)
  have : span * (i * (n + 1) + s) + span ≤ span * ((n + 1) * i + p) := by
    rw [← Nat.mul_succ]
    exact Nat.mul_le_mul_left _ (by rw [Nat.mul_comm]; omega)
  unfold slotTime gslot
  omega

theorem statS_at {n T a b i s : Nat} (hi : i < T) (hs : s ≤ n) :
    statS n T a b ((n + 1) * i + s) = slotTime n i s (a + if s = n then b else 0) := by
  have hlt : (n + 1) * i + s < (n + 1) * T := by
    have : (n + 1) * (i + 1) ≤ (n + 1) * T := Nat.mul_le_mul_left _ hi
    rw [Nat.mul_succ] at this
    omega
  have hm : ((n + 1) * i + s) % (n + 1) = s := by
    rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt (by omega)
  simp only [statS, hlt, ↓reduceIte, hm, slotTime, gslot]
  rw [Nat.mul_comm (n + 1) i]

/-- A time earlier in the slot of the event is before it. -/
theorem lt_same {n T a b i s p o : Nat} (hi : i < T) (hs : s ≤ n) (hsp : p = s)
    (ho : o < a + if s = n then b else 0) :
    slotTime n i s o < statS n T a b ((n + 1) * i + p) := by
  rw [hsp, statS_at hi hs]
  exact Progress.Time.lt_of_off ho

/-- A state at the event's site is at its time. -/
theorem eq_same {n T a b i s p o : Nat} (hi : i < T) (hs : s ≤ n) (hsp : p = s)
    (ho : o = a + if s = n then b else 0) :
    slotTime n i s o = statS n T a b ((n + 1) * i + p) := by
  rw [hsp, statS_at hi hs, ho]

theorem lt_statS' {n T a b i s c o : Nat} (hsp : (n + 1) * i + s < c) (ho : o < span) :
    slotTime n i s o < statS n T a b c := by
  have h := lt_statS (n := n) (T := T) (a := a) (b := b) (i := i) (s := s)
    (p := c - (n + 1) * i) (o := o)
    (by omega) ho
  rwa [show (n + 1) * i + (c - (n + 1) * i) = c by omega] at h

theorem lt_same' {n T a b i s c o : Nat} (hi : i < T) (hs : s ≤ n) (hc : c = (n + 1) * i + s)
    (ho : o < a + if s = n then b else 0) : slotTime n i s o < statS n T a b c := by
  rw [hc]; exact lt_same hi hs rfl ho

theorem eq_same' {n T a b i s c o : Nat} (hi : i < T) (hs : s ≤ n) (hc : c = (n + 1) * i + s)
    (ho : o = a + if s = n then b else 0) : slotTime n i s o = statS n T a b c := by
  rw [hc]; exact eq_same hi hs rfl ho

/-- The tail is before the schedule past the items. -/
theorem tail_lt_statS {n T a b o : Nat} (ho : o < 2500) :
    tailTime n T o < statS n T a b ((n + 1) * T) := by
  have : ¬ (n + 1) * T < (n + 1) * T := lt_irrefl _
  simp only [statS, this, ↓reduceIte, tailTime, slotTime, gslot, Nat.add_zero]
  rw [Nat.mul_comm T (n + 1)]
  omega

theorem fixed_lt_statS {x n T a b c : Nat} (h : x < base) : x < statS n T a b c :=
  lt_of_lt_of_le (by omega) (statS_ge n T a b c)

/-! ### Barrier 2's schedules -/

/-- Barrier 2's schedule of a softmax or correction warp. -/
def b2S (n T : Nat) : Nat → Nat
  | 0 => bar0T
  | 1 => tailTime n T 2000
  | k + 2 => tailTime n T (2100 + k)

/-- Barrier 2's schedule of the MMA warp. -/
def b2M (n T : Nat) : Nat → Nat
  | 0 => bar0T
  | 1 => mmaTail n T 10
  | k + 2 => mmaTail n T (100 + k)

theorem b2S_mono (n T k : Nat) : b2S n T k < b2S n T (k + 1) := by
  match k with
  | 0 => simp only [b2S, tailTime]; exact Progress.Time.fixed_lt (by decide)
  | 1 => exact Progress.Time.tail_lt (by decide)
  | k + 2 => exact Progress.Time.tail_lt (by omega)

theorem b2M_mono (n T k : Nat) : b2M n T k < b2M n T (k + 1) := by
  match k with
  | 0 => simp only [b2M, mmaTail, tailTime]; exact Progress.Time.fixed_lt (by decide)
  | 1 => exact Progress.Time.tail_lt (by decide)
  | k + 2 => exact Progress.Time.tail_lt (by omega)

/-- The arrivals at the end barrier are before the MMA warp's second `bar.sync`. -/
theorem b2S_le_b2M (n T : Nat) {k : Nat} (hk : k ≤ 1) : b2S n T k ≤ b2M n T k := by
  rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
  · exact le_rfl
  · exact (Progress.Time.tail_lt (by decide)).le

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Sched
