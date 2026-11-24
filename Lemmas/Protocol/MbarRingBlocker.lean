-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.MbarPending
public import Lemmas.MBarrier.MBarrierTransactions
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring

@[expose] public section

/-! # Who blocks a failed poll of a ring object

A proof tool for the progress of ring waits. A thread stopped at a failed poll of a ring object
waits for the object's current phase to complete. The object's history says who has not yet
delivered: the kernel names the contributors and supplies the rank comparison.

* **Unit objects** (no transactions: an empty barrier completed by consumer notifications, or
  a full barrier by unit arrivals). In a checked history without invalidation whose final
  state has no outstanding transactions, an arrival of the phase is pending
  (`MBarrier.stateBefore_pending_pos`), so the arrival units are below a full phase
  (`units_lt`); with count 1, the arrival units are the phase number (`units_eq_phase`). When
  contributor `k` owes `w k` units per phase (the count is `∑ k, w k`) and the history holds at
  least `w k` units per delivery `cnt k` of each contributor, some contributor has delivered no
  more than the phase number (`exists_short`, by pigeonhole `exists_short_of_lt`); when each has
  delivered at least the phase number, exactly that (`exists_eq`).
* **Transaction objects** (a full barrier with count 1, completed by one arrival expecting
  `n · B` bytes and `n` copies of `B` bytes each). The phase either awaits its arrival (the
  arrival units are the phase number) or has its arrival and fewer than `n` copies per phase
  reached (`tx_short`): otherwise the transaction counter would be zero and an arrival pending. -/

namespace PTX.MbarRing.Blocker

open MBarrier

/-- **Pigeonhole**: weighted deliveries below a full phase leave a contributor with a positive
weight at most `P` deliveries. -/
theorem exists_short_of_lt {κ : Type} [Fintype κ] (w cnt : κ → Nat) (P : Nat)
    (h : ∑ k, w k * cnt k < (∑ k, w k) * (P + 1)) : ∃ k, 0 < w k ∧ cnt k ≤ P := by
  by_contra hn
  push Not at hn
  have hle : (∑ k, w k) * (P + 1) ≤ ∑ k, w k * cnt k := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro k _
    rcases Nat.eq_zero_or_pos (w k) with h0 | hp
    · simp [h0]
    · exact Nat.mul_le_mul_left _ (hn k hp)
  omega

variable {ι : Type} {log : List (Record ι)}

/-- **A blocked unit object's arrival units are below a full phase**: with no outstanding
transactions, the final state has a pending arrival. -/
theorem units_lt (h : CheckedLog log) (hni : NoInval log) {st : State}
    (hs : stateBefore log log.length = some st) (htx : st.tx = 0)
    (hinc : incrementsBefore log log.length = 0) :
    arrivalUnits log < st.expected * (st.phase + 1) := by
  have hpos := stateBefore_pending_pos h hs htx
  obtain ⟨-, hacc⟩ := (h.accounted hni le_rfl).2 st hs
  simp only [unitsBefore, List.take_length] at hacc
  rw [hinc] at hacc
  omega

/-- **A count-1 object without transactions has completed one phase per arrival unit.** -/
theorem units_eq_phase (h : CheckedLog log) (hni : NoInval log) {st : State}
    (hs : stateBefore log log.length = some st) (htx : st.tx = 0) (hexp : st.expected = 1)
    (hinc : incrementsBefore log log.length = 0) :
    arrivalUnits log = st.phase := by
  have hpos := stateBefore_pending_pos h hs htx
  obtain ⟨hp, hacc⟩ := (h.accounted hni le_rfl).2 st hs
  simp only [unitsBefore, List.take_length] at hacc
  rw [hexp, hinc] at hp hacc
  omega

/-- **A blocked unit object has a short contributor.** Contributor `k` owes `w k` units per
phase (`hexp`), and the history holds `w k` units per delivery `cnt k` (`hunits`): some
contributor that owes units has delivered at most the phase number. -/
theorem exists_short {κ : Type} [Fintype κ] (h : CheckedLog log) (hni : NoInval log)
    {st : State} (hs : stateBefore log log.length = some st) (htx : st.tx = 0) (w cnt : κ → Nat)
    (hexp : st.expected = ∑ k, w k) (hunits : ∑ k, w k * cnt k ≤ arrivalUnits log)
    (hinc : incrementsBefore log log.length = 0) :
    ∃ k, 0 < w k ∧ cnt k ≤ st.phase := by
  have hlt := units_lt h hni hs htx hinc
  rw [hexp] at hlt
  exact exists_short_of_lt w cnt st.phase (by omega)

/-- **A blocked unit object has a contributor exactly at its phase**, when every contributor has
delivered at least the phase number. -/
theorem exists_eq {κ : Type} [Fintype κ] (h : CheckedLog log) (hni : NoInval log)
    {st : State} (hs : stateBefore log log.length = some st) (htx : st.tx = 0) (w cnt : κ → Nat)
    (hexp : st.expected = ∑ k, w k) (hunits : ∑ k, w k * cnt k ≤ arrivalUnits log)
    (hge : ∀ k, st.phase ≤ cnt k) (hinc : incrementsBefore log log.length = 0) :
    ∃ k, 0 < w k ∧ cnt k = st.phase := by
  obtain ⟨k, hw, hk⟩ := exists_short h hni hs htx w cnt hexp hunits hinc
  exact ⟨k, hw, Nat.le_antisymm hk (hge k)⟩

/-- **A blocked transaction object awaits its arrival or a copy.** An object of count 1 whose
arrivals expect `n · B` bytes per unit (`hbytes`) and whose completions move `B` bytes each
(`hu`), with at most `n` completions per phase reached (`hle`): either the phase's arrival is
pending (the arrival units are the phase number), or it is in and fewer than `n` copies per
phase reached completed. -/
theorem tx_short (h : CheckedLog log) (hni : NoInval log) {st : State}
    (hs : stateBefore log log.length = some st) (hexp : st.expected = 1) {n B : Nat}
    (hbytes : expectedTxBytes log = n * B * arrivalUnits log) (hu : UniformCompletedTx log B)
    (hle : completedTxCount log ≤ n * (st.phase + 1))
    (hinc : incrementsBefore log log.length = 0) :
    arrivalUnits log = st.phase ∨
      (arrivalUnits log = st.phase + 1 ∧ completedTxCount log < n * (st.phase + 1)) := by
  obtain ⟨hpend, hacc⟩ := (h.accounted hni le_rfl).2 st hs
  simp only [unitsBefore, List.take_length] at hacc
  rw [hexp, hinc] at hpend hacc
  rcases (show st.pending = 0 ∨ st.pending = 1 by omega) with hp0 | hp1
  · refine .inr ⟨by omega, ?_⟩
    have hbal := h.tx_balance hni le_rfl hs
    rw [List.take_length, hbytes, completedTxBytes_eq_unit_mul_count hu] at hbal
    have htx : st.tx ≠ 0 := fun h0 => by
      have := stateBefore_pending_pos h hs h0
      omega
    refine Nat.lt_of_le_of_ne hle fun heq => htx ?_
    rw [hbal, heq, show arrivalUnits log = st.phase + 1 by omega]
    push_cast
    ring
  · exact .inl (by omega)

end PTX.MbarRing.Blocker
