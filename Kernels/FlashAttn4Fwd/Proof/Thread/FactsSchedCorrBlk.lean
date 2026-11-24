-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsSchedBase

@[expose] public section

/-! # The blocks of a correction warp's warp-collective `tcgen05` events

An item of `n` trips has `V = 2 (n - 1)` votes. A correction thread's warp-collective
`tcgen05` events come in blocks: block `r < V` of item `i` is the rescale after vote `V i + r`,
twenty-five events when that vote's ballot is nonzero and none otherwise; block `V` is the item's
final part, thirty-two events. With `v m` the nonzero ballots among the first `m`, block `r` of
item `i` starts at ordinal `25 v (V i + r) + 32 i` (`bS`). Block `q` of the run is block
`q % (V + 1)` of item `q / (V + 1)` (`blkB`, `blkT`).

Event `o` of a rescale is in the vote's slot and band at `+6 + 2 o` (the chunks' loads, waits and
stores, then the store wait at `+54`); event `o` of a final part is in slot `n`, in the band of
stage `o / 16`, at `+12 + 20 j` (a chunk's load, `j = (o % 16) / 2`) or two later (its wait)
(`tmB`). Times increase along a block and from a block to the next (`blkT_step`,
`blkT_next`).

The schedule `sch` maps an ordinal `N` to the block `q` with `blkB q ≤ N < blkB (q + 1)` (the
least `q` with `N < blkB (q + 1)`) and to the event `N - blkB q` of it. It increases
(`sch_mono`), it is the block's time inside a block (`sch_eq`), and it is no earlier than the
time of every event of a block that starts at or before `N` (`le_sch`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Sched
open PTX PTX.Proof PTX.Flow Cross Progress.Time

noncomputable section

namespace CorrTc

/-- The votes of an item of `n` trips. -/
abbrev nV (n : Nat) : Nat := 2 * (n - 1)

/-- The first ordinal of block `r` of item `i`. -/
def bS (n : Nat) (v : Nat → Nat) (i r : Nat) : Nat := 25 * v (nV n * i + r) + 32 * i

/-- The first ordinal of block `q` of the run. -/
def blkB (n : Nat) (v : Nat → Nat) (q : Nat) : Nat := bS n v (q / (nV n + 1)) (q % (nV n + 1))

/-- The time of event `o` of block `r` of item `i`. -/
def tmB (n i r o : Nat) : Nat :=
  if r < nV n then slotTime n i (r / 2 + 1) (bandC (r % 2) + 6 + 2 * o)
  else slotTime n i n (bandC (o / 16) + 12 + 20 * (o % 16 / 2) + 2 * (o % 2))

/-- The time of event `o` of block `q` of the run. -/
def blkT (n q o : Nat) : Nat := tmB n (q / (nV n + 1)) (q % (nV n + 1)) o

/-- The count of nonzero ballots: it starts at zero and grows by at most one per ballot. -/
structure VOk (v : Nat → Nat) : Prop where
  zero : v 0 = 0
  step : ∀ m, v m ≤ v (m + 1) ∧ v (m + 1) ≤ v m + 1

theorem dec_eq {W i r : Nat} (hr : r < W) : (W * i + r) / W = i ∧ (W * i + r) % W = r := by
  have hW : 0 < W := by omega
  refine ⟨?_, ?_⟩
  · rw [Nat.mul_add_div hW, Nat.div_eq_of_lt hr, Nat.add_zero]
  · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

theorem blkB_at {n : Nat} {v : Nat → Nat} {i r : Nat} (hr : r ≤ nV n) :
    blkB n v ((nV n + 1) * i + r) = bS n v i r := by
  obtain ⟨h1, h2⟩ := dec_eq (W := nV n + 1) (i := i) (r := r) (by omega)
  rw [blkB, h1, h2]

theorem blkT_at {n i r o : Nat} (hr : r ≤ nV n) :
    blkT n ((nV n + 1) * i + r) o = tmB n i r o := by
  obtain ⟨h1, h2⟩ := dec_eq (W := nV n + 1) (i := i) (r := r) (by omega)
  rw [blkT, h1, h2]

/-- Every block of the run is block `r ≤ V` of an item `i`. -/
theorem blk_cases (n q : Nat) : ∃ i r, r ≤ nV n ∧ q = (nV n + 1) * i + r :=
  ⟨q / (nV n + 1), q % (nV n + 1), by have := Nat.mod_lt q (show 0 < nV n + 1 by omega); omega,
    (Nat.div_add_mod q (nV n + 1)).symm⟩

/-! ### Ordinals of the blocks -/

theorem bS_next {n : Nat} {v : Nat → Nat} (i : Nat) :
    bS n v (i + 1) 0 = bS n v i (nV n) + 32 := by
  simp only [bS, Nat.add_zero, Nat.mul_succ]
  omega

theorem blkB_step {n : Nat} {v : Nat → Nat} (hv : VOk v) (q : Nat) :
    blkB n v q ≤ blkB n v (q + 1) ∧ blkB n v (q + 1) ≤ blkB n v q + 32 := by
  obtain ⟨i, r, hr, rfl⟩ := blk_cases n q
  rcases Nat.lt_or_ge r (nV n) with h | h
  · rw [blkB_at hr, show (nV n + 1) * i + r + 1 = (nV n + 1) * i + (r + 1) by omega,
      blkB_at h]
    have := hv.step (nV n * i + r)
    simp only [bS, show nV n * i + (r + 1) = nV n * i + r + 1 by omega]
    omega
  · rw [show r = nV n by omega, blkB_at le_rfl,
      show (nV n + 1) * i + nV n + 1 = (nV n + 1) * (i + 1) + 0 by ring, blkB_at (Nat.zero_le _),
      bS_next]
    omega

theorem blkB_mono {n : Nat} {v : Nat → Nat} (hv : VOk v) {q q' : Nat} (h : q ≤ q') :
    blkB n v q ≤ blkB n v q' := by
  induction q' with
  | zero => rw [Nat.le_zero.mp h]
  | succ q' ih =>
    rcases Nat.lt_or_ge q (q' + 1) with h' | h'
    · exact (ih (by omega)).trans (blkB_step hv q').1
    · rw [show q = q' + 1 by omega]

theorem blkB_zero {n : Nat} {v : Nat → Nat} (hv : VOk v) : blkB n v 0 = 0 := by
  rw [show (0 : Nat) = (nV n + 1) * 0 + 0 by rfl, blkB_at (Nat.zero_le _)]
  simp [bS, hv.zero]

theorem exists_blk (n : Nat) (v : Nat → Nat) (N : Nat) : ∃ q, N < blkB n v (q + 1) := by
  refine ⟨(nV n + 1) * N + nV n, ?_⟩
  rw [show (nV n + 1) * N + nV n + 1 = (nV n + 1) * (N + 1) + 0 by ring,
    blkB_at (Nat.zero_le _)]
  simp only [bS]
  omega

/-! ### Times of the blocks -/

theorem tmB_step {n i r o : Nat} : tmB n i r o < tmB n i r (o + 1) := by
  unfold tmB
  split_ifs
  · exact Progress.Time.lt_of_off (by omega)
  · exact Progress.Time.lt_of_off (by simp only [bandC]; omega)

theorem tmB_next_rs {n i r o : Nat} (hr : r < nV n) (ho : o < 32) :
    tmB n i r o < tmB n i (r + 1) 0 := by
  unfold tmB
  simp only [hr, ↓reduceIte]
  split_ifs with h
  · rcases Nat.mod_two_eq_zero_or_one r with h2 | h2
    · rw [show (r + 1) / 2 = r / 2 by omega]
      exact Progress.Time.lt_of_off (by simp only [bandC]; omega)
    · exact Progress.Time.lt_of_slot (by omega) (by simp only [bandC, span]; omega)
  · exact Progress.Time.lt_of_slot (by simp only [nV] at *; omega)
      (by simp only [bandC, span]; omega)

theorem tmB_next_fin {n i o : Nat} (ho : o < 32) :
    tmB n i (nV n) o < tmB n (i + 1) 0 0 := by
  unfold tmB
  simp only [lt_irrefl, ↓reduceIte]
  split_ifs <;> exact Progress.Time.lt_of_item le_rfl (by omega) (by simp only [bandC, span]; omega)

theorem blkT_step {n q o : Nat} : blkT n q o < blkT n q (o + 1) :=
  tmB_step

theorem blkT_next {n q o : Nat} (ho : o < 32) : blkT n q o < blkT n (q + 1) 0 := by
  obtain ⟨i, r, hr, rfl⟩ := blk_cases n q
  rcases Nat.lt_or_ge r (nV n) with h | h
  · rw [blkT_at hr, show (nV n + 1) * i + r + 1 = (nV n + 1) * i + (r + 1) by omega,
      blkT_at h]
    exact tmB_next_rs h ho
  · rw [show r = nV n by omega, blkT_at le_rfl,
      show (nV n + 1) * i + nV n + 1 = (nV n + 1) * (i + 1) + 0 by ring,
      blkT_at (Nat.zero_le _)]
    exact tmB_next_fin ho

theorem blkT_le_off {n q o o' : Nat} (h : o ≤ o') : blkT n q o ≤ blkT n q o' := by
  induction o' with
  | zero => rw [Nat.le_zero.mp h]
  | succ o' ih =>
    rcases Nat.lt_or_ge o (o' + 1) with h' | h'
    · exact (ih (by omega)).trans blkT_step.le
    · rw [show o = o' + 1 by omega]

theorem blkT_off {n q o : Nat} : blkT n q 0 ≤ blkT n q o :=
  blkT_le_off (Nat.zero_le _)

theorem blkT_mono {n q q' : Nat} (h : q ≤ q') : blkT n q 0 ≤ blkT n q' 0 := by
  induction q' with
  | zero => rw [Nat.le_zero.mp h]
  | succ q' ih =>
    rcases Nat.lt_or_ge q (q' + 1) with h' | h'
    · exact (ih (by omega)).trans (blkT_next (by decide)).le
    · rw [show q = q' + 1 by omega]

/-! ### The schedule -/

/-- The block of ordinal `N`: the least `q` with `N < blkB (q + 1)`. -/
def blkOf (n : Nat) (v : Nat → Nat) (N : Nat) : Nat := Nat.find (exists_blk n v N)

/-- **The time of the `N`-th event**: event `N - blkB q` of its block `q`. -/
def sch (n : Nat) (v : Nat → Nat) (N : Nat) : Nat :=
  blkT n (blkOf n v N) (N - blkB n v (blkOf n v N))

theorem blkOf_spec {n : Nat} {v : Nat → Nat} (hv : VOk v) (N : Nat) :
    blkB n v (blkOf n v N) ≤ N ∧ N < blkB n v (blkOf n v N + 1) := by
  refine ⟨?_, Nat.find_spec (exists_blk n v N)⟩
  cases h : blkOf n v N with
  | zero => rw [blkB_zero hv]; exact Nat.zero_le _
  | succ p =>
    have := Nat.find_min (exists_blk n v N) (m := p) (by unfold blkOf at h; omega)
    omega

theorem blkOf_off {n : Nat} {v : Nat → Nat} (hv : VOk v) (N : Nat) :
    N - blkB n v (blkOf n v N) < 32 := by
  have h := blkOf_spec (n := n) hv N
  have := (blkB_step (n := n) hv (blkOf n v N)).2
  omega

/-- **Inside a block** the schedule is the block's time. -/
theorem sch_eq {n : Nat} {v : Nat → Nat} (hv : VOk v) {q N : Nat} (h1 : blkB n v q ≤ N)
    (h2 : N < blkB n v (q + 1)) : sch n v N = blkT n q (N - blkB n v q) := by
  have hq : blkOf n v N = q := by
    refine le_antisymm (Nat.find_min' _ h2) ?_
    by_contra hlt
    have := blkB_mono (n := n) hv (show blkOf n v N + 1 ≤ q by omega)
    have := (blkOf_spec (n := n) hv N).2
    omega
  rw [sch, hq]

/-- **The schedule is no earlier** than event `o` of a block that starts `o` or more before
`N`. -/
theorem le_sch {n : Nat} {v : Nat → Nat} (hv : VOk v) {q o N : Nat} (h : blkB n v q + o ≤ N)
    (ho : o < 32) : blkT n q o ≤ sch n v N := by
  have hs := blkOf_spec (n := n) hv N
  have hoff := blkOf_off (n := n) hv N
  unfold sch
  rcases Nat.lt_trichotomy (blkOf n v N) q with hlt | heq | hgt
  · have := blkB_mono (n := n) hv (show blkOf n v N + 1 ≤ q by omega)
    omega
  · rw [heq] at hoff ⊢
    exact blkT_le_off (by omega)
  · have h1 := blkT_next (n := n) (q := q) ho
    have h2 := blkT_mono (n := n) (show q + 1 ≤ blkOf n v N by omega)
    have h3 := blkT_off (n := n) (q := blkOf n v N) (o := N - blkB n v (blkOf n v N))
    omega

/-- **The schedule increases.** -/
theorem sch_mono {n : Nat} {v : Nat → Nat} (hv : VOk v) (N : Nat) :
    sch n v N < sch n v (N + 1) := by
  have hs := blkOf_spec (n := n) hv N
  have hoff := blkOf_off (n := n) hv N
  have hN : sch n v N = blkT n (blkOf n v N) (N - blkB n v (blkOf n v N)) := rfl
  rcases Nat.lt_or_ge (N + 1) (blkB n v (blkOf n v N + 1)) with h | h
  · rw [hN, sch_eq hv (by omega) h, show N + 1 - blkB n v (blkOf n v N) =
      N - blkB n v (blkOf n v N) + 1 by omega]
    exact blkT_step
  · have h1 := le_sch (n := n) hv (q := blkOf n v N + 1) (o := 0) (N := N + 1) (by omega)
      (by decide)
    have h2 := blkT_next (n := n) (q := blkOf n v N) hoff
    rw [hN]
    omega

/-! ### The schedule at the blocks of an item -/

/-- Event `o` of the rescale of block `r` (its vote nonzero) is at the event's time. -/
theorem sch_at_rs {n : Nat} {v : Nat → Nat} (hv : VOk v) {i r o N : Nat} (hr : r < nV n)
    (hz : v (nV n * i + r + 1) = v (nV n * i + r) + 1) (ho : o < 25)
    (hN : N = bS n v i r + o) : sch n v N = tmB n i r o := by
  have h1 := blkB_at (v := v) (i := i) hr.le
  have h2 := blkB_at (v := v) (i := i) (show r + 1 ≤ nV n by omega)
  rw [← Nat.add_assoc] at h2
  rw [sch_eq hv (q := (nV n + 1) * i + r) (by omega)
    (by rw [h2]; simp only [bS, ← Nat.add_assoc, hz] at hN ⊢; omega), h1,
    show N - bS n v i r = o by omega, blkT_at hr.le]

/-- Event `o` of the final part is at the event's time. -/
theorem sch_at_fin {n : Nat} {v : Nat → Nat} (hv : VOk v) {i o N : Nat} (ho : o < 32)
    (hN : N = bS n v i (nV n) + o) : sch n v N = tmB n i (nV n) o := by
  have h1 := blkB_at (v := v) (i := i) (le_refl (nV n))
  have h2 := blkB_at (n := n) (v := v) (i := i + 1) (Nat.zero_le _)
  rw [bS_next, show (nV n + 1) * (i + 1) + 0 = (nV n + 1) * i + nV n + 1 by ring] at h2
  rw [sch_eq hv (q := (nV n + 1) * i + nV n) (by omega) (by omega), h1,
    show N - bS n v i (nV n) = o by omega, blkT_at le_rfl]

/-- A time before event `o` of a block that starts `o` or more before `N` is before the
schedule. -/
theorem lt_sch {n : Nat} {v : Nat → Nat} (hv : VOk v) {i r o N x : Nat} (hr : r ≤ nV n)
    (ho : o < 32) (hN : bS n v i r + o ≤ N) (h : x < tmB n i r o) : x < sch n v N := by
  have := le_sch (n := n) hv (q := (nV n + 1) * i + r) (o := o) (N := N)
    (by rw [blkB_at hr]; exact hN) ho
  rw [blkT_at hr] at this
  omega

/-- A time before the next item is before the schedule past the final part. -/
theorem lt_sch_next {n : Nat} {v : Nat → Nat} (hv : VOk v) {i N x : Nat}
    (hN : bS n v i (nV n) + 32 ≤ N) (h : x < tmB n (i + 1) 0 0) : x < sch n v N :=
  lt_sch hv (Nat.zero_le _) (by decide) (by rw [bS_next]; omega) h

end CorrTc
end
end PTX.Kernels.FlashAttn4Fwd.Proof.Sched
