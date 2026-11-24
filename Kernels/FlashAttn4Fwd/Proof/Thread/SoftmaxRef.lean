-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxRealsSums
public import Lemmas.Flow.EventCount
public import Lemmas.Flow.FilterIndex

@[expose] public section

/-! # The reference maximum and row sum of each tile

With `n` tiles per item and scores `S u k` of tile `u` (global over the items, `u = n i + T`),
the softmax's reference maximum `refM` and row sum `rowL` follow the code's recurrence: the first
tile of an item takes its row maximum (`rmax0`) and the sum of its probabilities; a loop tile
moves the reference by the lazy rescale (`mNr`, as `mN`) and rescales the previous sum. The
recurrence is defined for every tile, so tiles that never ran continue it.

The scores of a thread's trace prefix `es` (`tsc`) are the words its loads returned, its load of
ordinal `4 u + c` holding columns `32 c …` of tile `u` (`loadValsAt`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The lazy rescale of reference `m` against scores `s` (`mN`). -/
def mNr (sc m : ℝ) (s : Nat → ℝ) : ℝ := if sc * (m - mx m s) ≥ -8 then m else mx m s

/-- The reference maximum of tile `u`. -/
def refM (sc : ℝ) (n : Nat) (S : Nat → Nat → ℝ) : Nat → ℝ
  | 0 => rmax0 (S 0)
  | u + 1 => if (u + 1) % n = 0 then rmax0 (S (u + 1)) else mNr sc (refM sc n S u) (S (u + 1))

/-- The probabilities of tile `u`, summed. -/
def pSum (sc : ℝ) (n : Nat) (S : Nat → Nat → ℝ) (u : Nat) : ℝ :=
  ∑ k ∈ Finset.range 128, (2 : ℝ) ^ (sc * S u k - sc * refM sc n S u)

/-- The row sum after tile `u`. -/
def rowL (sc : ℝ) (n : Nat) (S : Nat → Nat → ℝ) : Nat → ℝ
  | 0 => pSum sc n S 0
  | u + 1 => if (u + 1) % n = 0 then pSum sc n S (u + 1) else
      rowL sc n S u * (2 : ℝ) ^ (sc * refM sc n S u - sc * refM sc n S (u + 1)) +
        pSum sc n S (u + 1)

theorem refM_first {sc : ℝ} {n : Nat} {S : Nat → Nat → ℝ} {u : Nat} (h : u % n = 0) :
    refM sc n S u = rmax0 (S u) := by
  cases u with
  | zero => rfl
  | succ u => simp [refM, h]

theorem refM_loop {sc : ℝ} {n : Nat} {S : Nat → Nat → ℝ} {u : Nat} (h : (u + 1) % n ≠ 0) :
    refM sc n S (u + 1) = mNr sc (refM sc n S u) (S (u + 1)) := by
  simp [refM, h]

theorem rowL_first {sc : ℝ} {n : Nat} {S : Nat → Nat → ℝ} {u : Nat} (h : u % n = 0) :
    rowL sc n S u = pSum sc n S u := by
  cases u with
  | zero => rfl
  | succ u => simp [rowL, h]

theorem rowL_loop {sc : ℝ} {n : Nat} {S : Nat → Nat → ℝ} {u : Nat} (h : (u + 1) % n ≠ 0) :
    rowL sc n S (u + 1) = rowL sc n S u *
      (2 : ℝ) ^ (sc * refM sc n S u - sc * refM sc n S (u + 1)) + pSum sc n S (u + 1) := by
  simp [rowL, h]

/-- The reference does not decrease in a loop tile. -/
theorem refM_mono {sc : ℝ} {n : Nat} {S : Nat → Nat → ℝ} {u : Nat} (h : (u + 1) % n ≠ 0) :
    sc * refM sc n S u ≤ sc * refM sc n S (u + 1) := by
  rw [refM_loop h]
  exact (Numeric.lazy_rescale sc (refM sc n S u) (mx (refM sc n S u) (S (u + 1))) (-8)
    (by norm_num)).2

/-- The scores of the first tile's row maximum are its first 128. -/
theorem rmax0_congr {s s' : Nat → ℝ} (h : ∀ k < 128, s k = s' k) : rmax0 s = rmax0 s' := by
  simp (disch := omega) only [rmax0, h]

/-- A loop tile's row maximum reads its first 128 scores. -/
theorem mx_congr {m : ℝ} {s s' : Nat → ℝ} (h : ∀ k < 128, s k = s' k) : mx m s = mx m s' := by
  simp (disch := omega) only [mx, h]

theorem mNr_congr {sc m : ℝ} {s s' : Nat → ℝ} (h : ∀ k < 128, s k = s' k) :
    mNr sc m s = mNr sc m s' := by
  simp only [mNr, mx_congr h]

/-- The recurrence reads the first 128 scores of the tiles up to `u`. -/
theorem refM_congr {sc : ℝ} {n : Nat} {S S' : Nat → Nat → ℝ} :
    ∀ {u : Nat}, (∀ u' ≤ u, ∀ k < 128, S u' k = S' u' k) → refM sc n S u = refM sc n S' u
  | 0, h => rmax0_congr (h 0 le_rfl)
  | u + 1, h => by
    have ih := refM_congr (sc := sc) (n := n) (u := u) fun u' hu' k hk => h u' (by omega) k hk
    simp only [refM, ih, rmax0_congr (h (u + 1) le_rfl), mNr_congr (h (u + 1) le_rfl)]

theorem pSum_congr {sc : ℝ} {n : Nat} {S S' : Nat → Nat → ℝ} {u : Nat}
    (h : ∀ u' ≤ u, ∀ k < 128, S u' k = S' u' k) : pSum sc n S u = pSum sc n S' u := by
  unfold pSum
  rw [refM_congr h]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [h u le_rfl k (Finset.mem_range.mp hk)]

theorem rowL_congr {sc : ℝ} {n : Nat} {S S' : Nat → Nat → ℝ} :
    ∀ {u : Nat}, (∀ u' ≤ u, ∀ k < 128, S u' k = S' u' k) → rowL sc n S u = rowL sc n S' u
  | 0, h => pSum_congr h
  | u + 1, h => by
    have ih := rowL_congr (sc := sc) (n := n) (u := u) fun u' hu' k hk => h u' (by omega) k hk
    have hr := refM_congr (sc := sc) (n := n) (u := u) fun u' hu' k hk => h u' (by omega) k hk
    simp only [rowL, ih, hr, refM_congr h, pSum_congr h]

/-- The values the thread's load of ordinal `o` (of the stage's score columns) returned. -/
def loadValsAt (L : Launch) (g : Nat) (es : List Event) (o : Nat) : List Value :=
  match (es.filter (tcLdAt (tmem L g 0) (tmem L g 128)))[o]? with
  | some ⟨_, .tc (.ld _ vals _)⟩ => vals
  | _ => []

/-- The scores of the trace prefix `es`: column `k` of tile `u` is word `k % 32` of the load of
ordinal `4 u + k / 32`. -/
def tsc (L : Launch) (g : Nat) (es : List Event) (u k : Nat) : ℝ :=
  rd32 ((loadValsAt L g es (4 * u + k / 32)).getD (k % 32) (b32 0))

/-- Every load of `es` returned 32 single-precision numbers. -/
def LoadsF32 (es : List Event) : Prop :=
  ∀ x ∈ es, ∀ pc a vals, x = ⟨pc, .tc (.ld a vals .s32x32b)⟩ →
    vals.length = 32 ∧ ∀ v ∈ vals, ∃ y, v = .float .f32 y

theorem LoadsF32.of_snoc {es : List Event} {e : Event} (h : LoadsF32 (es ++ [e])) :
    LoadsF32 es := fun x hx => h x (List.mem_append_left _ hx)

theorem loadValsAt_snoc {L : Launch} {g : Nat} {es : List Event} {e : Event} {o : Nat}
    (h : o < tcLdsIn (tmem L g 0) (tmem L g 128) es) :
    loadValsAt L g (es ++ [e]) o = loadValsAt L g es o := by
  unfold loadValsAt
  rw [filter_append_getElem h]

/-- The scores of loaded tiles do not change when the trace grows. -/
theorem tsc_snoc {L : Launch} {g : Nat} {es : List Event} {e : Event} {u k : Nat}
    (h : 4 * u + 4 ≤ tcLdsIn (tmem L g 0) (tmem L g 128) es) (hk : k < 128) :
    tsc L g (es ++ [e]) u k = tsc L g es u k := by
  unfold tsc
  rw [loadValsAt_snoc (by omega)]

theorem tsc_snoc_le {L : Launch} {g : Nat} {es : List Event} {e : Event} {u : Nat}
    (h : 4 * u + 4 ≤ tcLdsIn (tmem L g 0) (tmem L g 128) es) :
    ∀ u' ≤ u, ∀ k < 128, tsc L g (es ++ [e]) u' k = tsc L g es u' k :=
  fun _ hu' _ hk => tsc_snoc (by omega) hk

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
