-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

namespace PTX

/-- The last `width` values ending at the given lane, clipped to lane zero. -/
def prefixWindow (xs : Nat → Nat) (width lane : Nat) : Nat :=
  ∑ i ∈ Finset.range (min width (lane + 1)), xs (lane - i)

/-- The contribution of one lane before the warp prefix scan. -/
theorem prefixWindow_one (xs : Nat → Nat) (lane : Nat) : prefixWindow xs 1 lane = xs lane := by
  simp [prefixWindow]

/-- One guarded shuffle-up and addition doubles the width of the prefix window. -/
theorem prefixWindow_double (xs : Nat → Nat) (width lane : Nat) :
    prefixWindow xs (2 * width) lane =
      prefixWindow xs width lane +
        if width ≤ lane then prefixWindow xs width (lane - width) else 0 := by
  by_cases h : width ≤ lane
  · have hmin : min (2 * width) (lane + 1) = width + min width (lane - width + 1) := by
      omega
    simp only [prefixWindow, hmin, ite_eq_left h,
      Nat.min_eq_left (show width ≤ lane + 1 by omega)]
    rw [Finset.sum_range_add]
    simp only [Nat.sub_sub]
  · have hmin : min (2 * width) (lane + 1) = lane + 1 := by omega
    simp only [prefixWindow, hmin, ite_eq_right h, Nat.add_zero,
      Nat.min_eq_right (show lane + 1 ≤ width by omega)]

/-- Offsets 1, 2, 4, 8 and 16 give every lane of a warp its full inclusive prefix. -/
theorem prefixWindow_warp (xs : Nat → Nat) {lane : Nat} (hl : lane < 32) :
    prefixWindow xs 32 lane = ∑ i ∈ Finset.range (lane + 1), xs i := by
  rw [prefixWindow, Nat.min_eq_right (show lane + 1 ≤ 32 by omega)]
  simpa only [Nat.add_sub_cancel] using Finset.sum_range_reflect xs (lane + 1)

/-- Every partial scan contains at most the entire warp's contribution. -/
theorem prefixWindow_le_warp (xs : Nat → Nat) (width : Nat) {lane : Nat} (hl : lane < 32) :
    prefixWindow xs width lane ≤ ∑ i ∈ Finset.range 32, xs i := by
  have hRange (f : Nat → Nat) {a b : Nat} (hab : a ≤ b) :
      (∑ i ∈ Finset.range a, f i) ≤ ∑ i ∈ Finset.range b, f i := by
    rw [← Nat.add_sub_of_le hab, Finset.sum_range_add]
    exact Nat.le_add_right _ _
  have hPart : prefixWindow xs width lane ≤ prefixWindow xs 32 lane := by
    unfold prefixWindow
    exact hRange _ (by omega)
  rw [prefixWindow_warp xs hl] at hPart
  exact hPart.trans (hRange _ (by omega))

end PTX
