-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Real.Exp2

@[expose] public section

/-! # Rescale factors of an online softmax

A proof tool for kernels that keep a reference exponent per row and rescale their accumulators
by `α = 2 ^ (c - c')` when the reference moves from `c` to `c'`:

* a reference that never decreases gives `α ≤ 1` (`two_rpow_sub_le_one`), and `α = 1` when
  `α < 1` fails (`two_rpow_sub_eq_one`): an accumulator that skips the rescale because its
  factor is not below one is rescaled by one;
* a lazy rescale, which moves the reference `sc · m` to `sc · mx` only when the gap
  `sc · (m - mx)` is below a threshold `θ ≤ 0` and otherwise keeps it with factor one, has the
  factor `2 ^ (sc · m - sc · m')` of its new reference `m'`, which is not below the old one
  (`lazy_rescale`);
* a normalization by `1 / l'`, with `l' = l` unless `l = 0`, is the division by `l` for a
  positive `l` (`mul_recip_guard`). -/

namespace PTX.Numeric

/-- A rescale factor of a reference that does not decrease is at most one. -/
theorem two_rpow_sub_le_one {a b : ℝ} (h : a ≤ b) : (2 : ℝ) ^ (a - b) ≤ 1 := by
  rw [← two_rpow_zero]
  exact two_rpow_le_iff.mpr (by linarith)

/-- A rescale factor of a reference that does not decrease, and is not below one, is one. -/
theorem two_rpow_sub_eq_one {a b : ℝ} (h : a ≤ b) (hn : ¬ (2 : ℝ) ^ (a - b) < 1) :
    (2 : ℝ) ^ (a - b) = 1 :=
  le_antisymm (two_rpow_sub_le_one h) (not_lt.mp hn)

/-- **A lazy rescale.** Keeping the reference `m` while the scaled gap `sc · (m - mx)` is at
least `θ ≤ 0` (factor one), and moving it to `mx` otherwise (factor `2 ^ (sc · (m - mx))`), has
the factor of the reference move, and the scaled reference does not decrease. -/
theorem lazy_rescale (sc m mx θ : ℝ) (hθ : θ ≤ 0) :
    (if sc * (m - mx) ≥ θ then 1 else (2 : ℝ) ^ (sc * (m - mx))) =
        (2 : ℝ) ^ (sc * m - sc * (if sc * (m - mx) ≥ θ then m else mx)) ∧
      sc * m ≤ sc * (if sc * (m - mx) ≥ θ then m else mx) := by
  split_ifs with h
  · simp
  · refine ⟨by ring_nf, ?_⟩
    have h' := not_le.mp h
    nlinarith

/-- A normalization by the reciprocal of `l`, guarded against `l = 0`, divides by a positive
`l`. -/
theorem mul_recip_guard {o l : ℝ} (hl : 0 < l) : o * (1 / (if l = 0 then 1 else l)) = o / l := by
  simp [hl.ne', div_eq_mul_inv]

end PTX.Numeric
