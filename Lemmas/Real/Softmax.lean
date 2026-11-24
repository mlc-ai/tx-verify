-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Real.Exp2
public import Lemmas.Real.BlockSums

@[expose] public section

/-! # Online softmax in base 2, independent of the reference maxima

A proof tool for an online (blockwise) softmax. Block `τ < n` has `b` scores `x τ j` (already
scaled) and values `v τ j`. After block `τ` the accumulator holds its sums against a reference
exponent `c τ` (`c τ = sc · m` for a running reference maximum `m`). The first block writes
`S 0 = Σ_j 2 ^ (x 0 j - c 0) · v 0 j`; each later block rescales by
`α = 2 ^ (c τ - c (τ + 1))` and adds its own terms:
`S (τ + 1) = S τ · α + Σ_j 2 ^ (x (τ + 1) j - c (τ + 1)) · v (τ + 1) j`.

* `softmax_acc`: then `S τ = Σ_{τ' ≤ τ} Σ_j 2 ^ (x τ' j - c τ) · v τ' j`, for any reference
  sequence (no sign, monotonicity or bound on `c`); `softmax_sum` is the row sum (`v = 1`), and
  `softmax_sum_pos` its positivity.
* The reference factors out (`sum_sum_two_rpow_sub_mul`, `sum_sum_two_rpow_sub`), so the ratio
  of an accumulator and the row sum with one reference sequence does not depend on it
  (`softmax_ratio`).
* `final_ratio`: with the blocks visited last first over keys `b · (n - 1 - τ) + j`, the ratio
  of the sums with any reference is the base-2 softmax average over all `b · n` keys;
  `softmax_final` combines it with `softmax_acc`. -/

namespace PTX.Numeric

open Finset

/-! ## The reference factors out -/

theorem sum_sum_two_rpow_sub_mul {α β : Type*} (s : Finset α) (t : Finset β)
    (y z : α → β → ℝ) (r : ℝ) :
    ∑ a ∈ s, ∑ b ∈ t, (2 : ℝ) ^ (y a b - r) * z a b =
      2 ^ (-r) * ∑ a ∈ s, ∑ b ∈ t, (2 : ℝ) ^ y a b * z a b := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [two_rpow_sub_eq_mul]
  ring

theorem sum_sum_two_rpow_sub {α β : Type*} (s : Finset α) (t : Finset β) (y : α → β → ℝ)
    (r : ℝ) :
    ∑ a ∈ s, ∑ b ∈ t, (2 : ℝ) ^ (y a b - r) = 2 ^ (-r) * ∑ a ∈ s, ∑ b ∈ t, (2 : ℝ) ^ y a b := by
  simpa using sum_sum_two_rpow_sub_mul s t y (fun _ _ => 1) r

/-! ## The accumulation invariant -/

/-- **Max-agnostic accumulation.** A first block against reference `c 0` followed by rescales
`2 ^ (c τ - c (τ + 1))` and the next block's terms against `c (τ + 1)` hold, after block `τ`,
the terms of all blocks so far against `c τ`. -/
theorem softmax_acc {n b : ℕ} {x v : ℕ → ℕ → ℝ} {c S : ℕ → ℝ}
    (h0 : S 0 = ∑ j ∈ range b, (2 : ℝ) ^ (x 0 j - c 0) * v 0 j)
    (hs : ∀ τ, τ + 1 < n → S (τ + 1) = S τ * 2 ^ (c τ - c (τ + 1)) +
      ∑ j ∈ range b, (2 : ℝ) ^ (x (τ + 1) j - c (τ + 1)) * v (τ + 1) j) :
    ∀ τ < n, S τ = ∑ τ' ∈ range (τ + 1), ∑ j ∈ range b, (2 : ℝ) ^ (x τ' j - c τ) * v τ' j := by
  intro τ hτ
  induction τ with
  | zero => simp [h0]
  | succ τ ih =>
    rw [hs τ hτ, ih (by omega), Finset.sum_range_succ (n := τ + 1)]
    congr 1
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun τ' _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← two_rpow_sub_sub (x τ' j) (c τ) (c (τ + 1))]
    ring

/-- `softmax_acc` for the row sum. -/
theorem softmax_sum {n b : ℕ} {x : ℕ → ℕ → ℝ} {c l : ℕ → ℝ}
    (h0 : l 0 = ∑ j ∈ range b, (2 : ℝ) ^ (x 0 j - c 0))
    (hs : ∀ τ, τ + 1 < n → l (τ + 1) = l τ * 2 ^ (c τ - c (τ + 1)) +
      ∑ j ∈ range b, (2 : ℝ) ^ (x (τ + 1) j - c (τ + 1))) :
    ∀ τ < n, l τ = ∑ τ' ∈ range (τ + 1), ∑ j ∈ range b, (2 : ℝ) ^ (x τ' j - c τ) := by
  intro τ hτ
  have h := softmax_acc (n := n) (v := fun _ _ => 1) (S := l) (by simpa using h0)
    (by simpa using hs) τ hτ
  simpa using h

/-- The row sum of at least one key is positive. -/
theorem softmax_sum_pos {n b : ℕ} {x : ℕ → ℕ → ℝ} {c l : ℕ → ℝ} (hb : 0 < b)
    (h0 : l 0 = ∑ j ∈ range b, (2 : ℝ) ^ (x 0 j - c 0))
    (hs : ∀ τ, τ + 1 < n → l (τ + 1) = l τ * 2 ^ (c τ - c (τ + 1)) +
      ∑ j ∈ range b, (2 : ℝ) ^ (x (τ + 1) j - c (τ + 1))) :
    ∀ τ < n, 0 < l τ := by
  intro τ hτ
  rw [softmax_sum h0 hs τ hτ]
  refine Finset.sum_pos (fun τ' _ => ?_) (by simp)
  exact sum_two_rpow_pos (by simp [Nat.pos_iff_ne_zero.mp hb]) _

/-- **The ratio does not depend on the references**: an accumulator and the row sum built
with one reference sequence have the ratio of the unreferenced sums. -/
theorem softmax_ratio {n b : ℕ} {x v : ℕ → ℕ → ℝ} {c O l : ℕ → ℝ}
    (hO0 : O 0 = ∑ j ∈ range b, (2 : ℝ) ^ (x 0 j - c 0) * v 0 j)
    (hOs : ∀ τ, τ + 1 < n → O (τ + 1) = O τ * 2 ^ (c τ - c (τ + 1)) +
      ∑ j ∈ range b, (2 : ℝ) ^ (x (τ + 1) j - c (τ + 1)) * v (τ + 1) j)
    (hl0 : l 0 = ∑ j ∈ range b, (2 : ℝ) ^ (x 0 j - c 0))
    (hls : ∀ τ, τ + 1 < n → l (τ + 1) = l τ * 2 ^ (c τ - c (τ + 1)) +
      ∑ j ∈ range b, (2 : ℝ) ^ (x (τ + 1) j - c (τ + 1))) :
    ∀ τ < n, O τ / l τ =
      (∑ τ' ∈ range (τ + 1), ∑ j ∈ range b, (2 : ℝ) ^ x τ' j * v τ' j) /
        ∑ τ' ∈ range (τ + 1), ∑ j ∈ range b, (2 : ℝ) ^ x τ' j := by
  intro τ hτ
  rw [softmax_acc hO0 hOs τ hτ, softmax_sum hl0 hls τ hτ, sum_sum_two_rpow_sub_mul,
    sum_sum_two_rpow_sub, mul_div_mul_left _ _ (two_rpow_ne_zero _)]

/-! ## Descending blocks of keys -/

/-- **The final ratio.** With `n` blocks of `b` keys visited last first (block `n - 1 - τ` at
visit `τ`), the ratio of the sums of `2 ^ (sc · s k - r) · v k` and `2 ^ (sc · s k - r)` over
the visits is the base-2 softmax average over all `b · n` keys, for any reference `r`. -/
theorem final_ratio (n b : ℕ) (s v : ℕ → ℝ) (sc r : ℝ) :
    (∑ τ ∈ range n, ∑ j ∈ range b,
        (2 : ℝ) ^ (sc * s (b * (n - 1 - τ) + j) - r) * v (b * (n - 1 - τ) + j)) /
      (∑ τ ∈ range n, ∑ j ∈ range b, (2 : ℝ) ^ (sc * s (b * (n - 1 - τ) + j) - r)) =
    (∑ k ∈ range (b * n), (2 : ℝ) ^ (sc * s k) * v k) /
      ∑ k ∈ range (b * n), (2 : ℝ) ^ (sc * s k) := by
  rw [sum_sum_two_rpow_sub_mul (y := fun τ j => sc * s (b * (n - 1 - τ) + j))
      (z := fun τ j => v (b * (n - 1 - τ) + j)),
    sum_sum_two_rpow_sub (y := fun τ j => sc * s (b * (n - 1 - τ) + j)),
    mul_div_mul_left _ _ (two_rpow_ne_zero _)]
  have h1 := sum_desc_blocks (fun k => (2 : ℝ) ^ (sc * s k) * v k) b n
  have h2 := sum_desc_blocks (fun k => (2 : ℝ) ^ (sc * s k)) b n
  rw [h1, h2]

/-- **Online softmax over descending blocks.** An accumulator and a row sum built blockwise
(`softmax_acc`) over `n ≥ 1` blocks of `b` keys visited last first, with scores
`sc · s k` and values `v k` of key `k = b · (n - 1 - τ) + j`, end with the base-2 softmax
average over all `b · n` keys. -/
theorem softmax_final {n b : ℕ} {s v : ℕ → ℝ} {sc : ℝ} {c O l : ℕ → ℝ} (hn : 0 < n)
    (hO0 : O 0 = ∑ j ∈ range b,
      (2 : ℝ) ^ (sc * s (b * (n - 1) + j) - c 0) * v (b * (n - 1) + j))
    (hOs : ∀ τ, τ + 1 < n → O (τ + 1) = O τ * 2 ^ (c τ - c (τ + 1)) +
      ∑ j ∈ range b, (2 : ℝ) ^ (sc * s (b * (n - 1 - (τ + 1)) + j) - c (τ + 1)) *
        v (b * (n - 1 - (τ + 1)) + j))
    (hl0 : l 0 = ∑ j ∈ range b, (2 : ℝ) ^ (sc * s (b * (n - 1) + j) - c 0))
    (hls : ∀ τ, τ + 1 < n → l (τ + 1) = l τ * 2 ^ (c τ - c (τ + 1)) +
      ∑ j ∈ range b, (2 : ℝ) ^ (sc * s (b * (n - 1 - (τ + 1)) + j) - c (τ + 1))) :
    O (n - 1) / l (n - 1) =
      (∑ k ∈ range (b * n), (2 : ℝ) ^ (sc * s k) * v k) /
        ∑ k ∈ range (b * n), (2 : ℝ) ^ (sc * s k) := by
  rw [softmax_acc (x := fun τ j => sc * s (b * (n - 1 - τ) + j))
      (v := fun τ j => v (b * (n - 1 - τ) + j)) (by simpa using hO0) hOs (n - 1) (by omega),
    softmax_sum (x := fun τ j => sc * s (b * (n - 1 - τ) + j)) (by simpa using hl0) hls
      (n - 1) (by omega),
    Nat.sub_add_cancel hn]
  exact final_ratio n b s v sc (c (n - 1))

end PTX.Numeric
