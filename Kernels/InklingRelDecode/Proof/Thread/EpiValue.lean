-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.EpiPm

@[expose] public section

/-! # The words the epilogue stores, as numbers

The machine's value table states each stored word of `OPart` as the half of a product pair
(`D.word`) of the loaded words with the pair `(inv_l, inv_l)`, evaluated by the Core's rule
under the kernel's assumptions (`mul.f32x2` read as exact real arithmetic, `idealArith`;
`rcp.approx.ftz.f32` read as the exact reciprocal, `approx`). This file reads those values as
reals for the result layer: when the loaded words are `f32` numbers `c k` (the cells of the `O`
tile) and the reciprocal is `1 / l'` (`l'` the row sum, or `1` for an empty row), word `k` is the
number `(1 / l') * c k` (`word_fin`), and the reciprocal is exact (`inv_fin`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.Epi
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section
set_option maxRecDepth 100000

/-- **A packed multiplication of numbers** (no rounding modifier) is the pair of the exact
products. -/
theorem floatE_mulI_fin {va vb : Value} {x0 x1 y0 y1 : ℝ}
    (hx0 : valFloat .f32 (splitValue 64 va).1 = .ok x0)
    (hx1 : valFloat .f32 (splitValue 64 va).2 = .ok x1)
    (hy0 : valFloat .f32 (splitValue 64 vb).1 = .ok y0)
    (hy1 : valFloat .f32 (splitValue 64 vb).2 = .ok y1) :
    floatE mulI [va, vb] = .ok (.pair (.float .f32 (x0 * y0)) (.float .f32 (x1 * y1))) := by
  simp only [floatE, idealVal, pairRead_of hx0 hx1, pairRead_of hy0 hy1, bindRead, mulEReal_coe,
    erealValue_coe, pure, Except.pure]

/-- **The reciprocal is exact**: for a nonzero `f32` number `x` selected by the code (the row
sum, or `1.0` for an empty row), `inv_l = 1 / x`. -/
theorem inv_fin (p : Prm) {x : ℝ} (hx : valFloat .f32 (if p.eq0 then one32 else p.l) = .ok x)
    (h0 : x ≠ 0) : p.inv = fl (1 / x) := by
  simp [Prm.inv, rcpE_fin hx h0, okVal, fl]

/-- The product pair of `f32` numbers: `inv_l` times each. -/
theorem prod_fin (d : D) (hsk : d.sk = false) {q : Nat} {c0 c1 y : ℝ}
    (h0 : d.o.getD (2 * q) (b32 0) = fl c0) (h1 : d.o.getD (2 * q + 1) (b32 0) = fl c1)
    (hy : d.pr.inv = fl y) :
    d.prod q = .pair (fl (y * c0)) (fl (y * c1)) := by
  have hc : d.pr.cpair = .pair (fl y) (fl y) := by
    simp [Prm.cpair, hy, joinValue, fl]
  have hj : joinValue (d.o.getD (2 * q) (b32 0)) (d.o.getD (2 * q + 1) (b32 0)) =
      .pair (fl c0) (fl c1) := by
    rw [h0, h1]
    simp [joinValue, fl]
  simp only [D.prod, hsk, Bool.false_eq_true, ↓reduceIte, hc, hj]
  have hm := floatE_mulI_fin (va := .pair (fl y) (fl y)) (vb := .pair (fl c0) (fl c1))
    (x0 := y) (x1 := y) (y0 := c0) (y1 := c1)
    (by simp [fl, splitValue, valFloat_float]) (by simp [fl, splitValue, valFloat_float])
    (by simp [fl, splitValue, valFloat_float]) (by simp [fl, splitValue, valFloat_float])
  unfold mulOut
  rw [hm]
  rfl

/-- **The stored words are the cells times `1 / l'`**: if the loaded words are the `f32` numbers
`c k` and `inv_l` is the number `y`, then word `k` of `OPart` is the number `y * c k`. -/
theorem word_fin (d : D) (hsk : d.sk = false) {c : Nat → ℝ} {y : ℝ}
    (hc : ∀ k < 64, d.o.getD k (b32 0) = fl (c k)) (hy : d.pr.inv = fl y) {k : Nat}
    (hk : k < 64) : d.word k = fl (y * c k) := by
  unfold D.word
  split_ifs with hk2
  · obtain ⟨q, rfl⟩ : ∃ q, k = 2 * q := ⟨k / 2, by omega⟩
    have := prod_fin d hsk (q := q) (hc _ (by omega)) (by
      have := hc (2 * q + 1) (by omega); exact this) hy
    rw [show 2 * q / 2 = q by omega, this]
    simp [splitValue, fl]
  · obtain ⟨q, rfl⟩ : ∃ q, k = 2 * q + 1 := ⟨k / 2, by omega⟩
    have := prod_fin d hsk (q := q) (hc _ (by omega)) (hc _ (by omega)) hy
    rw [show (2 * q + 1) / 2 = q by omega, this]
    simp [splitValue, fl]

end
end PTX.Kernels.InklingRelDecode.Proof.Epi
