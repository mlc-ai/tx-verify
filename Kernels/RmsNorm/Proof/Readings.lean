-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.Thread.Machine
public import Lemmas.Flow.Scalars

@[expose] public section

/-! # The outcomes of the code on real values

The abstract states hold raw values and the registers the outcomes of the code on them
(`Sites.lean`). On words of real halves and on single-precision numbers every outcome is the
number of the exact real result: a widened half is its number (`xw_hwords`), the chain of fused
multiply-adds is the real sum of squares (`fmaRun_fin`), a butterfly's running sum is the real one
(`bsumV_fin`), the scale factor of a total is `rms` of it where its `rsqrt` argument is positive
(`rrV_fin`), and an output pair is the pair of halves of the real products (`outV_fin`). None of
the conditions of the machine fails on such values (`xOk_fin`, `ttOk_fin`, `tileOk_fin`). -/

namespace PTX.Kernels.RmsNorm.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- A word of two halves. -/
def hpair (a b : ℝ) : Value := .pair (h16 a) (h16 b)

/-- Four words of the halves `x 0, ..., x 7`. -/
def hwords (x : Nat → ℝ) : List Value :=
  [hpair (x 0) (x 1), hpair (x 2) (x 3), hpair (x 4) (x 5), hpair (x 6) (x 7)]

/-- Four single-precision numbers `x k, ..., x (k + 3)`. -/
def fwords (x : Nat → ℝ) (k : Nat) : List Value := [fl (x k), fl (x (k + 1)), fl (x (k + 2)),
  fl (x (k + 3))]

theorem valFloat_h16 (x : ℝ) : valFloat .f16 (h16 x) = .ok x := rfl

theorem halfOf_hwords (x : Nat → ℝ) {m : Nat} (hm : m < 8) : halfOf (hwords x) m = h16 (x m) := by
  interval_cases m <;> rfl

/-- **A widened half of real words is its number.** -/
theorem xw_hwords (x : Nat → ℝ) {m : Nat} (hm : m < 8) : xw (hwords x) m = fl (x m) := by
  rw [xw, halfOf_hwords x hm, widenE_fin (valFloat_h16 _)]; rfl

theorem unpackE_hpair (a b : ℝ) : unpackE 32 (hpair a b) = .ok (h16 a, h16 b) := by
  simp [unpackE, hpair, h16, splitValue, Value.bytes, FloatFmt.bytes]

/-- **The chain of fused multiply-adds of real squares** reads as the real sum. -/
theorem fmaRun_fin {ws : List Value} {v : Nat → ℝ} (hw : ∀ m < 8, xw ws m = fl (v m))
    {z : Value} {s : ℝ} (hz : valFloat .f32 z = .ok s) :
    ∀ n, n ≤ 8 → valFloat .f32 (fmaRun ws n z) = .ok (fmaSum v n s)
  | 0, _ => hz
  | n + 1, hn => by
    rw [fmaRun, fmaV, hw n (Nat.lt_of_succ_le hn),
      floatE_fma_fin (valFloat_fl _) (valFloat_fl _) (fmaRun_fin hw hz n (Nat.le_of_succ_le hn))]
    rfl

theorem fmaRun_fl {ws : List Value} {v : Nat → ℝ} (hw : ∀ m < 8, xw ws m = fl (v m))
    {z : Value} {s : ℝ} (hz : valFloat .f32 z = .ok s) {n : Nat} (hn : n < 8) :
    fmaRun ws (n + 1) z = fl (fmaSum v (n + 1) s) := by
  rw [fmaRun, fmaV, hw n hn,
    floatE_fma_fin (valFloat_fl _) (valFloat_fl _) (fmaRun_fin hw hz n hn.le)]
  rfl

/-- The fused multiply-adds of real squares do not fault. -/
theorem fmaOk_fin {ws : List Value} {v : Nat → ℝ} (hw : ∀ m < 8, xw ws m = fl (v m))
    {z : Value} {s : ℝ} (hz : valFloat .f32 z = .ok s) {n : Nat} (hn : n < 8) :
    (floatE (fmaI .rn true) [xw ws n, xw ws n, fmaRun ws n z]).toBool = true := by
  rw [hw n hn, floatE_fma_fin (valFloat_fl _) (valFloat_fl _) (fmaRun_fin hw hz n hn.le)]; rfl

/-- **On words of real halves the input loads' code does not fault.** -/
theorem xOk_fin (x : Nat → ℝ) {z : Value} {s : ℝ} (hz : valFloat .f32 z = .ok s) :
    xOk (hwords x) z = true := by
  have hw : ∀ m < 8, xw (hwords x) m = fl (x m) := fun m hm => xw_hwords x hm
  have hu : ∀ k < 8, (widenE (halfOf (hwords x) k)).toBool = true := fun k hk => by
    rw [halfOf_hwords x hk, widenE_fin (valFloat_h16 _)]; rfl
  simp only [xOk, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, hu 0 (by decide)⟩, hu 1 (by decide)⟩, ?_⟩, hu 2 (by decide)⟩,
    hu 3 (by decide)⟩, ?_⟩, hu 4 (by decide)⟩, hu 5 (by decide)⟩, ?_⟩, hu 6 (by decide)⟩,
    hu 7 (by decide)⟩, fmaOk_fin hw hz (by decide)⟩, fmaOk_fin hw hz (by decide)⟩,
    fmaOk_fin hw hz (by decide)⟩, fmaOk_fin hw hz (by decide)⟩, fmaOk_fin hw hz (by decide)⟩,
    fmaOk_fin hw hz (by decide)⟩, fmaOk_fin hw hz (by decide)⟩, fmaOk_fin hw hz (by decide)⟩ <;>
  simp only [hwords, List.getD_cons_zero, List.getD_cons_succ, unpackE_hpair] <;> rfl

/-- **A running sum of real summands** reads as the real sum. -/
theorem bsumV_fin {q : Value} {qr : ℝ} (hq : valFloat .f32 q = .ok qr) {r : Nat → Value}
    {rr : Nat → ℝ} : ∀ n, (∀ k < n, valFloat .f32 (r k) = .ok (rr k)) →
      valFloat .f32 (bsumV q r n) = .ok (bsum qr rr n)
  | 0, _ => hq
  | n + 1, hr => by
    rw [bsumV, addV, floatE_add_fin (bsumV_fin hq n fun k hk => hr k (by omega))
      (hr n (by omega))]
    rfl

theorem bsumV_fl {q : Value} {qr : ℝ} (hq : valFloat .f32 q = .ok qr) {r : Nat → Value}
    {rr : Nat → ℝ} {n : Nat} (hr : ∀ k < n + 1, valFloat .f32 (r k) = .ok (rr k)) :
    bsumV q r (n + 1) = fl (bsum qr rr (n + 1)) := by
  rw [bsumV, addV, floatE_add_fin (bsumV_fin hq n fun k hk => hr k (by omega))
    (hr n (by omega))]
  rfl

/-- An addition of two numbers does not fault. -/
theorem addOk_fin {a b : Value} {x y : ℝ} (ha : valFloat .f32 a = .ok x)
    (hb : valFloat .f32 b = .ok y) : (floatE (addI true) [a, b]).toBool = true := by
  rw [floatE_add_fin ha hb]; rfl

theorem eps_pos : 0 < eps := by
  simp [eps, f32Value, FloatFmt.decode, FloatFmt.layout, Layout.decode, Layout.fieldVal,
    Layout.magnitude, Layout.bias, Layout.width, FVal.num]

/-- The `rsqrt` argument of a row's total is positive. -/
theorem tt_pos (P : Params) (r : Nat) :
    0 < (∑ m ∈ Finset.range 4096, xe P r m ^ 2) / c4096 + eps := by
  have := Finset.sum_nonneg fun m (_ : m ∈ Finset.range 4096) => sq_nonneg (xe P r m)
  have := eps_pos
  rw [c4096_eq]
  positivity

theorem divV_fin (T : ℝ) : divV (fl T) = fl (T / c4096) := by
  have hc : c4096 ≠ 0 := by rw [c4096_eq]; norm_num
  rw [divV, approxE_div_fin (valFloat_fl T) valFloat_4096 hc]; rfl

theorem addV_eps (q : ℝ) : addV (fl q) epsw = fl (q + eps) := by
  rw [addV, floatE_add_fin (vb := epsw) (valFloat_fl q) valFloat_eps]; rfl

/-- **The scale factor of a real total** whose `rsqrt` argument is positive is `rms` of it. -/
theorem rrV_fin {T : ℝ} (hpos : 0 < T / c4096 + eps) : rrV (fl T) = fl (rms T) := by
  rw [rrV, divV_fin, addV_eps, approxE_rsqrt_fin (valFloat_fl _) hpos]; rfl

theorem cpair_fin {T : ℝ} (hpos : 0 < T / c4096 + eps) :
    cpair (fl T) = .pair (fl (rms T)) (fl (rms T)) := by
  rw [cpair, rrV_fin hpos]; rfl

/-- **The load of a real total whose `rsqrt` argument is positive does not fault.** -/
theorem ttOk_fin {T : ℝ} (hpos : 0 < T / c4096 + eps) : ttOk (fl T) = true := by
  have hc : c4096 ≠ 0 := by rw [c4096_eq]; norm_num
  simp only [ttOk, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [approxE_div_fin (valFloat_fl T) valFloat_4096 hc]; rfl
  · rw [divV_fin, floatE_add_fin (vb := epsw) (valFloat_fl _) valFloat_eps]; rfl
  · rw [divV_fin, addV_eps, approxE_rsqrt_fin (valFloat_fl _) hpos]; rfl

theorem mulV_fin (a b c d : ℝ) :
    mulV (.pair (fl a) (fl b)) (.pair (fl c) (fl d)) = .pair (fl (a * c)) (fl (b * d)) := by
  rw [mulV, floatE_mul2_fin (va := .pair (fl a) (fl b)) (vb := .pair (fl c) (fl d))
    (valFloat_fl a) (valFloat_fl b) (valFloat_fl c) (valFloat_fl d)]
  rfl

theorem mulOk_fin (a b c d : ℝ) :
    (floatE (mul2I .rz true) [.pair (fl a) (fl b), .pair (fl c) (fl d)]).toBool = true := by
  rw [floatE_mul2_fin (va := .pair (fl a) (fl b)) (vb := .pair (fl c) (fl d))
    (valFloat_fl a) (valFloat_fl b) (valFloat_fl c) (valFloat_fl d)]
  rfl

theorem pw_fin (s : Nat → ℝ) {j : Nat} (hj : j < 4) :
    pw (fwords s 0) (fwords s 4) j = .pair (fl (s (2 * j))) (fl (s (2 * j + 1))) := by
  interval_cases j <;> rfl

theorem mm1_fin (s : Nat → ℝ) (r : ℝ) {j : Nat} (hj : j < 4) :
    mm1 (fwords s 0) (fwords s 4) (.pair (fl r) (fl r)) j =
      .pair (fl (s (2 * j) * r)) (fl (s (2 * j + 1) * r)) := by
  rw [mm1, pw_fin s hj, mulV_fin]

theorem mm2_fin (w s : Nat → ℝ) (r : ℝ) {j : Nat} (hj : j < 4) :
    mm2 (hwords w) (fwords s 0) (fwords s 4) (.pair (fl r) (fl r)) j =
      .pair (fl (s (2 * j) * r * w (2 * j))) (fl (s (2 * j + 1) * r * w (2 * j + 1))) := by
  rw [mm2, ml1, mh1, mm1_fin s r hj, xw_hwords w (by omega), xw_hwords w (by omega)]
  exact mulV_fin _ _ _ _

/-- **An output pair of real values** is the pair of halves of the real products. -/
theorem outV_fin (w s : Nat → ℝ) (r : ℝ) {j : Nat} (hj : j < 4) :
    outV (hwords w) (fwords s 0) (fwords s 4) (.pair (fl r) (fl r)) j =
      .pair (.float .f16 (s (2 * j) * r * w (2 * j)))
        (.float .f16 (s (2 * j + 1) * r * w (2 * j + 1))) := by
  rw [outV, mh2, ml2, mm2_fin w s r hj]
  exact cvtPairV_of_valFloat (valFloat_fl _) (valFloat_fl _) |>.trans rfl

/-- **On real weights, reloads and scale factors a tile's code does not fault.** -/
theorem tileOk_fin (w s : Nat → ℝ) (r : ℝ) :
    tileOk (hwords w) (fwords s 0) (fwords s 4) (.pair (fl r) (fl r)) = true := by
  have hu : ∀ k < 8, (widenE (halfOf (hwords w) k)).toBool = true := fun k hk => by
    rw [halfOf_hwords w hk, widenE_fin (valFloat_h16 _)]; rfl
  have hc : ∀ j < 4, (cvtPairE (mh2 (hwords w) (fwords s 0) (fwords s 4) (.pair (fl r) (fl r)) j)
      (ml2 (hwords w) (fwords s 0) (fwords s 4) (.pair (fl r) (fl r)) j)).toBool = true :=
    fun j hj => by
      rw [mh2, ml2, mm2_fin w s r hj]
      simp only [splitValue]
      rw [cvtPairE_of_valFloat (valFloat_fl _) (valFloat_fl _)]; rfl
  have hq : ∀ j < 4, (floatE (mul2I .rz true)
      [joinValue (ml1 (fwords s 0) (fwords s 4) (.pair (fl r) (fl r)) j)
        (mh1 (fwords s 0) (fwords s 4) (.pair (fl r) (fl r)) j),
      joinValue (xw (hwords w) (2 * j)) (xw (hwords w) (2 * j + 1))]).toBool = true :=
    fun j hj => by
      rw [ml1, mh1, mm1_fin s r hj, xw_hwords w (by omega), xw_hwords w (by omega)]
      exact mulOk_fin _ _ _ _
  have hp : ∀ j < 4, (floatE (mul2I .rz true)
      [pw (fwords s 0) (fwords s 4) j, .pair (fl r) (fl r)]).toBool = true :=
    fun j hj => by rw [pw_fin s hj]; exact mulOk_fin _ _ _ _
  simp only [tileOk, tileW, tileP, tileQ, tileC, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, hu 0 (by decide)⟩, hu 1 (by decide)⟩, ?_⟩, hu 2 (by decide)⟩,
    hu 3 (by decide)⟩, ?_⟩, hu 4 (by decide)⟩, hu 5 (by decide)⟩, ?_⟩, hu 6 (by decide)⟩,
    hu 7 (by decide)⟩, ⟨⟨⟨⟨⟨⟨⟨?_, hp 0 (by decide)⟩, ?_⟩, hp 1 (by decide)⟩, ?_⟩,
    hp 2 (by decide)⟩, ?_⟩, hp 3 (by decide)⟩⟩, ⟨⟨⟨hq 0 (by decide), hq 1 (by decide)⟩,
    hq 2 (by decide)⟩, hq 3 (by decide)⟩⟩, ⟨⟨⟨hc 0 (by decide), hc 1 (by decide)⟩,
    hc 2 (by decide)⟩, hc 3 (by decide)⟩⟩ <;>
  simp only [hwords, fwords, List.getD_cons_zero, List.getD_cons_succ, unpackE_hpair] <;> rfl

end
end PTX.Kernels.RmsNorm.Proof
