-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Proof.Enclosure
import Mathlib.Tactic

/-! Rational enclosures of the nonlinear stages from the public KDA inputs. -/
@[expose] public section
namespace FlashKda.Enclosure
open Finset

/-- The first twelve terms and a uniform Taylor remainder for arguments in [-1,1]. -/
def taylor (z : ℚ) : Ball :=
  ⟨∑ m ∈ range 12, z^m/m.factorial, |z|^12*(13/(12 : Nat).factorial/12)⟩

theorem taylor_ok {z : ℚ} (hz : |z| ≤ 1) : Covers (taylor z) (Real.exp (z:ℝ)) := by
  have h := Real.exp_bound (n := 12) (by exact_mod_cast hz : |(z:ℝ)| ≤ 1) (by decide)
  simpa [Covers,taylor,div_div] using h

def squareTimes (bits : Nat) : Nat → Ball → Ball
  | 0, a => a
  | n+1, a => let b := squareTimes bits n a; grid bits (mul b b)

theorem square_times_ok (bits n : Nat) {a : Ball} {x : ℝ} (h : Covers a (Real.exp x)) :
    Covers (squareTimes bits n a) (Real.exp (x*(2:ℝ)^n)) := by
  induction n with
  | zero => simpa [squareTimes] using h
  | succ n ih =>
    rw [show x*(2:ℝ)^(n+1) = x*2^n+x*2^n by ring,Real.exp_add]
    exact grid_ok _ (mul_ok ih ih)

def expAt (bits splits : Nat) (x : ℚ) : Option Ball :=
  let z := x/(2:ℚ)^splits
  if |z| ≤ 1 then some (squareTimes bits splits (grid bits (taylor z))) else none

theorem exp_at_ok {bits splits : Nat} {x : ℚ} {b : Ball} (h : expAt bits splits x = some b) :
    Covers b (Real.exp (x:ℝ)) := by
  dsimp only [expAt] at h
  split at h
  · rename_i bound
    cases h
    have r := square_times_ok bits splits (grid_ok bits (taylor_ok bound))
    simpa [Rat.cast_div] using r
  · contradiction

def expBall (bits splits : Nat) (a : Ball) : Option Ball := do
  let l ← expAt bits splits (lower a)
  let u ← expAt bits splits (upper a)
  return endpoints (lower l) (upper u)

theorem exp_ok {bits splits : Nat} {a b : Ball} {x : ℝ} (hx : Covers a x)
    (h : expBall bits splits a = some b) : Covers b (Real.exp x) := by
  obtain ⟨lx,ux⟩ := bounds.mp hx
  unfold expBall at h
  cases lo : expAt bits splits (lower a) with
  | none => simp [lo] at h
  | some l =>
    cases hi : expAt bits splits (upper a) with
    | none => simp [lo,hi] at h
    | some u =>
      simp [lo,hi] at h
      subst b
      exact ends.mpr ⟨(bounds.mp (exp_at_ok lo)).1.trans (Real.exp_le_exp.mpr lx),
        (Real.exp_le_exp.mpr ux).trans (bounds.mp (exp_at_ok hi)).2⟩

def logistic (bits splits : Nat) (a : Ball) : Option Ball := do
  let e ← expBall bits splits (neg a)
  let r ← invPos (add (point 1) e)
  return grid bits r

theorem logistic_ok {bits splits : Nat} {a b : Ball} {x : ℝ} (hx : Covers a x)
    (h : logistic bits splits a = some b) : Covers b (Algorithm.sigmoid x) := by
  unfold logistic at h
  cases he : expBall bits splits (neg a) with
  | none => simp [he] at h
  | some e =>
    cases hi : invPos (add (point 1) e) with
    | none => simp [he,hi] at h
    | some r =>
      simp [he,hi] at h
      subst b
      simpa [Algorithm.sigmoid] using grid_ok bits
        (inv_ok (add_ok (point_ok 1) (exp_ok (neg_ok hx) he)) hi)

/-- Integer square root proposes adjacent grid points. Their defining inequalities
are checked directly, keeping the proposal outside the proof's trusted assumptions. -/
def invRoot (bits : Nat) (v : ℚ) : Option Ball :=
  let p : ℚ := 2^bits
  let n := Nat.sqrt ⌊p^2/v⌋.toNat
  let l := (n:ℚ)/p
  let u := ((n:ℚ)+1)/p
  if 0 < v ∧ 0 ≤ l ∧ 0 ≤ u ∧ l^2*v ≤ 1 ∧ 1 ≤ u^2*v then some (endpoints l u) else none

theorem inv_root_ok {bits : Nat} {v : ℚ} {b : Ball} (h : invRoot bits v = some b) :
    Covers b (1/Real.sqrt (v:ℝ)) := by
  dsimp only [invRoot] at h
  split at h
  · rename_i check
    cases h
    obtain ⟨positive,lp,up,lv,uv⟩ := check
    have pos : (0:ℝ) < v := by exact_mod_cast positive
    have root := Real.sqrt_pos.mpr pos
    apply ends.mpr
    constructor
    · apply (le_div_iff₀ root).2
      apply (sq_le_sq₀ (mul_nonneg (by exact_mod_cast lp) root.le) (by norm_num)).mp
      rw [mul_pow,Real.sq_sqrt pos.le,one_pow]
      exact_mod_cast lv
    · apply (div_le_iff₀ root).2
      apply (sq_le_sq₀ (by norm_num) (mul_nonneg (by exact_mod_cast up) root.le)).mp
      rw [mul_pow,Real.sq_sqrt pos.le,one_pow]
      exact_mod_cast uv
  · contradiction

end FlashKda.Enclosure
