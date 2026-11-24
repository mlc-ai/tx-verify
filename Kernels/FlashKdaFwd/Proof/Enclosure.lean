-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Sequence
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-! Executable rational intervals for independently enclosing the real public recurrence.
Centers and radii are exact rationals. Grid rounding always widens the interval. -/
@[expose] public section
namespace FlashKda.Enclosure
open Finset

structure Ball where
  center : ℚ
  radius : ℚ
  deriving Repr, DecidableEq, Inhabited

def Covers (b : Ball) (x : ℝ) := |x-(b.center:ℝ)| ≤ b.radius

def point (x : ℚ) : Ball := ⟨x,0⟩
def endpoints (l u : ℚ) : Ball := ⟨(l+u)/2,(u-l)/2⟩
def lower (a : Ball) := a.center-a.radius
def upper (a : Ball) := a.center+a.radius
def neg (a : Ball) : Ball := ⟨-a.center,a.radius⟩
def add (a b : Ball) : Ball := ⟨a.center+b.center,a.radius+b.radius⟩
def sub (a b : Ball) := add a (neg b)
def mul (a b : Ball) : Ball :=
  ⟨a.center*b.center, |a.center| *b.radius + |b.center| *a.radius + a.radius*b.radius⟩

theorem point_ok (x : ℚ) : Covers (point x) x := by simp [Covers,point]
theorem ends {l u : ℚ} {x : ℝ} : Covers (endpoints l u) x ↔ (l:ℝ) ≤ x ∧ x ≤ u := by
  simp only [Covers,endpoints,Rat.cast_div,Rat.cast_add,Rat.cast_sub,Rat.cast_ofNat,abs_le]
  constructor <;> rintro ⟨a,b⟩ <;> constructor <;> linarith
theorem bounds {b : Ball} {x : ℝ} : Covers b x ↔ (lower b:ℝ) ≤ x ∧ x ≤ upper b := by
  simp only [Covers,lower,upper,abs_le,Rat.cast_sub,Rat.cast_add]
  constructor <;> rintro ⟨a,b⟩ <;> constructor <;> linarith

theorem neg_ok {a x} (h : Covers a x) : Covers (neg a) (-x) := by
  unfold Covers neg
  push_cast
  rw [show -x- -(a.center:ℝ) = -(x-a.center) by ring,abs_neg]
  exact h
theorem add_ok {a b x y} (hx : Covers a x) (hy : Covers b y) : Covers (add a b) (x+y) := by
  change |x+y-((a.center+b.center:ℚ):ℝ)| ≤ ((a.radius+b.radius:ℚ):ℝ)
  push_cast
  rw [show x+y-(a.center+b.center) = (x-a.center)+(y-b.center) by ring]
  exact (abs_add_le _ _).trans (add_le_add hx hy)
theorem sub_ok {a b x y} (hx : Covers a x) (hy : Covers b y) : Covers (sub a b) (x-y) := by
  simpa [sub,sub_eq_add_neg] using add_ok hx (neg_ok hy)

theorem mul_ok {a b x y} (hx : Covers a x) (hy : Covers b y) : Covers (mul a b) (x*y) := by
  have ax : 0 ≤ (a.radius:ℝ) := (abs_nonneg _).trans hx
  have err := mul_le_mul hx hy (abs_nonneg _) ax
  have h1 := mul_le_mul_of_nonneg_left hy (abs_nonneg (a.center:ℝ))
  have h2 := mul_le_mul_of_nonneg_left hx (abs_nonneg (b.center:ℝ))
  let da := x-(a.center:ℝ)
  let db := y-(b.center:ℝ)
  have ident : x*y-(a.center:ℝ)*b.center = (a.center:ℝ)*db+(b.center:ℝ)*da+da*db := by
    dsimp [da,db]; ring
  unfold Covers mul
  push_cast
  rw [ident]
  calc
    _ ≤ |(a.center:ℝ)*db + (b.center:ℝ)*da| + |da*db| := abs_add_le _ _
    _ ≤ (|(a.center:ℝ)*db| + |(b.center:ℝ)*da|) + |da*db| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ ≤ _ := by simpa [da,db,abs_mul] using add_le_add (add_le_add h1 h2) err

/-- An outward-directed grid keeps intermediate denominators bounded across tokens. -/
def grid (bits : Nat) (a : Ball) : Ball :=
  let p : ℚ := 2^bits
  endpoints ((⌊lower a*p⌋:ℚ)/p) ((⌈upper a*p⌉:ℚ)/p)

theorem grid_ok (bits : Nat) {a x} (h : Covers a x) : Covers (grid bits a) x := by
  let p : ℚ := 2^bits
  have pos : 0 < p := by dsimp [p]; positivity
  have l : (⌊lower a*p⌋:ℚ)/p ≤ lower a := (div_le_iff₀ pos).2 (Int.floor_le _)
  have u : upper a ≤ (⌈upper a*p⌉:ℚ)/p := (le_div_iff₀ pos).2 (Int.le_ceil _)
  exact ends.mpr ⟨((Rat.cast_le (K := ℝ)).2 l).trans (bounds.mp h).1,
    (bounds.mp h).2.trans ((Rat.cast_le (K := ℝ)).2 u)⟩

def inner {d : Nat} (a b : Fin d → Ball) : Ball :=
  ⟨∑ i, (mul (a i) (b i)).center, ∑ i, (mul (a i) (b i)).radius⟩

theorem inner_ok {d : Nat} {a b : Fin d → Ball} {x y : Chunk.Row d}
    (ha : ∀ i, Covers (a i) (x i)) (hb : ∀ i, Covers (b i) (y i)) :
    Covers (inner a b) (Chunk.dot x y) := by
  unfold Covers inner Chunk.dot
  push_cast
  rw [← sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs ..).trans (sum_le_sum fun i _ => mul_ok (ha i) (hb i))

/-- A reciprocal is issued only for an interval strictly above zero. -/
def invPos (a : Ball) : Option Ball :=
  if 0 < lower a then some (endpoints (1/upper a) (1/lower a)) else none

theorem inv_ok {a b x} (hx : Covers a x) (h : invPos a = some b) : Covers b (1/x) := by
  unfold invPos at h
  split at h
  · rename_i positive
    cases h
    obtain ⟨l,u⟩ := bounds.mp hx
    have lp : (0:ℝ) < lower a := by exact_mod_cast positive
    apply ends.mpr
    push_cast
    exact ⟨one_div_le_one_div_of_le (lt_of_lt_of_le lp l) u,one_div_le_one_div_of_le lp l⟩
  · contradiction

end FlashKda.Enclosure
