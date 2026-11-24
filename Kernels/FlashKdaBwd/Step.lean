-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Sequence
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import all Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-! # Reverse differentiation of one Kimi Delta Attention token
The state is one column of one head's state matrix. A bar is a weight on a scalar output
of the computation, also called a cotangent. -/
@[expose] public section
namespace FlashKda.Backward
open Chunk Finset
noncomputable section
variable {d : ℕ}

def add (x y : Row d) : Row d := fun i => x i + y i
def scaleRow (a : ℝ) (x : Row d) : Row d := fun i => a * x i
def had (x y : Row d) : Row d := fun i => x i * y i

theorem dot_swap (x y : Row d) : dot x y = dot y x := by simp [dot, mul_comm]
theorem dot_add (x y z : Row d) : dot (add x y) z = dot x z + dot y z := by
  simp [dot, add, add_mul, sum_add_distrib]
theorem dot_scale (a : ℝ) (x y : Row d) : dot (scaleRow a x) y = a * dot x y := by
  simp [dot, scaleRow, mul_sum, mul_assoc]
theorem dot_had (x y z : Row d) : dot (had x y) z = dot x (had y z) := by
  simp [dot, had, mul_assoc]

structure Args (d : ℕ) where
  key : Row d
  query : Row d
  logDecay : Row d
  value : ℝ
  strength : ℝ
  scale : ℝ

def pair (a b : Args d) : ℝ :=
  dot a.key b.key + dot a.query b.query + dot a.logDecay b.logDecay +
    a.value * b.value + a.strength * b.strength + a.scale * b.scale

def decay (a : Args d) : Row d := fun i => Real.exp (a.logDecay i)
def before (s : Row d) (a : Args d) := had s (decay a)
def residual (s : Row d) (a : Args d) := a.value - dot (before s a) a.key
def advance (s : Row d) (a : Args d) := Chunk.step s (decay a) a.key a.value a.strength

/-- Directional change of state, computed in forward order. -/
def beforeD (s ds : Row d) (a da : Args d) :=
  add (had ds (decay a)) (had (before s a) da.logDecay)
def residualD (s ds : Row d) (a da : Args d) :=
  da.value - (dot (beforeD s ds a da) a.key + dot (before s a) da.key)
def advanceD (s ds : Row d) (a da : Args d) :=
  add (beforeD s ds a da)
    (add (scaleRow (da.strength * residual s a + a.strength * residualD s ds a da) a.key)
      (scaleRow (a.strength * residual s a) da.key))

/-- One reverse step takes the weight on the output and the weight on the outgoing state.
It returns the weight on the incoming state and the gradient for each local input. -/
def pull (s : Row d) (a : Args d) (outBar : ℝ) (stateBar : Row d) : Row d × Args d :=
  let z := add stateBar (scaleRow (outBar * a.scale) a.query)
  let r := dot a.key z
  let v := a.strength * r
  let b := add z (scaleRow (-v) a.key)
  (had (decay a) b, {
    key := add (scaleRow (a.strength * residual s a) z) (scaleRow (-v) (before s a))
    query := scaleRow (outBar * a.scale) (advance s a)
    logDecay := had (before s a) b
    value := v
    strength := residual s a * r
    scale := outBar * dot (advance s a) a.query })

theorem readout_adjoint (s ds : Row d) (a da : Args d) (w : ℝ) (b : Row d) :
    w * (da.scale * dot s a.query + a.scale * (dot ds a.query + dot s da.query)) + dot ds b =
    dot ds (add b (scaleRow (w*a.scale) a.query)) +
    dot (scaleRow (w*a.scale) s) da.query + (w * dot s a.query) * da.scale := by
  rw [dot_swap ds (add b (scaleRow (w*a.scale) a.query)), dot_add, dot_scale, dot_scale,
    dot_swap b ds,
    dot_swap a.query ds]
  ring

theorem step_adjoint (s ds : Row d) (a da : Args d) (z : Row d) :
    let v := a.strength * dot a.key z
    let b := add z (scaleRow (-v) a.key)
    dot (advanceD s ds a da) z =
      dot (had (decay a) b) ds + dot (had (before s a) b) da.logDecay +
      dot (add (scaleRow (a.strength * residual s a) z) (scaleRow (-v) (before s a))) da.key +
      v * da.value + (residual s a * dot a.key z) * da.strength := by
  dsimp only
  have split (b : Row d) : dot (beforeD s ds a da) b =
      dot (had (decay a) b) ds + dot (had (before s a) b) da.logDecay := by
    unfold beforeD
    rw [dot_add, dot_had, dot_swap ds]
    congr 1
    simp [dot, had, mul_comm, mul_assoc]
  have hb := split (add z (scaleRow (-(a.strength * dot a.key z)) a.key))
  rw [dot_swap (beforeD s ds a da) (add z _), dot_add, dot_scale,
    dot_swap z (beforeD s ds a da), dot_swap a.key (beforeD s ds a da)] at hb
  simp only [advanceD, dot_add, dot_scale, residualD]
  rw [← hb]
  rw [dot_swap da.key z]
  ring

theorem pull_correct (s ds : Row d) (a da : Args d) (w : ℝ) (b : Row d) :
    let y := advance s a
    let dy := advanceD s ds a da
    w * (da.scale * dot y a.query + a.scale * (dot dy a.query + dot y da.query)) + dot dy b =
    dot (pull s a w b).1 ds + pair (pull s a w b).2 da := by
  dsimp only
  rw [readout_adjoint, step_adjoint]
  unfold pull pair
  ring

/-- Each coordinate follows a differentiable real path with the stated tangent. -/
def RowPath (x : ℝ → Row d) (dx : Row d) (u : ℝ) :=
  ∀ i, HasDerivAt (fun t => x t i) (dx i) u

structure Path (a : ℝ → Args d) (da : Args d) (u : ℝ) : Prop where
  key : RowPath (fun t => (a t).key) da.key u
  query : RowPath (fun t => (a t).query) da.query u
  logDecay : RowPath (fun t => (a t).logDecay) da.logDecay u
  value : HasDerivAt (fun t => (a t).value) da.value u
  strength : HasDerivAt (fun t => (a t).strength) da.strength u
  scale : HasDerivAt (fun t => (a t).scale) da.scale u

theorem dot_deriv {x y : ℝ → Row d} {dx dy : Row d} {u : ℝ}
    (hx : RowPath x dx u) (hy : RowPath y dy u) :
    HasDerivAt (fun t => dot (x t) (y t)) (dot dx (y u) + dot (x u) dy) u := by
  simpa only [dot, ← sum_add_distrib, Pi.mul_apply] using!
    (HasDerivAt.fun_sum (u := univ) (fun i _ => (hx i).mul (hy i)))

theorem advance_deriv {s : ℝ → Row d} {ds : Row d} {a : ℝ → Args d} {da : Args d} {u : ℝ}
    (hs : RowPath s ds u) (ha : Path a da u) :
    RowPath (fun t => advance (s t) (a t)) (advanceD (s u) ds (a u) da) u := by
  have hb : RowPath (fun t => before (s t) (a t)) (beforeD (s u) ds (a u) da) u := by
    intro i
    simpa [beforeD, before, add, had, decay, mul_assoc] using! (hs i).mul (ha.logDecay i).exp
  have hr := ha.value.sub (dot_deriv hb ha.key)
  intro i
  convert (hb i).add ((ha.strength.mul hr).mul (ha.key i)) using 1
  · ext t
    rfl
  · simp [advanceD, add, scaleRow, residual, residualD]

end
end FlashKda.Backward
