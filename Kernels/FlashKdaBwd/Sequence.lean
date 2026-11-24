-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaBwd.Step
import all Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-! # Reverse sweep through all live KDA tokens
Weighting every output and the final state gives the usual vector-Jacobian product.
The cotangent on the incoming state is passed to the preceding token. -/
@[expose] public section
namespace FlashKda.Backward
open Chunk Sequence Finset
noncomputable section
variable {d : ℕ}

def atToken (x : Tokens d) (scl : ℝ) (t : ℕ) : Args d :=
  ⟨x.key t, x.query t, x.logDecay t, x.value t, x.strength t, scl⟩

/-- The gradient contains the initial-state weight followed by one record per live token. -/
inductive Gradient (d : ℕ) (α : Type) where
  | initial (state : Row d)
  | token (earlier : Gradient d α) (index : ℕ) (inputs : α)

/-- Apply the gradient to an input perturbation. The scale perturbation is shared over time. -/
def Gradient.apply {α : Type} (pairing : α → α → ℝ) (ds : Row d) (dx : ℕ → α) : Gradient d α → ℝ
  | .initial b => dot b ds
  | .token earlier t a => earlier.apply pairing ds dx + pairing a (dx t)

/-- The forward states serve as the reverse pass's saved activations. -/
def reverseSweep (x : Tokens d) (s : Row d) (scl : ℝ) (w : ℕ → ℝ) :
    ℕ → Row d → Gradient d (Args d)
  | 0, b => .initial b
  | t+1, b =>
    let p := pull (tokenState x s t) (atToken x scl t) (w t) b
    .token (reverseSweep x s scl w t p.1) t p.2

def tangentState (x : Tokens d) (s : Row d) (scl : ℝ) (ds : Row d) (dx : ℕ → Args d) :
    ℕ → Row d
  | 0 => ds
  | t+1 => advanceD (tokenState x s t) (tangentState x s scl ds dx t) (atToken x scl t) (dx t)

def outputD (x : Tokens d) (s : Row d) (scl : ℝ) (ds : Row d) (dx : ℕ → Args d) (t : ℕ) :=
  let y := tokenState x s (t+1)
  let dy := tangentState x s scl ds dx (t+1)
  (dx t).scale * dot y (x.query t) + scl * (dot dy (x.query t) + dot y (dx t).query)

theorem reverse_pair (x : Tokens d) (s : Row d) (scl : ℝ) (ds : Row d)
    (dx : ℕ → Args d) (w : ℕ → ℝ) (n : ℕ) (b : Row d) :
    (reverseSweep x s scl w n b).apply pair ds dx =
      (∑ t ∈ range n, w t * outputD x s scl ds dx t) + dot (tangentState x s scl ds dx n) b := by
  induction n generalizing b with
  | zero => simpa [reverseSweep, Gradient.apply, tangentState] using dot_swap b ds
  | succ n ih =>
    rw [reverseSweep, Gradient.apply, ih, sum_range_succ]
    have h := pull_correct (tokenState x s n) (tangentState x s scl ds dx n)
      (atToken x scl n) (dx n) (w n) b
    dsimp only at h
    unfold outputD
    rw [dot_swap (tangentState x s scl ds dx n)]
    rw [add_assoc, ← h, ← add_assoc]
    rfl

/-- Scalarized loss of the original block program, including its final carry. -/
def loss (x : Tokens d) (s : Row d) (scl : ℝ) (w : ℕ → ℝ) (n : ℕ) (b : Row d) :=
  (∑ t ∈ range n, w t * output x s n scl t) + dot (carry x s n scl ((n+15)/16)) b

theorem loss_eq (x : Tokens d) (s : Row d) (scl : ℝ) (w : ℕ → ℝ) (n : ℕ) (b : Row d) :
    loss x s scl w n b = (∑ t ∈ range n, w t * (scl * dot (tokenState x s (t+1)) (x.query t))) +
      dot (tokenState x s n) b := by
  unfold loss
  rw [(forward x s n scl).2]
  congr 1
  exact sum_congr rfl fun t ht => congrArg (w t * ·) ((forward x s n scl).1 t (mem_range.mp ht))

/-- The returned cotangents give the actual derivative along every differentiable input path.
Choosing coordinate directions recovers every partial derivative. -/
theorem backward {x : ℝ → Tokens d} {s : ℝ → Row d} {scl : ℝ → ℝ} {u : ℝ}
    {ds : Row d} {dx : ℕ → Args d} (w : ℕ → ℝ) (n : ℕ) (b : Row d)
    (hs : RowPath s ds u) (hx : ∀ t, Path (fun z => atToken (x z) (scl z) t) (dx t) u) :
    HasDerivAt (fun z => loss (x z) (s z) (scl z) w n b)
      ((reverseSweep (x u) (s u) (scl u) w n b).apply pair ds dx) u := by
  let states (t : ℕ) : ℝ → Row d := fun z => tokenState (x z) (s z) t
  let tang (t : ℕ) := tangentState (x u) (s u) (scl u) ds dx t
  have hstate (t) : RowPath (states t) (tang t) u := by
    induction t with
    | zero => exact hs
    | succ t ih => exact advance_deriv ih (hx t)
  have hout (t) : HasDerivAt (fun z => scl z * dot (states (t+1) z) ((x z).query t))
      (outputD (x u) (s u) (scl u) ds dx t) u :=
    (hx t).scale.mul (dot_deriv (hstate (t+1)) (hx t).query)
  have hsum := HasDerivAt.fun_sum (u := range n) (fun t _ => (hout t).const_mul (w t))
  have hb : HasDerivAt (fun z => dot (states n z) b) (dot (tang n) b) u := by
    simpa [dot, mul_zero] using! dot_deriv (hstate n)
      (show RowPath (fun _ => b) (fun _ => 0) u from fun i => hasDerivAt_const u (b i))
  simp only [loss_eq, reverse_pair]
  exact hsum.add hb

end
end FlashKda.Backward
