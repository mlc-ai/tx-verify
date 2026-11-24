-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaBwd.Sequence
public import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Analysis.Calculus.Deriv.Inv
import all Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Derivatives of the query/key normalization and the bounded gate in FlashKDA -/
@[expose] public section
namespace FlashKda.Backward
open Chunk Algorithm Finset
noncomputable section
variable {d : ℕ}

def sigmoidSlope (x : ℝ) := sigmoid x * (1 - sigmoid x)

theorem sigmoid_deriv {f : ℝ → ℝ} {u df : ℝ} (h : HasDerivAt f df u) :
    HasDerivAt (fun t => sigmoid (f t)) (sigmoidSlope (f u) * df) u := by
  simpa [sigmoidSlope, sigmoid, Real.sigmoid, Function.comp_def] using!
    (Real.hasDerivAt_sigmoid (f u)).comp u h

def radius (x : Row d) := Real.sqrt (dot x x + 1 / 1000000)
def normD (x dx : Row d) :=
  add (scaleRow (1 / radius x) dx) (scaleRow (-dot x dx / (radius x)^3) x)

theorem norm_self_adjoint (x dx b : Row d) : dot b (normD x dx) = dot (normD x b) dx := by
  rw [dot_swap b]
  unfold normD
  simp only [dot_add, dot_scale]
  rw [dot_swap dx b]
  ring

theorem norm_deriv {x : ℝ → Row d} {dx : Row d} {u : ℝ} (h : RowPath x dx u) :
    RowPath (fun t => normalize (x t)) (normD (x u) dx) u := by
  have sq : 0 ≤ dot (x u) (x u) := sum_nonneg fun i _ => mul_self_nonneg _
  have pos : 0 < dot (x u) (x u) + 1 / 1000000 := by positivity
  have hn : radius (x u) ≠ 0 := (Real.sqrt_pos.2 pos).ne'
  have hd := ((dot_deriv h h).add_const (1 / 1000000 : ℝ)).sqrt pos.ne'
  intro i
  apply ((h i).fun_div hd hn).congr_deriv
  change (dx i * radius (x u) - x u i * _) / (radius (x u))^2 = _
  unfold normD add scaleRow
  rw [dot_swap dx (x u)]
  change (dx i * radius (x u) - x u i *
    ((dot (x u) dx + dot (x u) dx) / (2 * radius (x u)))) / (radius (x u))^2 = _
  field_simp
  ring

/-- Public inputs at one token and one value channel. Bias, parameter, lower bound and scale
are shared by all times at a head; the raw pairing accumulates their contributions. -/
structure Raw (d : ℕ) where
  key : Row d
  query : Row d
  gate : Row d
  value : ℝ
  logit : ℝ
  parameter : ℝ
  bias : Row d
  lower : ℝ
  scale : ℝ

def activated (r : Raw d) : Args d :=
  ⟨normalize r.key, normalize r.query, logGate r.lower r.parameter r.bias r.gate,
    r.value, sigmoid r.logit, r.scale⟩

def gateInput (r : Raw d) (i : Fin d) := Real.exp r.parameter * (r.gate i + r.bias i)
def gateSlope (r : Raw d) (i : Fin d) :=
  r.lower * sigmoidSlope (gateInput r i) * Real.exp r.parameter

def activatedD (r dr : Raw d) : Args d where
  key := normD r.key dr.key
  query := normD r.query dr.query
  value := dr.value
  strength := sigmoidSlope r.logit * dr.logit
  scale := dr.scale
  logDecay i := dr.lower * sigmoid (gateInput r i) +
    gateSlope r i * (dr.gate i + dr.bias i + (r.gate i + r.bias i) * dr.parameter)

def rawPull (r : Raw d) (b : Args d) : Raw d where
  key := normD r.key b.key
  query := normD r.query b.query
  gate := had b.logDecay (gateSlope r)
  bias := had b.logDecay (gateSlope r)
  parameter := dot (had b.logDecay (gateSlope r)) (add r.gate r.bias)
  lower := dot b.logDecay (fun i => sigmoid (gateInput r i))
  value := b.value
  logit := b.strength * sigmoidSlope r.logit
  scale := b.scale

def rawPair (b dr : Raw d) : ℝ :=
  dot b.key dr.key + dot b.query dr.query + dot b.gate dr.gate + dot b.bias dr.bias +
    b.parameter * dr.parameter + b.lower * dr.lower + b.value * dr.value +
    b.logit * dr.logit + b.scale * dr.scale

theorem raw_adjoint (r dr : Raw d) (b : Args d) :
    pair b (activatedD r dr) = rawPair (rawPull r b) dr := by
  have hg : dot b.logDecay (activatedD r dr).logDecay =
      dot (rawPull r b).gate dr.gate + dot (rawPull r b).bias dr.bias +
      (rawPull r b).parameter * dr.parameter + (rawPull r b).lower * dr.lower := by
    simp only [rawPull, activatedD, dot, add, had, sum_mul, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    ring
  unfold pair rawPair
  rw [hg]
  dsimp only [activatedD, rawPull]
  rw [norm_self_adjoint, norm_self_adjoint]
  ring

structure RawPath (r : ℝ → Raw d) (dr : Raw d) (u : ℝ) : Prop where
  key : RowPath (fun t => (r t).key) dr.key u
  query : RowPath (fun t => (r t).query) dr.query u
  gate : RowPath (fun t => (r t).gate) dr.gate u
  bias : RowPath (fun t => (r t).bias) dr.bias u
  value : HasDerivAt (fun t => (r t).value) dr.value u
  logit : HasDerivAt (fun t => (r t).logit) dr.logit u
  parameter : HasDerivAt (fun t => (r t).parameter) dr.parameter u
  lower : HasDerivAt (fun t => (r t).lower) dr.lower u
  scale : HasDerivAt (fun t => (r t).scale) dr.scale u

theorem activated_deriv {r : ℝ → Raw d} {dr : Raw d} {u : ℝ} (h : RawPath r dr u) :
    Path (fun t => activated (r t)) (activatedD (r u) dr) u := by
  refine ⟨norm_deriv h.key, norm_deriv h.query, ?_, h.value, sigmoid_deriv h.logit, h.scale⟩
  intro i
  have hp := h.parameter.exp.mul ((h.gate i).add (h.bias i))
  apply (h.lower.mul (sigmoid_deriv hp)).congr_deriv
  simp only [Pi.add_apply, Pi.mul_apply, activatedD, gateSlope, gateInput]
  ring

end
end FlashKda.Backward
