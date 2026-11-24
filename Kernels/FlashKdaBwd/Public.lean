-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaBwd.Activation
import all Mathlib.Basic.Real.Basic

/-! # The KDA backward operator on the public tensor inputs of one head
The state is indexed by value channel and then by key coordinate. Tokens sharing an input
use the same perturbation, so their gradients add by the chain rule. -/
@[expose] public section
namespace FlashKda.Backward
open Chunk Sequence Finset
noncomputable section
variable {d v : ℕ}

/-- Query, key, gate and update logits are shared across a head's value channels. -/
structure Inputs (d v : ℕ) where
  key : ℕ → Row d
  query : ℕ → Row d
  gate : ℕ → Row d
  value : ℕ → Fin v → ℝ
  logit : ℕ → ℝ
  parameter : ℝ
  bias : Row d
  lower : ℝ
  scale : ℝ
  initial : Fin v → Row d

def Inputs.raw (x : Inputs d v) (j : Fin v) (t : ℕ) : Raw d :=
  ⟨x.key t, x.query t, x.gate t, x.value t j, x.logit t, x.parameter, x.bias, x.lower, x.scale⟩

def Inputs.tokens (x : Inputs d v) (j : Fin v) :=
  activate x.query x.key x.gate (fun t => x.value t j) x.logit x.lower x.parameter x.bias

def Gradient.throughGate (raw : ℕ → Raw d) : Gradient d (Args d) → Gradient d (Raw d)
  | .initial b => .initial b
  | .token earlier t b => .token (earlier.throughGate raw) t (rawPull (raw t) b)

theorem throughGate_apply (r dr : ℕ → Raw d) (ds : Row d) (g : Gradient d (Args d)) :
    (g.throughGate r).apply rawPair ds dr =
      g.apply pair ds (fun t => activatedD (r t) (dr t)) := by
  induction g with
  | initial => rfl
  | token earlier t b ih => simp only [Gradient.throughGate, Gradient.apply, ih, raw_adjoint]

/-- A sparse representation of gradients. Each record contributes to its raw input coordinate;
entries for shared parameters use the same coordinate across tokens and value channels. -/
def rawBackward (x : Inputs d v) (w : Fin v → ℕ → ℝ) (n : ℕ) (b : Fin v → Row d)
    (j : Fin v) : Gradient d (Raw d) :=
  (reverseSweep (x.tokens j) (x.initial j) x.scale (w j) n (b j)).throughGate (x.raw j)

def publicLoss (x : Inputs d v) (w : Fin v → ℕ → ℝ) (n : ℕ) (b : Fin v → Row d) :=
  ∑ j, loss (x.tokens j) (x.initial j) x.scale (w j) n (b j)

/-- Every path through the raw inputs, every set of output and final-state weights, and every
sequence length, including zero. Gates, biases, parameters and the incoming state may all vary. -/
theorem public_backward {x : ℝ → Inputs d v} {dx : Inputs d v} {u : ℝ}
    (w : Fin v → ℕ → ℝ) (n : ℕ) (b : Fin v → Row d)
    (hx : ∀ j t, RawPath (fun z => (x z).raw j t) (dx.raw j t) u)
    (hs : ∀ j, RowPath (fun z => (x z).initial j) (dx.initial j) u) :
    HasDerivAt (fun z => publicLoss (x z) w n b)
      (∑ j, (rawBackward (x u) w n b j).apply rawPair (dx.initial j) (dx.raw j)) u := by
  apply HasDerivAt.fun_sum
  intro j _
  rw [rawBackward, throughGate_apply]
  exact backward (w j) n (b j) (hs j) (fun t => activated_deriv (hx j t))

end
end FlashKda.Backward
