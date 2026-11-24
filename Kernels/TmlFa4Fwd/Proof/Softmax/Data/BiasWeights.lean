-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.BiasShift
import Tactics.KernelRfl

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
open PTX.Flow PTX.Assumption
noncomputable section
set_option maxRecDepth 100000

def biasOut (soft : Bool) (W : Nat → Value) :=
  Gen.expoBTA1_facts4 (bif soft then nextTB (lookupD (Gen.expoBB8_facts1 (vB8 W)))
    else nextTA (lookupD (Gen.expoBA_facts5 W)))

def expLane (soft : Bool) (x : Value) :=
  bif soft then Value.float .f32 (laneR x) else okVal (.bits 32 0) (ex2E true x)

theorem expLane_shift (p M x) (soft : Bool) :
    expLane soft (shifted p M x) = .float .f32 (probability p M x) := by
  cases soft
  · exact hw_exp p M x
  · exact congrArg (Value.float .f32) (sw_exp p M x)

theorem clean_shift (p M x) : Clean (shifted p M x) := by
  unfold shifted shift
  split
  · exact clean_negInf
  · exact clean_float _

private def pathPair (soft : Bool) (j : Nat) (x y : Value) : Value × Value :=
  let sw := soft && decide (22 ≤ j ∧ 6 ≤ j%8)
  let a := expLane sw x
  let b := expLane sw y
  if j < 47 then splitValue 64 (joinValue a b)
  else if j = 47 then ((splitValue 64 (joinValue a y)).1, b)
  else let xy := splitValue 64 (joinValue x y)
       (expLane false xy.1, expLane false xy.2)

/-- The probabilities retained for the sum, before BF16 conversion. -/
def biasLanes (V : Nat → Value) (j : Nat) : Value × Value :=
  if j < 47 then splitValue 64 (V (if j < 32 then 9573+j else 9541+(j-32)))
  else if j = 47 then (V 4905, V 7252)
  else (V (4827+4*(j-48)), V (4828+4*(j-48)))

private theorem routing (soft : Bool) (W : Nat → Value) {j : Nat} (hj : j < 64) :
    biasLanes (lookupD (biasOut soft W)) j =
      pathPair soft j (W (1363+2*j)) (W (1363+2*j+1)) := by
  apply atColumn (f := biasLanes (lookupD (biasOut soft W)))
    (g := fun j => pathPair soft j (W (1363+2*j)) (W (1363+2*j+1))) hj
  cases soft <;> kernel_rfl

private theorem path_eval (p M x y) (soft : Bool) (j : Nat) :
    pathPair soft j (shifted p M x) (shifted p M y) =
      (.float .f32 (probability p M x), .float .f32 (probability p M y)) := by
  unfold pathPair
  simp only [expLane_shift]
  split
  · rfl
  split
  · rw [split_join_clean (clean_float _) (clean_shift p M y)]
  · rw [split_join_clean (clean_shift p M x) (clean_shift p M y)]
    exact congrArg₂ Prod.mk (expLane_shift p M x false) (expLane_shift p M y false)

theorem bias_weights {p L m} (hp : Pre p L m) (g v) {j : Nat} (hj : j < 64) :
    biasLanes (lookupD (tailB p L g v)) j =
      (.float .f32 (P p L g v .bias (2*j)), .float .f32 (P p L g v .bias (2*j+1))) := by
  let sw := Epilogue.scmp .lt .u v.bt (r301 p L g v)
  change biasLanes (lookupD (biasOut sw (vExpoB p L g v))) j = _
  have h := bias_shift hp g v hj
  rw [routing sw _ hj, (Prod.mk.inj h).1, (Prod.mk.inj h).2]
  exact path_eval p _ _ _ sw j

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Data
