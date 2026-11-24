-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBTKA
public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBTKB
public import Kernels.TmlFa4Fwd.Proof.Softmax.Gen.RsumB
import Tactics.KernelRfl
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # Start kinds for the bias round’s row sum -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- Registers carried by the exponent paths into the bias round's row sum. -/
def rsumBaKeys : List Nat := (Gen.rsumBa_facts0 fun _ => .pred false).map Prod.fst

def sumK (r : Nat) : Kd := if 9541 ≤ r then .pr .fl else .s .fl

/-- The rescale starts from finite scalar and pair registers. -/
def rsumBaK0 : List (Nat × Kd) := kList rsumBaKeys sumK

def checkSumKind (K : Nat → Kd) (r : Nat) : Bool :=
  match K r with
  | .s k => decide (r < 9541) && k.le .fl
  | .pr k => decide (9541 ≤ r) && k.le .fl
  | _ => false

theorem asSumKind {k : Kd} {x : Value} {r : Nat} (h : k.Has x)
    (hcheck : checkSumKind (fun _ => k) r = true) :
    (sumK r).Has x := by
  cases k with
  | no | h16 => cases hcheck
  | s k =>
    obtain ⟨hr, hk⟩ := band_split (by simpa only [checkSumKind] using hcheck)
    have hn : ¬ 9541 ≤ r := Nat.not_le_of_lt (of_decide_eq_true hr)
    simp only [sumK, ite_eq_right hn]
    exact SK.mono hk h
  | pr k =>
    obtain ⟨hr, hk⟩ := band_split (by simpa only [checkSumKind] using hcheck)
    simp only [sumK, ite_eq_left (of_decide_eq_true hr)]
    exact ⟨h.1, SK.mono hk h.2.1, SK.mono hk h.2.2⟩

theorem rsumBa_facts0_eq (W : Nat → Value) :
    Gen.rsumBa_facts0 W = factsFrom rsumBaKeys W := by kernel_rfl

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
