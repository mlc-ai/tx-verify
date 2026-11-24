-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.Decode.Source
public meta import Kernels.FlashKdaFwd.Packed.Decode.Source
public meta import Lean.Elab.Term
public meta import Lean.ToExpr
public import Tactics.KernelRfl
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import all Init.Data.ToString.Extra
import all Init.Data.Repr

@[expose] public section
namespace FlashKda.Packed.Prologue
open PTX
set_option maxRecDepth 60000
set_option maxHeartbeats 0

def param (i : Nat) : String :=
  let header := Generated.FlashKdaPacked.module.functions[0]!.header
  let token := if i < 11 then 8+9*i else [108,112,116,120,127,131].getD (i-11) 0
  header.getD token ""
meta section
open Lean
elab "stemChars%" : term => do
  return toExpr <|
    ((Generated.FlashKdaPacked.module.functions[0]!.name ++ "_param_").toList)
end
private def stem : List Char := stemChars%
private theorem spell (i : Fin 17) :
    param i.val = String.ofList (stem ++ (toString i.val).toList) := by
  fin_cases i <;> kernel_rfl
theorem param_injective {i j : Fin 17} (h : i ≠ j) : param i.val ≠ param j.val := by
  intro eq
  rw [spell,spell] at eq
  have suffix := List.append_cancel_left (String.ofList_inj.mp eq)
  have same := congrArg String.ofList suffix
  simp only [String.ofList_toList] at same
  have inj : ∀ a b : Fin 17, decide (toString a.val = toString b.val) = decide (a=b) := by
    decide +kernel
  exact h (of_decide_eq_true ((inj i j).symm.trans (decide_eq_true same)))

def topBindings : List Decode.Binding :=
  (Decode.scopeBindings Generated.FlashKdaPacked.module.functions[0]!.body [] "").toOption.getD []

private theorem unbound (cs : List Char) : Decode.findBinding topBindings ('_' :: cs) = none := by
  kernel_rfl

theorem resolvedParam (i : Fin 17) :
    Decode.resolveOperand topBindings (.symbol (param i.val)) = .symbol (param i.val) := by
  have first : (param i.val).toList = '_' :: (stem.tail ++ (toString i.val).toList) := by
    rw [spell, String.toList_ofList]
    rfl
  unfold Decode.resolveOperand
  rw [first, unbound]

end FlashKda.Packed.Prologue
