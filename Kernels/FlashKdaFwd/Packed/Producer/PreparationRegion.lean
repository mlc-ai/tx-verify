-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.ProducerControl

@[expose] public section
namespace FlashKda.Packed.ProducerControl
open PTX

def preparationOp : Op → Bool
  | .bra dst _ => decide (315 ≤ dst ∧ dst ≤ 1402)
  | .brx .. | .ret | .exit => false
  | _ => true

def preparationRegs : List Nat := [307,486,314,88]

def preservesDispatch (i : Instr) :=
  preparationOp i.op && preparationRegs.all fun r => !(writes i.op).contains r

def preparationWindow (pc n : Nat) :=
  (Transfers.slice pc n).map (List.all · preservesDispatch)

theorem inPreparationWindow {pc n j : Nat} {i : Instr} (h : preparationWindow pc n = some true)
    (fit : pc+n ≤ 3835) (lo : pc ≤ j) (hi : j < pc+n) (site : kernel.code[j]? = some i) :
    preservesDispatch i = true := by
  unfold preparationWindow at h
  rw [instructions fit] at h
  apply List.all_eq_true.mp (Option.some.inj h)
  apply List.mem_of_getElem?
  rw [List.getElem?_take_of_lt (show j-pc < n by omega),List.getElem?_drop,
    show pc+(j-pc)=j by omega,site]

end FlashKda.Packed.ProducerControl
