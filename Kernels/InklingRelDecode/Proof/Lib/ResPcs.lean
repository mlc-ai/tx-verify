-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Assumptions
public import Lemmas.Flow.OpPcsFast
public import Lemmas.Flow.Resource
public import Lemmas.Flow.NotClc

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX

open PTX.Flow

def resPcs : List Nat := [11, 15, 2851, 2854]

/-- **The kernel's paired Tensor Memory instructions are at four positions.** -/
theorem kernel_res_pcs : OpPcsFast kernel.code tmemOp resPcs = true := by decide +kernel

/-- A `ret` or `exit` instruction. -/
def isRet : Op → Bool
  | .ret => true
  | .exit => true
  | _ => false

/-- The position of the kernel's return. -/
def retPcs : List Nat := [2855]

/-- **The kernel's only return is at pc 2855.** -/
theorem kernel_ret_pcs : OpPcsFast kernel.code isRet retPcs = true := by decide +kernel

/-- The positions of both lists. -/
def specialPcs : List Nat := resPcs ++ retPcs

/-- A resource event's instruction is at a position of `resPcs`. -/
theorem res_pc' {g : Nat} {t : TState} {pc : Nat} {ins : Instr} {e : Event} {o : Option TState}
    (hc : kernel.code[pc]? = some ins)
    (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) e o) {grp : CtaGroup}
    {dst : Option Loc} {act : Tmem.Request} (hk : e.kind = .tc (.resource grp dst act)) :
    pc ∈ resPcs :=
  OpPcsFast.mem kernel_res_pcs hc (fires_resource_op hf hk)

/-- A resource event's instruction is at a special position. -/
theorem res_pc {g : Nat} {t : TState} {pc : Nat} {ins : Instr} {e : Event} {o : Option TState}
    (hc : kernel.code[pc]? = some ins)
    (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) e o) {grp : CtaGroup}
    {dst : Option Loc} {act : Tmem.Request} (hk : e.kind = .tc (.resource grp dst act)) :
    pc ∈ specialPcs :=
  List.mem_append_left _ (res_pc' hc hf hk)

/-- An exit event's instruction is the return. -/
theorem ret_pc' {g : Nat} {t : TState} {pc : Nat} {ins : Instr} {e : Event} {o : Option TState}
    (hc : kernel.code[pc]? = some ins)
    (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) e o) (hk : e.kind = .exit) :
    pc ∈ retPcs := by
  refine OpPcsFast.mem kernel_ret_pcs hc ?_
  rcases fires_exit_op hf hk with h | h <;> rw [h] <;> rfl

/-- An exit event's instruction is at a special position. -/
theorem ret_pc {g : Nat} {t : TState} {pc : Nat} {ins : Instr} {e : Event} {o : Option TState}
    (hc : kernel.code[pc]? = some ins)
    (hf : Fires pc (eventTmpl Assumptions.all L g t ins.op) e o) (hk : e.kind = .exit) :
    pc ∈ specialPcs :=
  List.mem_append_right _ (ret_pc' hc hf hk)

end PTX.Kernels.InklingRelDecode.Proof.Lib
