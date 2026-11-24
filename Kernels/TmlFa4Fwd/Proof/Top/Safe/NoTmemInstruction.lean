-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Top.Base
public import Kernels.TmlFa4Fwd.Proof.Protocol.Values.Elements
import Kernels.TmlFa4Fwd.Proof.Protocol.Values.StatReadsAll
import Kernels.TmlFa4Fwd.Proof.Lib.Guarded
import Kernels.TmlFa4Fwd.Proof.Protocol.Mbar.FaultFree
import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Issue
import Kernels.TmlFa4Fwd.Proof.Protocol.Values.Results

@[expose] public section

/-! # ERR-TC-MMA: every MMA issue is well formed

`Safe.noTmemInstruction` proves this safety class of Core's `Unsafe`. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Top
open PTX PTX.Proof

variable {p : Params} {l : Launch} {m : Mem0}

/-- **Each unmasked result of a completed MMA has a value.** -/
theorem Safe.mmaValues (hp : Pre p l m)
    {X : Execution} (hX : Consistent l kernel Assumptions.all m X) (i : EvId) (d : Nat)
    (s : TcMma.OperandSpec) (acc : Bool) (mask : List Nat) (hi : X.MmaIssue i d s acc mask) :
    TcMma.CompletedValues l Assumptions.all X i :=
  have hF := launchFollow hp hX
  Values.completedValues hp hX hF (guardedOfNoObjectFault hX (no_fault hp hX hF))
    (Values.elementFacts hp hX hF (Values.softFacts hp hX hF)) hi

/-- **ERR-TC-MMA**. -/
theorem Safe.noTmemInstruction (hp : Pre p l m) {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) :
    ¬ TcMma.InstructionUnsafe l Assumptions.all X :=
  Tm.instruction_safe hp hX (launchFollow hp hX) (Safe.mmaValues hp hX)

end PTX.Kernels.TmlFa4Fwd.Proof.Top
