-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.Machine

@[expose] public section

/-! # The election site of each elected role

The loader, MMA and scheduler warps each run their task loop on one lane, elected by a
full-mask `elect.sync` at the role's election site; the consumer warps elect no lane. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

/-- The election site of each elected role. -/
def Prologue.Role.electPc : Prologue.Role → Option Nat
  | .loader _ => some Prologue.Site.roleElect.pc
  | .mma _ => some Mma.Site.elect.pc
  | .sched _ => some Scheduler.Site.elect.pc
  | .cons _ => none

end PTX.Kernels.Fp16Gemm8192.Proof
