-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Top.Prog.QTmaPoll
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Guarded

@[expose] public section

/-! # Synchronization is guarded in a safe launch

The premise `SyncGuarded` of the library's asynchronous and released-lane steps
(`Sched.store_stepsQ`, `Sched.mma_steps_cpQ`, `Descent.NextEnvQ.guard`): the objects' records are
fault-free by safety (`Prog.fault_free`) and the program has no releasing store, atomic or thread
fence and spins at every poll (`guardedOfNoObjectFault`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
open PTX

variable {L : Launch} {m : Mem0}

/-- **Synchronization is guarded** in a consistent execution of a safe launch. -/
theorem Prog.guarded (hs : SafeGoal kernel Assumptions.all L m) {X : Execution}
    (hX : Consistent L kernel Assumptions.all m X) : SyncGuarded L kernel X :=
  guardedOfNoObjectFault hX fun l r hr => Prog.fault_free hs hX l r hr

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Top
