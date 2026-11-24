-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Faults

@[expose] public section

/-! # The input ring's facts

The input ring's interface (`InputFacts`) holds in every execution whose threads have the
thread facts: every record of a slot's barriers is fault-free (`InputRing.fault_free`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX AsyncCopy MBarrier

theorem inputFacts {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} (hpre : Pre P L mem0)
    (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) :
    InputFacts L X :=
  ⟨fun hm _ hr => InputRing.fault_free hpre hX ht hm hr⟩

end PTX.Kernels.Fp16Gemm8192.Proof
