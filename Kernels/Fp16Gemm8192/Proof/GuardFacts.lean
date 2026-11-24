-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Safety.Tma
public import Kernels.Fp16Gemm8192.Proof.Thread.Facts
public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Complete
public import Kernels.Fp16Gemm8192.Proof.Protocol.TmemRing.Joint
public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.Joint

@[expose] public section

/-! # Guarded synchronization

Every consistent execution of the kernel has guarded synchronization (`SyncGuarded`): from the
code, every position spins and no write releases; from the rings, no mbarrier record faults
(`Safety.syncGuarded`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **A consistent execution's synchronization is guarded.** -/
theorem sync_guarded (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) :
    SyncGuarded L kernel X :=
  have ht := threadFacts hpre hX
  Safety.syncGuarded hpre hX ht (inputFacts hpre hX ht) (tmemFacts hpre hX ht)
    (clcFacts hpre hX ht)

end
end PTX.Kernels.Fp16Gemm8192.Proof
