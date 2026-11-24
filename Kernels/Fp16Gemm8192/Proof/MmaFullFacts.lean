-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.MmaFull
public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.FullBlocker
public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.Readers
public import Kernels.Fp16Gemm8192.Proof.Region.Accessors
public import Kernels.Fp16Gemm8192.Proof.Protocol.Exit.ClusterAll
public import Kernels.Fp16Gemm8192.Proof.Thread.Facts

@[expose] public section

/-! # The MMA full blocker's facts are instantiated

This file sits at the top of the proof tree, outside the layer order (as `ConsAccBlocked.lean`
does): the progress layer sees the protocol exports only through `MmaFullFacts`, and this file
instantiates it with the proved exports. The thread facts (`threadFacts`), the input-full blocker
(`InputRing.inputFullBlocked`), the cluster's exit (`clusterExitAll`) are proved; the CLC readers'
agreement (`ClcRing.allResponsesAgree`) takes the region layer's response writers, and the no-UB
premise is the safety fact. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

/-- **The MMA full blocker's per-execution facts, instantiated.** -/
theorem mma_full_facts_proved {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0)
    (hub : ∀ Y : Execution, Consistent L kernel Prod mem0 Y → ¬ HasUb Y) :
    Progress.MmaFullFacts L mem0 where
  ub := hub
  thread := fun _ hY => threadFacts hpre hY
  inputFull := fun _ hY => InputRing.inputFullBlocked hpre hY (threadFacts hpre hY)
  agree := fun _ hY => ClcRing.allResponsesAgree hpre hY (threadFacts hpre hY)
    (Region.responseWriters hpre hY (threadFacts hpre hY))
  clusterAll := fun _ hY => clusterExitAll hpre hY (threadFacts hpre hY)

end

end PTX.Kernels.Fp16Gemm8192.Proof
