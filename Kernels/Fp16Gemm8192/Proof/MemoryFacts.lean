-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Safety.Memory
public import Kernels.Fp16Gemm8192.Proof.Region.Window
public import Kernels.Fp16Gemm8192.Proof.Region.Base
public import Kernels.Fp16Gemm8192.Proof.Region.Response
public import Kernels.Fp16Gemm8192.Proof.Protocol.InputRing.Ordered
public import Kernels.Fp16Gemm8192.Proof.Protocol.OutputRing.Safe
public import Kernels.Fp16Gemm8192.Proof.Protocol.Exit.Order
public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.PartitionTiles
public import Kernels.Fp16Gemm8192.Proof.Thread.Facts

@[expose] public section

/-! # The memory branches of `Unsafe`

This file sits at the top of the proof tree, outside the layer order (as `ProgressFacts.lean` does):
it supplies the safety layer's memory branches (`Safety.Memory`) with the region layer's exports
(the shared window, the base word and response buffer orders) and the protocols' (the input and
output rings' orders, the output tiles' uniqueness), all from the thread facts. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof

noncomputable section

namespace Memory

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- Every byte's conflicting accesses are ordered. -/
theorem conflicts_ordered (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) :
    ConflictsOrdered L X fun _ => True :=
  have ht := threadFacts hpre hX
  Safety.Memory.conflicts_ordered hpre hX ht (Region.sharedWindow hpre hX ht)
    (Region.baseOrdered hpre hX ht) (Region.responseOrdered hpre hX ht)
    (InputRing.inputOrdered hpre hX ht (Region.inputAccessors hpre hX ht))
    (OutputRing.stagingOrdered hpre hX ht
      (ClcRing.allResponsesAgree hpre hX ht (Region.responseWriters hpre hX ht))
      (Region.stagingAccessors hpre hX ht))
    (ClcRing.outputUnique hpre hX ht
      (ClcRing.readerValues hpre hX ht (Region.responseWriters hpre hX ht)))

/-- **No race.** -/
theorem no_race (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) :
    ¬ Race L X :=
  (conflicts_ordered hpre hX).no_race

/-- **No mixed-size conflict.** -/
theorem no_mixed (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) : ¬ Mixed L X :=
  (conflicts_ordered hpre hX).no_mixed

/-- **Every touched byte is allocated.** -/
theorem no_unalloc (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) :
    ¬ Unalloc mem0 X :=
  have ht := threadFacts hpre hX
  Safety.Memory.no_unalloc hpre hX ht (Region.sharedWindow hpre hX ht)

end Memory

end

end PTX.Kernels.Fp16Gemm8192.Proof
