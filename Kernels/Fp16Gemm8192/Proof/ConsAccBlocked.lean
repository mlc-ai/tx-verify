-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Progress.ConsAccExport
public import Kernels.Fp16Gemm8192.Proof.Protocol.TmemRing.ConsExport
public import Kernels.Fp16Gemm8192.Proof.Protocol.ClcRing.Readers
public import Kernels.Fp16Gemm8192.Proof.Region.Accessors

@[expose] public section

/-! # The consumer's accumulator-full blocker is proved

This file sits at the top of the proof tree, outside the layer order: the conclusion layers see the
lower layers only through `Interface.lean` (`tests/test_proof_lint.py`), so the protocol export is
instantiated here, where both the protocol and the progress layer are visible.

`ConsAccBlocked` (`Progress/AccWaits.lean`) follows from the protocol export `ConsAccBlockedX`
(`Protocol/TmemRing/ConsExport.lean`), whose CLC reader facts (`readerValues`) take the region
layer's response writers (`Region.responseWriters`). The thread facts and the no-UB premise are the
same as the accumulator wait classes take. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

/-- **The consumer's accumulator-full blocker** (`ConsAccBlocked`). -/
theorem cons_acc_blocked_proved {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0)
    (hF : ∀ Y : Execution, Consistent L kernel Prod mem0 Y → ThreadFacts L Y)
    (hub : ∀ Y : Execution, Consistent L kernel Prod mem0 Y → ∀ g k pc f,
      Y.get (g, k) ≠ some ⟨pc, .ub f⟩) :
    Progress.ConsAccBlocked L mem0 :=
  Progress.cons_acc_blocked_of_export hub fun Y hY hub' =>
    TmemRing.cons_acc_blocked_x hpre hY (hF Y hY)
      (ClcRing.readerValues hpre hY (hF Y hY) (Region.responseWriters hpre hY (hF Y hY))) hub'

end
end PTX.Kernels.Fp16Gemm8192.Proof
