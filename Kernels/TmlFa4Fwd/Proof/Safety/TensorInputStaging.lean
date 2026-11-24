-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.TensorInputReuse
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStagingSetup
import Kernels.TmlFa4Fwd.Proof.Thread.QueryOutputBank
import Kernels.TmlFa4Fwd.Proof.Thread.SharedScratchWrites

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX PTX.AsyncCopy

/-- A pending or performed tensor input and any ordinary write to the same shared byte
are ordered. The overlap is necessarily a stage-zero output staging write. -/
theorem tensorInputBeforeOrdinaryWrite {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {input writer : EvId} {loc : Loc} {a dst : Acc} {data : List Byte} {x y byte : Nat}
    (hInput : X.Intent (.async input (.write (.load x y byte))) a true)
    (hSrc : a.Covers loc) (hWrite : X.Writes writer dst data) (hDst : dst.Covers loc) :
    X.AsyncPresent input (.write (.load x y byte)) ∧
      ByteCausality l X loc (.async input (.write (.load x y byte))) (.thread writer) := by
  obtain ⟨hShared, hLow⟩ := Thread.tensorInputWriteAboveScratch hp hX hInput hSrc
  obtain hBelow | hStage := Thread.ordinarySharedWriteBelowOrStaging hp hX hWrite hDst hShared
  · omega
  obtain ⟨stage, subbox, column, row, hx, hy, rfl, hStore⟩ := hStage.element hp hX
  exact (Protocol.tensorIntentBeforeStagingElement hp hX hInput hSrc hx hy hStore hDst).2

end PTX.Kernels.TmlFa4Fwd.Safety
