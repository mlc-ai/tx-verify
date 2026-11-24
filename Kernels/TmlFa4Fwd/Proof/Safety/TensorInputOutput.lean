-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Safety.TensorInputStaging
public import Kernels.TmlFa4Fwd.Proof.Thread.OutputReadSource
import Kernels.TmlFa4Fwd.Proof.Safety.SharedOwnership

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX PTX.Proof PTX.AsyncCopy

/-- Even before the output transfer performs its read, a tensor input at the same
byte is ordered through the MMA operand and the actual correction publication. -/
theorem tensorInputBeforeOutputRead {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {input issue : EvId} {x y k column row byte addr : Nat}
    {spec : TensorStore.Spec} {a : Acc} {loc : Loc}
    (hInput : X.Intent (.async input (.write (.load x y k))) a true) (hCover : a.Covers loc)
    (hIssue : X.TensorStoreIssue issue addr spec)
    (hRead : TensorStore.readLoc spec column row byte = some loc) :
    ByteCausality l X loc (.async input (.write (.load x y k)))
      (.async issue (.read (.store column row byte))) := by
  obtain ⟨writer, _, _, hWritten, hSlot, hSpace, hOwner, hProxy⟩ :=
    Thread.Output.actualPublishedSource hp hX hIssue hRead
  have hBefore := (tensorInputBeforeOrdinaryWrite hp hX hInput hCover hWritten hSlot).2
  have hInputOwner := asyncFootprintOwnsShared hp hX hInput.2 (hCover.1.symm.trans hSpace)
  have hCta : input.1 / l.block = issue.1 / l.block :=
    hInputOwner.symm.trans (hCover.2.1.symm.trans hOwner)
  obtain ⟨s, inputAddr, hLoad, _, _⟩ := hInput.2
  obtain ⟨_, hLoad⟩ := hLoad
  obtain ⟨_, hStore⟩ := hIssue
  exact .direct (Protocol.asyncSourceBeforePublishedRead hX
    ⟨event_thread_lt hX hLoad, event_thread_lt hX hStore, hCta⟩ hBefore hProxy)

end PTX.Kernels.TmlFa4Fwd.Safety
