-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.OutputDrain
import Kernels.TmlFa4Fwd.Proof.Thread.OutputReadSource
import Kernels.TmlFa4Fwd.Proof.Thread.SharedScratchWrites
import Kernels.TmlFa4Fwd.Proof.Thread.TerminalStatisticsWrites

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Output
open PTX PTX.AsyncCopy

private theorem cacheWriteLength {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {a : Acc} {bs : List Byte}
    (hw : X.MemWrites (.async i (.write .copy)) a bs) : bs.length = a.size := by
  obtain ⟨s, hCopy, hWhole, rfl, hw⟩ := hw
  have hShape := actualCopyShape hX hCopy
  have hPresent : AsyncCopy.nonempty (X.async.copies i) := ⟨.write .copy, by simp [present, hw]⟩
  obtain ⟨spec, hIssue, hOk⟩ := hX.tma.1 i hPresent
  have hSame := Execution.Copy.unique (issuedBy_some.mp hIssue) hCopy
  subst spec
  have hSource := hOk.2.2.1 bs hw
  rw [hWhole] at hSource
  unfold sourceBytes at hSource
  rw [hShape.noData] at hSource
  obtain ⟨read, hRead, rfl⟩ := Option.map_eq_some_iff.mp hSource
  simp only [List.length_append, List.length_replicate, (hOk.2.1 read hRead).2]
  exact Nat.add_sub_of_le hOk.1

/-- Each pending O read has a visible performed producer. Every performed competitor that
could be selected by a read supplies an actual byte at the requested slot. -/
theorem actualVisibleReadSources {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {address : Nat} {spec : TensorStore.Spec}
    (hi : X.TensorStoreIssue i address spec) : Step.StoreDone.VisibleReadSources l X i spec := by
  intro slot dest _
  let loc := spec.sharedLoc slot
  have hLoc : TensorStore.readLoc spec slot.1.val slot.2.1.val slot.2.2.val = some loc := by
    simp [TensorStore.readLoc, TensorCopy.slotAt_self, loc]
  obtain ⟨writer, dst, data, hw, hc, hSpace, _, hVisible⟩ :=
    Thread.Output.actualPublishedSource hp hX hi hLoc
  obtain ⟨stage, box, _, hx, hy, hk, hAt⟩ := Thread.Output.actualReadySlot hp hX hi hLoc
  have hAbove : l.sharedBase + 3072 ≤ loc.addr := by
    have hSlot := hAt.symm ▸ Acc.covers_at hk
    have hRange := Thread.Output.elementStageRange hx hy hSlot
    omega
  refine ⟨⟨.thread writer, dst, data, .inl hw, hc, .direct hVisible⟩, ?_⟩
  intro other a bytes hOther hCover _
  have hLength : bytes.length = a.size := by
    rcases Thread.sharedWriteSource hX hOther hCover hSpace with
      ⟨j, rfl, hWrite⟩ | ⟨input, x, y, k, rfl⟩ | ⟨copy, s, rfl, _, rfl⟩
    · rcases Thread.ordinarySharedWriteBelowOrStaging hp hX hWrite hCover hSpace with
        hLow | hStaging
      · change loc.addr < l.sharedBase + 3072 at hLow
        omega
      · exact hStaging.length_eq_size hX
    · obtain ⟨_, _, value, _, _, _, _, hSize, rfl, _, _, _, _⟩ := hOther
      simp [hSize]
    · exact cacheWriteLength hX hOther
  have hIndex : loc.addr - a.loc.addr < bytes.length := by
    have hLow : a.loc.addr ≤ loc.addr := hCover.2.2.1
    have hEnd : loc.addr < a.loc.addr + a.size := hCover.2.2.2
    omega
  exact ⟨bytes[loc.addr - a.loc.addr], List.getElem?_eq_getElem hIndex⟩

/-- Once the output issuer has issued a box, all its backed source bytes can be read
and its writes can finish in a maximal execution with guarded synchronization. -/
theorem actualStoreFullyDone {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {i : EvId} {address : Nat} {spec : TensorStore.Spec}
    (hi : X.TensorStoreIssue i address spec) (hGuarded : SyncGuarded l kernel X) :
    X.AsyncPresent i .fullDone :=
  storeFullyDoneOfVisibleSources hMax hi (actualVisibleReadSources hp hMax.1 hi) hGuarded

end PTX.Kernels.TmlFa4Fwd.Protocol.Output
