-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.OutputSourceLane
public import Kernels.TmlFa4Fwd.Proof.MbarAddressClosure
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpStartup
public import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
public import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
public import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
public import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
public import Kernels.TmlFa4Fwd.Proof.OutputFrame
public import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
public import Lemmas.Flow.NotClc
public import Lemmas.Step.CtaBar
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
public import Kernels.TmlFa4Fwd.Proof.RoleDispatch
public import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
public import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
public import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
public import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
public import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
public import Lemmas.Flow.TcTmpl
public import Lemmas.TensorStore.TensorStoreThread
public import Lemmas.Flow.BulkCount
public import Mathlib.Data.List.NodupEquivFin
public import Kernels.TmlFa4Fwd.Proof.CorrectionReadySources
public import Kernels.TmlFa4Fwd.Proof.Thread.OutputSlotGeometry
public import Kernels.TmlFa4Fwd.Proof.Thread.TensorForms
public import Kernels.TmlFa4Fwd.Proof.SoftmaxNumerics
public import Lemmas.Step.BulkWaitReady

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Output
open PTX PTX.Proof AsyncCopy Correction Epilogue

noncomputable section

/-- Other writes covering the slot are earlier in the correction lane, already ordered before
the chosen write, or ordered after the source read by the reuse protocol. -/
def CoveringWritesOrder (l : Launch) (X : Execution) (reader : Ref)
    (loc : Loc) (writer : EvId) : Prop :=
  ∀ other a bs, X.MemWrites other a bs → a.Covers loc →
    (∃ index ≤ writer.2, other = .thread (writer.1, index)) ∨
      ByteCausality l X loc other (.thread writer) ∨ ByteCausality l X loc reader other

variable {l : Launch} {m : Mem0}

/-- The physical source slot has an ordered ordinary writer carrying the expected byte. -/
def OrderedSlot (l : Launch) (X : Execution) (i : EvId) (spec : TensorStore.Spec)
    (column row k : Nat) (expected : Byte) : Prop :=
  ∃ src writer a bs, TensorStore.readLoc spec column row k = some src ∧
    SourceOrdered l X (.async i (.read (.store column row k))) src (.thread writer) a bs ∧
      wbyte a bs src = some expected

private theorem writesAccess {X : Execution} {i : EvId} {a : Acc} {bs : List Byte}
    (hw : X.MemWrites (.thread i) a bs) : X.Access i a true := by
  rcases hw with hw | ⟨old, hw⟩
  · exact hw.access
  · exact .inr (.inr ⟨old, _, hw⟩)

theorem coveringOrder {l : Launch} {X : Execution} {reader : Ref}
    {src : Loc} {i : EvId} {a : Acc} {bs : List Byte}
    (hw : X.Writes i a bs) (hc : a.Covers src)
    (hOrder : CoveringWritesOrder l X reader src i) :
    ∀ other fp bs', X.MemWrites other fp bs' → fp.Covers src →
      other = .thread i ∨ ByteCausality l X src other (.thread i) ∨
        ByteCausality l X src reader other := by
  intro other fp bs' ho hp
  rcases hOrder other fp bs' ho hp with ⟨index, hBefore, rfl⟩ | hOrdered
  · rcases Nat.lt_or_eq_of_le hBefore with hLt | hEq
    · exact .inr (.inl (.direct (.inl (.single (.inl (po_of_overlap (writesAccess ho) hw.access
        rfl hLt ⟨src, hp, hc⟩))))))
    · left
      rw [hEq]
  · exact .inr hOrdered

private theorem observationSpec {X : Execution} (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {addr : Nat} {spec : TensorStore.Spec} {o : TensorStore.Observation}
    (hIssue : X.TensorStoreIssue i addr spec) (ho : X.tensorStores i = some o) :
    o.spec = spec := by
  obtain ⟨_, ⟨_, hObserved⟩⟩ := (hX.store i o ho).1
  obtain ⟨_, hIssued⟩ := hIssue
  rw [hIssued] at hObserved
  exact (Kind.tensorStore.inj (Event.mk.inj (Option.some.inj hObserved)).2).2.symm

/-- A performed tensor read returns the ordered source byte even before the destination
write is recorded. -/
theorem OrderedSlot.readByte {X : Execution} (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {addr column row k : Nat} {spec : TensorStore.Spec} {o : TensorStore.Observation}
    {actual expected : Byte} (hIssue : X.TensorStoreIssue i addr spec)
    (ho : X.tensorStores i = some o) (hRead : TensorStore.readByte o column row k = some actual)
    (hSlot : OrderedSlot l X i spec column row k expected) : actual = expected := by
  obtain ⟨src, writer, a, written, hLoc, hSrc, hByte⟩ := hSlot
  have hs := observationSpec hX hIssue ho
  have hMem : X.MemReads (.async i (.read (.store column row k))) {loc := src, size := 1}
      [some actual] := ⟨o, addr, actual, ho, hs.symm ▸ hIssue, hs.symm ▸ hLoc,
        hRead, rfl, rfl⟩
  obtain ⟨hWrite, hCover, hVisible, hOrder⟩ := hSrc
  have hVal := read_byte_of_last_write_ordered hX hMem Nat.one_pos hWrite
    (by simpa [Loc.at] using hCover) (by simpa [Loc.at] using hVisible)
    (by simpa [Loc.at] using hOrder)
  simpa [Loc.at, hByte] using hVal

/-- A performed O write carries the ordered FP32 source byte. -/
theorem OrderedSlot.writeByte {X : Execution} (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {addr column row k : Nat} {spec : TensorStore.Spec} {o : TensorStore.Observation}
    {actual expected : Byte} (hIssue : X.TensorStoreIssue i addr spec)
    (ho : X.tensorStores i = some o) (hWrite : TensorStore.writeByte o column row k = some actual)
    (hSlot : OrderedSlot l X i spec column row k expected) : actual = expected := by
  have hs := observationSpec hX hIssue ho
  have hReduce := hs.symm ▸ (Thread.actualTensorStoreForm hX hIssue).2.2
  exact hSlot.readByte hX hIssue ho (TensorStore.writeByte_read (hX.store i o ho).2.2 hReduce
    hWrite).1

end
end PTX.Kernels.TmlFa4Fwd.Protocol.Output
