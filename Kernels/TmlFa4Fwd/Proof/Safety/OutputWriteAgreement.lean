-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Safety.LseConflicts
public import Kernels.TmlFa4Fwd.Proof.Safety.Metadata
public import Kernels.TmlFa4Fwd.Proof.Safety.SharedConflicts
public import Kernels.TmlFa4Fwd.Proof.Protocol.OutputScratchSource
import Kernels.TmlFa4Fwd.Proof.Protocol.OutputCoordinates
public import Kernels.TmlFa4Fwd.Proof.Protocol.SelectedCacheOutputOrder
import Kernels.TmlFa4Fwd.Proof.Thread.OutputReadSource
import Lemmas.TensorStore.SourceBytes
import Kernels.TmlFa4Fwd.Proof.OutputStoreFacts

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX Epilogue
open Protocol.Output

/-- Two output boxes writing one global byte carry the same published correction byte. -/
theorem outputWriteAgreement {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X)
    (hExtent : ∀ final output, Thread.SecondOutputCommit X final output →
      final.1 / l.block < tilePrefix p p.batch * p.heads →
      Nonempty (Thread.Mma.SelectedCacheExtent l p X final))
    {i j : EvId} {x y k x' y' k' : Nat} {a b : Acc} {data₁ data₂ : List Byte} {dst : Loc}
    (hi : X.MemWrites (.async i (.write (.store x y k))) a data₁)
    (hj : X.MemWrites (.async j (.write (.store x' y' k'))) b data₂)
    (ha : a.Covers dst) (hb : b.Covers dst) :
    data₁ = data₂ := by
  obtain ⟨o, addr, v, hO, hIssue, hWrite, hByte, hSize, rfl, _⟩ := hi
  obtain ⟨o', addr', v', hO', hIssue', hWrite', hByte', hSize', rfl, _⟩ := hj
  have hDst := hWrite.trans (congrArg some (Acc.loc_of_one ha hSize))
  have hDst' := hWrite'.trans (congrArg some (Acc.loc_of_one hb hSize'))
  have hCta := sameOutputByteSameCta hp hX hIssue hIssue' hDst hDst'
  have hReduce := (Thread.actualTensorStoreForm hX hIssue).2.2
  have hReduce' := (Thread.actualTensorStoreForm hX hIssue').2.2
  obtain ⟨batch, hBatch, head, hHead, tile, stage, box, hSpec⟩ :=
    OutputWarp.issuedBox hp hX hIssue
  obtain ⟨batch', hBatch', head', hHead', tile', stage', box', hSpec'⟩ :=
    OutputWarp.issuedBox hp hX hIssue'
  rw [hSpec] at hDst
  rw [hSpec'] at hDst'
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ :=
    sameWritebackByte hp hBatch hHead hBatch' hHead' hDst hDst'
  obtain ⟨hx, hy, hk, _, _⟩ := writebackByteCoordinates hp hBatch hHead hDst
  let src := (Correction.outputElementAccess l i.1 stage box x y).loc.at k
  have hSource : TensorStore.readLoc o.spec x y k = some src := by
    rw [hSpec]
    exact Correction.writebackSourceAddress hp rfl stage box hx hy hk
  have hSource' : TensorStore.readLoc o'.spec x y k = some src := by
    rw [hSpec']
    exact Correction.writebackSourceAddress hp hCta stage box hx hy hk
  obtain ⟨w, dst, data, hw, hc, hOrder⟩ :=
    actualSourceOrderedOfSelectedExtent hp hX hFrame hExtent hIssue hSource
  obtain ⟨w', dst', data', hw', hc', hOrder'⟩ :=
    actualSourceOrderedOfSelectedExtent hp hX hFrame hExtent hIssue' hSource'
  have hEq := samePublishedWriter hp hX hIssue hSource hw hw' hc hc'
  subst w'
  obtain ⟨rfl, rfl⟩ := Execution.Writes.unique hw hw'
  have hv := hX.store_read_byte hO hReduce hByte hSource hOrder
  have hv' := hX.store_read_byte hO' hReduce' hByte' hSource' hOrder'
  exact congrArg (· :: []) (Option.some.inj (hv.trans hv'.symm))

/-- A global metadata load sharing a byte with an output writer. -/
def GlobalReadConflict (p : Params) (X : Execution) (reader : AsyncCopy.Ref) (a : Acc) : Prop :=
  ∃ i bytes, reader = .thread i ∧ UnbackedMetadataRead p X i a bytes

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
    (hFrames : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputIntentFootprint p Y)
include hp hX hFrames

private theorem metadataConflict (hAddresses : CuQReplayAddresses p X) {e f : AsyncCopy.Ref}
    {a b : Acc} {loc : Loc} (hRead : X.Intent e a false) (hWrite : X.Intent f b true)
    (ha : a.Covers loc) (hb : b.Covers loc) (hGlobal : loc.space = .global) :
    GlobalReadConflict p X e a := by
  have hFrame := hFrames X hX
  obtain ⟨i, _, bytes, he, hMeta, _⟩ :=
    globalReadAgainstOutputCases hp hX hFrame hRead hWrite ha hb hGlobal
  refine ⟨i, bytes, he, unbackedMetadataRead hp hX (fun Y hY => (hFrames Y hY).performed)
    hAddresses hMeta.reads (ha.1.symm.trans hGlobal) ?_⟩
  rintro ⟨kind, value, hWord⟩
  obtain ⟨region, hRegion, hLoc⟩ := hWord.inInput hp ha
  exact outputIntentApartInput hp hFrame hWrite hRegion hLoc hb

/-- Any outstanding global conflict involves a metadata reader. -/
theorem globalConflictCases (hAddresses : CuQReplayAddresses p X)
    (hExtent : ∀ final output, Thread.SecondOutputCommit X final output →
      final.1 / l.block < tilePrefix p p.batch * p.heads →
      Nonempty (Thread.Mma.SelectedCacheExtent l p X final)) {e f : AsyncCopy.Ref} {a b : Acc}
    {loc : Loc} (h : Conflict X e f a b) (ha : a.Covers loc) (hb : b.Covers loc)
    (hGlobal : loc.space = .global) (hef : ¬ ByteCausality l X loc e f)
    (hfe : ¬ ByteCausality l X loc f e)
    (hBad : ¬ a.SameFootprint b ∨ ¬ MorallyStrong l X e f a b ∧ ¬ SameValueWrites X e f a b) :
    GlobalReadConflict p X e a ∨ GlobalReadConflict p X f b := by
  have hFrame := hFrames X hX
  obtain ⟨hNe, wa, wb, he, hf, hw, _⟩ := h
  cases wa <;> cases wb
  · cases hw <;> contradiction
  · exact .inl (metadataConflict hp hX hFrames hAddresses he hf ha hb hGlobal)
  · exact .inr (metadataConflict hp hX hFrames hAddresses hf he hb ha hGlobal)
  · exfalso
    have hFoot := globalWriteFootprintsMatch hp hX hFrame he hf ha hb hGlobal
    apply (hBad.resolve_left (not_not_intro hFoot)).2
    obtain ⟨i, j, x, y, k, x', y', k', rfl, rfl, _⟩ :=
      unorderedGlobalWriters hp hX hFrame he hf ha hb hGlobal hNe hef hfe
    exact ⟨he, hf, hFoot,
      fun _ _ hA hB => outputWriteAgreement hp hX hFrame.performed hExtent hA hB ha hb⟩

omit hp hX hFrames in
/-- A remaining memory conflict involves an unbacked global metadata observation. -/
def ClassifiedMemoryConflict (p : Params) (l : Launch) (X : Execution) : Prop :=
  ∃ e f a b loc,
    loc.space = .global ∧ (GlobalReadConflict p X e a ∨ GlobalReadConflict p X f b) ∧
    Conflict X e f a b ∧
    a.Covers loc ∧ b.Covers loc ∧ ¬ ByteCausality l X loc e f ∧ ¬ ByteCausality l X loc f e ∧
    (¬ a.SameFootprint b ∨ ¬ MorallyStrong l X e f a b ∧ ¬ SameValueWrites X e f a b)

omit hp hX hFrames in
/-- The remaining global read case is excluded by the bounded metadata replay. -/
theorem ClassifiedMemoryConflict.impossible {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) (hBad : ClassifiedMemoryConflict p l X) : False := by
  obtain ⟨_, _, _, _, _, _, hReads, _⟩ := hBad
  rcases hReads with ⟨_, _, _, hRead⟩ | ⟨_, _, _, hRead⟩
  all_goals exact hRead.impossible hp hX hFrame

/-- Protected launch metadata determines the cache path and orders all shared effects. -/
theorem classifyMemoryConflict (hAddresses : CuQReplayAddresses p X) (hBad : MemoryConflict l X) :
    ClassifiedMemoryConflict p l X := by
  have hFrame := hFrames X hX
  have hExtent : ∀ final output, Thread.SecondOutputCommit X final output →
      final.1 / l.block < tilePrefix p p.batch * p.heads →
      Nonempty (Thread.Mma.SelectedCacheExtent l p X final) :=
    fun _ _ => Thread.Mma.selectedCacheExtentOfConsistentPrefix hp hX
      (fun Y hY => (hFrames Y hY).performed)
  obtain ⟨e, f, a, b, loc, hSpace, h, ha, hb, hef, hfe, hBad⟩ := hBad
  rcases hSpace with hGlobal | hShared
  · exact ⟨e, f, a, b, loc, hGlobal,
      globalConflictCases hp hX hFrames hAddresses hExtent h ha hb hGlobal hef hfe hBad,
      h, ha, hb, hef, hfe, hBad⟩
  · have hCuQ := (outputIntent_iff_cuQProtected hp hX).mp hFrame
    exact (noUnorderedSharedConflict hp hX hCuQ hFrame.performed hExtent
      hShared.1 ha hb h hef hfe).elim

end PTX.Kernels.TmlFa4Fwd.Safety
