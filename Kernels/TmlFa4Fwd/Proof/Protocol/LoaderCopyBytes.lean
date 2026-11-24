-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderActualReady
public import Kernels.TmlFa4Fwd.Proof.MmaOperandValues
import Kernels.TmlFa4Fwd.Proof.PagedKvGeometry
import Lemmas.Protocol.CpAsync
import Lemmas.Protocol.CpAsyncCompletionOrder

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.AsyncCopy
open Thread.Loader (CachePlane PublishedCopyGroup)

noncomputable section

/-- The source layout named by the loader's abstract packet plane. -/
def cacheLayout (p : Params) : CachePlane → CacheLayout
  | .key => p.kLayout
  | .value => p.vLayout

/-- The specified byte within one cache vector. -/
def cacheByte (p : Params) (plane : CachePlane) (batch head row lane : Nat) (upper : Bool)
    (offset : Nat) : Byte :=
  let cells := match plane with | .key => p.k | .value => p.v
  (Value.float .bf16 (cells (p.page batch (row / 16)) head (row % 16)
    (kvCopyColumn lane upper + offset / 2))).byteAt (offset % 2)

/-- The live source vector of one cache row, before any destination swizzle. -/
def cacheVector (p : Params) (plane : CachePlane) (batch head row lane : Nat)
    (upper : Bool) : Loc :=
  (cacheLayout p plane).loc (p.page batch (row / 16)) head (row % 16) (kvCopyColumn lane upper)

/-- The decoded cache source lies in a launch input region and has its specified BF16 byte. -/
theorem cacheVectorBacking {p : Params} {l : Launch} {m : Mem0} (hp : Pre p l m)
    (plane : CachePlane) {batch head row lane : Nat} (hBatch : batch < p.batch)
    (hHead : head < p.kvHeads) (hRow : row < p.kLength batch) (upper : Bool)
    {k : Nat} (hk : k < 16) :
    let loc := (cacheVector p plane batch head row lane upper).at k
    ((cacheLayout p plane).region p.pages p.kvHeads).Contains loc ∧
      m loc = some (some (cacheByte p plane batch head row lane upper k)) := by
  have hPage := ((hp.pageTable batch hBatch).2 (row / 16) (by omega)).1
  refine ⟨CacheLayout.loc_copy_in_region hPage hHead (Nat.mod_lt _ (by decide))
    (kvCopyColumn_byte_lt upper hk), ?_⟩
  have h := hp.kv_copy_byte (lane := lane) hBatch hHead hRow hk upper
  cases plane
  · exact h.1
  · exact h.2

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
include hp hX hFrame

/-- The geometry of an issued cache vector suffices to finish it in an execution prefix. -/
theorem pendingCacheVector {issue : EvId} {spec : Spec} (hIssue : X.Copy issue spec)
    (hPending : (X.async.copies issue).writeBytes = none) (plane : CachePlane)
    {batch head row lane : Nat} (hBatch : batch < p.batch) (hHead : head < p.kvHeads) (upper : Bool)
    (hSrc : row < p.kLength batch → spec.src.loc = cacheVector p plane batch head row lane upper)
    (hSize : spec.src.size = if row < p.kLength batch then 16 else 0) :
    ∃ Y, Consistent l kernel Assumptions.all m Y ∧ X.le Y ∧ X.size l < Y.size l := by
  obtain ⟨hShape, hNoWait⟩ := Thread.Loader.linearCopyOperands hX hIssue
  have hInput : (cacheLayout p plane).region p.pages p.kvHeads ∈ p.inputRegions := by
    cases plane <;> simp [cacheLayout, Params.inputRegions]
  have hByte : ∀ k < spec.src.size,
      ((cacheLayout p plane).region p.pages p.kvHeads).Contains (spec.src.loc.at k) ∧
        m (spec.src.loc.at k) = some (some (cacheByte p plane batch head row lane upper k)) := by
    intro k hk
    by_cases hRow : row < p.kLength batch
    · rw [hSrc hRow]
      exact cacheVectorBacking hp plane hBatch hHead hRow upper (by simpa [hSize, hRow] using hk)
    · simp [hSize, hRow] at hk
  exact pending_cpAsync_extendsInOrder Assumptions.wfStep hX hIssue
    hShape.completion hShape.whole hShape.noData hPending hNoWait hShape.srcSize
    (fun k hk => by rw [(hByte k hk).2]; simp)
    (fun k hk _ _ _ hw => hFrame.input_unwritten hp hInput (hByte k hk).1 hw)

/-- The bytes of a finished cache vector follow from its actual source address and size. -/
theorem writtenCacheVectorBytes {issue : EvId} {spec : Spec} (hCopy : X.Copy issue spec)
    (plane : CachePlane) {batch head row lane : Nat} (hBatch : batch < p.batch)
    (hHead : head < p.kvHeads) (upper : Bool)
    (hSrc : row < p.kLength batch → spec.src.loc = cacheVector p plane batch head row lane upper)
    (hSize : spec.src.size = if row < p.kLength batch then 16 else 0) {bytes : List Byte}
    (hWritten : (X.async.copies issue).writeBytes = some bytes) :
    bytes = if row < p.kLength batch then
      (List.range 16).map (cacheByte p plane batch head row lane upper)
      else List.replicate 16 zeroByte := by
  have hShape := actualCopyShape hX hCopy
  by_cases hRow : row < p.kLength batch
  · have hSource := hSrc hRow
    change spec.src.loc = cacheVector p plane batch head row lane upper at hSource
    rw [ite_eq_left hRow] at hSize ⊢
    have hInput : (cacheLayout p plane).region p.pages p.kvHeads ∈ p.inputRegions := by
      cases plane <;> simp [cacheLayout, Params.inputRegions]
    have hByte (k : Nat) (hk : k < 16) :
        ((cacheLayout p plane).region p.pages p.kvHeads).Contains (spec.src.loc.at k) ∧
          m (spec.src.loc.at k) = some (some (cacheByte p plane batch head row lane upper k)) := by
      rw [hSource]
      exact cacheVectorBacking hp plane hBatch hHead hRow upper hk
    have hBytes := whole_copy_write_initial hX hCopy hShape.whole hShape.noData hWritten
      (fun k hk => by rw [(hByte k (by omega)).2]; simp)
      (fun k hk _ _ _ hw => hFrame.input_unwritten hp hInput (hByte k (by omega)).1 hw)
    rw [hBytes, hShape.widthEq, hSize, Nat.sub_self, List.replicate_zero, List.append_nil]
    unfold initialBytes
    rw [hSize]
    apply List.map_congr_left
    intro k hk
    rw [(hByte k (List.mem_range.mp hk)).2]
    rfl
  · rw [ite_eq_right hRow] at hSize ⊢
    have hBytes := whole_copy_write_initial hX hCopy hShape.whole hShape.noData hWritten
      (fun _ hk => by omega) (fun _ hk => by omega)
    simpa [initialBytes, hShape.widthEq, hSize] using hBytes

omit hp hX hFrame in
/-- The exact geometry of an issued vector forces its completion in a maximal execution. -/
theorem cacheVectorWritesBytesOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {issue : EvId} {spec : Spec}
    (hCopy : X.Copy issue spec) (plane : CachePlane)
    {batch head row lane : Nat} (hBatch : batch < p.batch) (hHead : head < p.kvHeads) (upper : Bool)
    (hSrc : row < p.kLength batch → spec.src.loc = cacheVector p plane batch head row lane upper)
    (hSize : spec.src.size = if row < p.kLength batch then 16 else 0) :
    (X.async.copies issue).writeBytes = some
      (if row < p.kLength batch then
        (List.range 16).map (cacheByte p plane batch head row lane upper)
       else List.replicate 16 zeroByte) := by
  cases hw : (X.async.copies issue).writeBytes with
  | none =>
    exact (hMax.not_grows
      (pendingCacheVector hp hMax.1 hFrame hCopy hw plane hBatch hHead upper hSrc hSize)).elim
  | some bytes =>
    exact congrArg some (writtenCacheVectorBytes hp hMax.1 hFrame hCopy plane hBatch
      hHead upper hSrc hSize hw)

/-- A completed issue from the published group writes the specified BF16 bytes
of its physical cache page for a live row, and a complete zero vector for a
masked row. Source address and size are properties of the actual copy spec. -/
theorem publishedCopyWritesCacheBytes {issue : EvId} (group : PublishedCopyGroup l X issue)
    {j : Nat} {spec : Spec} (hMember : (j, spec) ∈ group.copies) {batch head row lane : Nat}
    (hBatch : batch < p.batch) (hHead : head < p.kvHeads) (upper : Bool)
    (hSrc : row < p.kLength batch →
      spec.src.loc = cacheVector p group.publication.packet.plane batch head row lane upper)
    (hSize : spec.src.size = if row < p.kLength batch then 16 else 0) {bytes : List Byte}
    (hWrite : X.MemWrites (.async (issue.1, j) (.write .copy)) spec.dst bytes) :
    bytes = if row < p.kLength batch then
      (List.range 16).map (cacheByte p group.publication.packet.plane batch head row lane upper)
      else List.replicate 16 zeroByte := by
  obtain ⟨_, _, hCopy⟩ := (group.member j spec).mp hMember
  have hShape := actualCopyShape hX hCopy
  have hWritten := ((Execution.memWrites_write_copy_of_whole hCopy hShape.whole).mp hWrite).2
  exact writtenCacheVectorBytes hp hX hFrame hCopy group.publication.packet.plane
    hBatch hHead upper hSrc hSize hWritten

/-- Use a written cache vector as the abstract source for an operand byte once
all competing writes at that byte have been ordered. -/
theorem publishedCopyOperandByteSource {issue mma : EvId} (group : PublishedCopyGroup l X issue)
    {j : Nat} {spec : Spec} (hMember : (j, spec) ∈ group.copies) {batch head row lane : Nat}
    (hBatch : batch < p.batch) (hHead : head < p.kvHeads) (upper : Bool)
    (hSrc : row < p.kLength batch →
      spec.src.loc = cacheVector p group.publication.packet.plane batch head row lane upper)
    (hSize : spec.src.size = if row < p.kLength batch then 16 else 0) {bytes : List Byte}
    {off index : Nat} (hOff : off < 16)
    (hWrite : X.MemWrites (.async (issue.1, j) (.write .copy)) spec.dst bytes) :
    let loc := spec.dst.loc.at off
    let write := Ref.async (issue.1, j) (.write .copy)
    let read := Ref.async mma (.mmaRead true index)
    modelCausality l X loc write read →
    (∀ other acc data, X.MemWrites other acc data → acc.Covers loc →
      other = write ∨ modelCausality l X loc other write ∨ modelCausality l X loc read other) →
    Mma.OperandByteSource l X mma true index loc (if row < p.kLength batch then
      cacheByte p group.publication.packet.plane batch head row lane upper off else zeroByte) := by
  intro loc write read hOrder hCompeting
  have hData := publishedCopyWritesCacheBytes hp hX hFrame group hMember
    hBatch hHead upper hSrc hSize hWrite
  have hDst := (actualCopyShape hX ((group.member j spec).mp hMember).2.2).widthEq
  refine ⟨write, spec.dst, bytes, hWrite, ?_, ?_, hOrder, hCompeting⟩
  · simp only [loc, Acc.Covers, Loc.InRange, Loc.at, hDst, true_and]
    exact ⟨by omega, by omega⟩
  · simp only [wbyte, loc, Loc.at, Nat.add_sub_cancel_left, hData]
    split
    · rw [List.getElem?_map, List.getElem?_range hOff, Option.map_some]
    · rw [List.getElem?_replicate, ite_eq_left hOff]

end
end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
