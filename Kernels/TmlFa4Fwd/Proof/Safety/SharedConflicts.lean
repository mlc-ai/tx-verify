-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Safety.TensorInputOutput
public import Kernels.TmlFa4Fwd.Proof.Safety.TensorInputReads
public import Kernels.TmlFa4Fwd.Proof.Thread.SharedReadSites
public import Kernels.TmlFa4Fwd.Proof.OutputProtection
public import Kernels.TmlFa4Fwd.Proof.Protocol.PrimingKeyOutput
public import Kernels.TmlFa4Fwd.Proof.Protocol.PrimingValueOutput
import Kernels.TmlFa4Fwd.Proof.Protocol.CacheWriteOrder
import Kernels.TmlFa4Fwd.Proof.Protocol.StatisticsReadOrder
import Kernels.TmlFa4Fwd.Proof.Safety.BiasReadConflicts
import Kernels.TmlFa4Fwd.Proof.Safety.StagingOperandOrder
import Kernels.TmlFa4Fwd.Proof.InputActualSources
import Kernels.TmlFa4Fwd.Proof.Protocol.OutputScratchSource
import Kernels.TmlFa4Fwd.Proof.Protocol.SelectedCacheOutputOrder
import Kernels.TmlFa4Fwd.Proof.Protocol.ObservedCacheOperandOrder
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaMaximalCacheExtent
public import Kernels.TmlFa4Fwd.Proof.Protocol.OperandOutputReuse
import Kernels.TmlFa4Fwd.Proof.CorrectionReadySources
import Kernels.TmlFa4Fwd.Proof.Thread.OutputSlotGeometry
import Kernels.TmlFa4Fwd.Proof.MmaQueryStartupPrefix
import Kernels.TmlFa4Fwd.Proof.Thread.BiasReadAddress
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderSameSlotCopy
import Kernels.TmlFa4Fwd.Proof.Thread.MmaSharedByteRange
import Kernels.TmlFa4Fwd.Proof.Thread.QueryOutputBank
import Kernels.TmlFa4Fwd.Proof.Thread.SharedScratchWrites
import Lemmas.Order.Order
import Kernels.TmlFa4Fwd.Proof.Thread.TensorForms

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Safety
open PTX PTX.AsyncCopy

/-- A shared write intent originates in a scalar store, a tensor input or a cache copy. -/
private inductive SharedWriter (X : Execution) : Ref → Acc → Prop
  | ordinary {i a data} (h : X.Writes i a data) : SharedWriter X (.thread i) a
  | tensorInput {i x y byte a} (h : X.AsyncFootprint i (.write (.load x y byte)) a) :
      SharedWriter X (.async i (.write (.load x y byte))) a
  | cache {i s} (h : X.Copy i s) : SharedWriter X (.async i (.write .copy)) s.dst

/-- The ordinary, MMA operand and output tensor reads that access shared memory. -/
private inductive SharedReader (X : Execution) : Ref → Acc → Prop
  | ordinary {i a data} (h : X.Reads i a data) : SharedReader X (.thread i) a
  | operand {i isB index a} (h : X.AsyncFootprint i (.mmaRead isB index) a) :
      SharedReader X (.async i (.mmaRead isB index)) a
  | output {i x y byte a} (h : X.AsyncFootprint i (.read (.store x y byte)) a) :
      SharedReader X (.async i (.read (.store x y byte))) a

private theorem sharedWriterOfIntent {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {e : Ref} {a : Acc} (h : X.Intent e a true) (hs : a.loc.space = .shared) :
    SharedWriter X e a := by
  cases e with
  | thread i =>
    rcases h with ⟨_, _, h⟩ | ⟨_, hw, _⟩ | ⟨_, _, hRmw⟩
    · cases h
    · exact .ordinary hw
    · exact (noActualRmw hX hRmw).elim
  | async i part =>
    obtain ⟨hMode, hFoot⟩ := h
    cases part <;> simp only [Part.writes, Bool.true_eq_false] at hMode <;>
      try exact False.elim hFoot
    case writeLoad => exact .tensorInput hFoot
    case writeCopy =>
      obtain ⟨_, hi, _, rfl⟩ := hFoot
      exact .cache hi
    case writeStore =>
      obtain ⟨_, _, _, hLoc, _⟩ := hFoot
      rw [Execution.store_writeLoc_global hLoc] at hs
      cases hs
    case writeCta =>
      obtain ⟨_, _, hi, _, _⟩ := hFoot
      exact (noClcIssue hX hi).elim
    case writeElem =>
      obtain ⟨s, hi, hAt⟩ := hFoot
      simp [Spec.elems, Spec.elemOffsets, (actualCopyShape hX hi).whole] at hAt

private theorem sharedReaderOfIntent {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {e : Ref} {a : Acc} (h : X.Intent e a false) (hs : a.loc.space = .shared) :
    SharedReader X e a := by
  cases e with
  | thread i =>
    rcases h with ⟨_, hr, _⟩ | ⟨_, _, h⟩ | ⟨_, _, hRmw⟩
    · exact .ordinary hr
    · cases h
    · exact (noActualRmw hX hRmw).elim
  | async i part =>
    obtain ⟨hMode, hFoot⟩ := h
    cases part <;> simp only [Part.writes, Bool.false_eq_true] at hMode <;>
      try exact False.elim hFoot
    case mmaRead => exact .operand hFoot
    case readStore => exact .output hFoot
    case readLoad =>
      obtain ⟨_, _, _, hLoc, _⟩ := hFoot
      rw [Execution.tensor_readLoc_global hLoc] at hs
      cases hs
    case readPrefetch =>
      obtain ⟨_, _, _, hLoc, _⟩ := hFoot
      rw [TensorTransfer.sourceLoc_global hLoc] at hs
      cases hs
    case readCopy =>
      rcases hFoot with ⟨_, hi, rfl⟩ | hPrefetch
      · rw [(actualCopyShape hX hi).srcGlobal] at hs
        cases hs
      · exact (Thread.noBulkPrefetch hX hPrefetch).elim
    case oldStore =>
      obtain ⟨_, _, _, _, hLoc, _⟩ := hFoot
      rw [Execution.store_writeLoc_global hLoc] at hs
      cases hs
    case oldElem =>
      obtain ⟨_, _, hi, hReduce, _⟩ := hFoot
      rw [(actualCopyShape hX hi).whole] at hReduce
      cases hReduce

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem cacheWriteRange {i : EvId} {s : Spec} (hCopy : X.Copy i s) {loc : Loc}
    (hCover : s.dst.Covers loc) :
    l.sharedBase + 68608 ≤ loc.addr ∧ loc.addr < l.sharedBase + 166912 := by
  obtain ⟨_, slot, pair, upper, hDst⟩ := Thread.Loader.copyDestination hp hX hCopy
  rw [hDst] at hCover
  let base := kvCopyAddress l.sharedBase slot (i.1 % l.block) pair upper
  have hLo : base ≤ loc.addr := hCover.2.2.1
  have hHi : loc.addr < base + 16 := hCover.2.2.2
  let byte := loc.addr - base
  have hByte : byte < 16 := by dsimp [byte]; omega
  have hEq : base + byte = loc.addr := Nat.add_sub_of_le hLo
  have hRange := kvCopyAddress_range (lane := i.1 % l.block) (upper := upper) hp.shared.1
    slot.isLt pair.isLt hByte
  exact hEq ▸ hRange

private theorem ordinaryReadOutsideCache {j : EvId} {b : Acc} {data : List (Option Byte)}
    (hr : X.Reads j b data) {loc : Loc} (hs : loc.space = .shared) (hb : b.Covers loc) :
    loc.addr < l.sharedBase + 3072 ∨ l.sharedBase + 166912 ≤ loc.addr := by
  have hLo := hb.2.2.1
  have hHi := hb.2.2.2
  rcases Thread.sharedReadObservation hX hr (hb.1.symm.trans hs) with
    hAlloc | ⟨repeated, vector, hBias⟩ | ⟨stage, kind, hStats⟩
  · left
    obtain ⟨g, j⟩ := j
    rw [Mma.allocationReadFootprint hp hX hAlloc] at hHi
    change loc.addr < l.sharedBase + 312 + 4 at hHi
    omega
  · right
    have hBias := (Thread.Scores.biasVectorReadLower hp hX hBias).1
    omega
  · left
    have hStats := (Thread.Correction.statisticsReadRange hp hX hStats).2.2
    omega

private theorem ordinaryWriteReadMmaCases {writer mma : EvId} {isB : Bool} {index : Nat} {a b : Acc}
    {bytes : List Byte} {loc : Loc} (hs : loc.space = .shared) (ha : a.Covers loc)
    (hb : b.Covers loc) (hw : X.Writes writer a bytes)
    (hr : X.AsyncFootprint mma (.mmaRead isB index) b)
    (hfe : ¬ ByteCausality l X loc (.async mma (.mmaRead isB index)) (.thread writer)) :
    False := by
  have hFoot := hr.2
  rw [Acc.loc_of_one hb hr.1] at hFoot
  have hRange := Thread.mmaSharedByteRange hp hX hFoot
  obtain hBelow | hStaging := Thread.ordinarySharedWriteBelowOrStaging hp hX hw ha hs
  · exact (Nat.not_lt_of_ge hRange.lower hBelow).elim
  obtain ⟨stage, box, x, row, hx, hy, hEq, hStore⟩ := hStaging.stageElement hp hX
  have hCta : loc.cta = writer.1/l.block := by
    rw [hEq] at ha
    exact ha.2.1
  obtain ⟨_,_,_,_,_,hIssue,hAt⟩ := Thread.mmaSharedFootprintIssue hX hFoot
  by_cases hStage : stage = 0
  · subst stage
    obtain ⟨box,chunk,he⟩ := hStore.decoded
    have hZero := Thread.Correction.StageZeroStagingWrites.of_event box chunk he
    obtain ⟨_,_,_,_,_,_,_,hOrder⟩ := observedOperandBeforeFirstStaging hp hX
      hZero hIssue (hRange.cta.symm.trans hCta) hAt ha hs
    exact (hfe (.direct hOrder)).elim
  have hSecond := (by decide : ∀ s : Fin 2, s ≠ 0 → s = 1) stage hStage
  subst stage
  obtain ⟨_,_,hOrder⟩ := Protocol.Output.mmaOperandBeforeSecondStagingOfSameCta
    hp hX hStore (hRange.cta.symm.trans hCta) hIssue hAt hs hCta
  exact (hfe (.direct hOrder)).elim

private theorem sharedWriteReadCases (hCuQ : Epilogue.DrainCuQProtected p X)
    (hFrame : OutputFootprint p X)
    (hExtent : ∀ final output, Thread.SecondOutputCommit X final output →
      final.1 / l.block < tilePrefix p p.batch * p.heads →
      Nonempty (Thread.Mma.SelectedCacheExtent l p X final)) {e f : Ref} {a b : Acc} {loc : Loc}
    (hs : loc.space = .shared) (ha : a.Covers loc) (hb : b.Covers loc)
    (hef : ¬ ByteCausality l X loc e f) (hfe : ¬ ByteCausality l X loc f e)
    (hw : SharedWriter X e a) (hr : SharedReader X f b) :
    False := by
  cases hw with
  | ordinary hw =>
    cases hr with
    | ordinary hr =>
      obtain hOrder | ⟨_, _, hRead⟩ :=
        Thread.ordinarySharedReadOrderOrStatistics hp hX hs hw hr ha hb
      · exact (hef hOrder).elim
      · have hStats := Protocol.Statistics.statisticsAccessOrder hp hX hCuQ hw hRead ha hb
        exact (hfe (hStats.resolve_left hef)).elim
    | operand hr => exact ordinaryWriteReadMmaCases hp hX hs ha hb hw hr hfe
    | output hr =>
      obtain ⟨_, _, hStore, hLoc, hSize⟩ := hr
      rw [Acc.loc_of_one hb hSize] at hLoc
      exact (hef (Protocol.Output.ordinaryWriteBeforeOutputRead hp hX hStore hLoc hw ha)).elim
  | @tensorInput i x y byte a hw =>
    have hIntent : X.Intent (.async i (.write (.load x y byte))) a true := ⟨rfl, hw⟩
    cases hr with
    | ordinary hr =>
      rcases Thread.sharedReadObservation hX hr (hb.1.symm.trans hs) with
        hAlloc | ⟨repeated, vector, hBias⟩ | ⟨stage, kind, hStats⟩
      · exfalso
        obtain ⟨_, hBelow⟩ := Thread.tensorInputWriteAboveScratch hp hX hIntent ha
        have hHi := hb.2.2.2
        rw [Mma.allocationReadFootprint hp hX hAlloc] at hHi
        change loc.addr < l.sharedBase + 312 + 4 at hHi
        omega
      · exact (hfe ((tensorBiasReadConflictOrdered hp hX hw ha hBias hb).resolve_left hef)).elim
      · exfalso
        obtain ⟨_, hBelow⟩ := Thread.tensorInputWriteAboveScratch hp hX hIntent ha
        have hHi := hb.2.2.2
        have hStats := (Thread.Correction.statisticsReadRange hp hX hStats).2.2
        omega
    | operand hr => exact (hef (tensorInputBeforeMmaRead hp hX hw hr ha hb)).elim
    | output hr =>
      obtain ⟨_, _, hStore, hLoc, hSize⟩ := hr
      rw [Acc.loc_of_one hb hSize] at hLoc
      exact (hef (tensorInputBeforeOutputRead hp hX hIntent ha hStore hLoc)).elim
  | cache hw =>
    cases hr with
    | ordinary hr =>
      obtain ⟨hLo, hHi⟩ := cacheWriteRange hp hX hw ha
      rcases ordinaryReadOutsideCache hp hX hr hs hb with h | h <;> omega
    | @operand j isB index b hr =>
      cases isB
      · have hFoot := hr.2
        rw [Acc.loc_of_one hb hr.1] at hFoot
        have hBelow := Thread.mmaSharedOperandBand hp hX hFoot
        change loc.addr < l.sharedBase + 68608 at hBelow
        have hAbove := (cacheWriteRange hp hX hw ha).1
        omega
      · have hFoot := hr.2
        rw [Acc.loc_of_one hb hr.1] at hFoot
        obtain ⟨_,_,_,_,_,hMma,hLoc⟩ := Thread.mmaSharedFootprintIssue hX hFoot
        obtain ⟨g,j'⟩ := j
        exact (Protocol.LoaderReady.cacheCopyOrderedWithObservedOperand hp hX hMma
          hLoc hw ha).elim hef hfe
    | output hr =>
      obtain ⟨_, _, hStore, hLoc, hSize⟩ := hr
      rw [Acc.loc_of_one hb hSize] at hLoc
      exact (hef (Protocol.Output.cacheCopyBeforeOutputReadOfSelectedExtent hp hX hFrame
        hExtent hw ha hStore hLoc)).elim

private theorem tensorInputOutsideCache {i : EvId} {s : Spec} (hCopy : X.Copy i s) {loc : Loc}
    (ha : s.dst.Covers loc) {j : EvId} {x y byte : Nat} {b : Acc}
    (h : X.AsyncFootprint j (.write (.load x y byte)) b) (hb : b.Covers loc) : False := by
  obtain ⟨hLo, hHi⟩ := cacheWriteRange hp hX hCopy ha
  obtain ⟨_, _, hi, hLoc, hSize⟩ := h
  rw [Acc.loc_of_one hb hSize] at hLoc
  rcases tensorInputWriteLocOutsideKv hp hX hi hLoc with h | h <;> omega

private theorem sharedWritePairCases (hFrame : OutputFootprint p X)
    (hExtent : ∀ final output, Thread.SecondOutputCommit X final output →
      final.1 / l.block < tilePrefix p p.batch * p.heads →
      Nonempty (Thread.Mma.SelectedCacheExtent l p X final)) {e f : Ref} {a b : Acc} {loc : Loc}
    (hs : loc.space = .shared) (ha : a.Covers loc) (hb : b.Covers loc) (hNe : e ≠ f)
    (hef : ¬ ByteCausality l X loc e f) (hfe : ¬ ByteCausality l X loc f e) (h : SharedWriter X e a)
    (hOther : SharedWriter X f b) :
    False := by
  cases h with
  | ordinary hw =>
    cases hOther with
    | ordinary hOther =>
      have hLane := Thread.ordinarySharedWritersSameLane hp hX hs hw hOther ha hb
      have hIndex : _ ≠ _ := fun h => hNe (congrArg Ref.thread (Prod.ext hLane h))
      rcases Nat.lt_or_gt_of_ne hIndex with h | h
      · exact (hef (.direct (.inl (.single (.inl
          (po_of_overlap hw.access hOther.access hLane h ⟨loc,ha,hb⟩)))))).elim
      · exact (hfe (.direct (.inl (.single (.inl
          (po_of_overlap hOther.access hw.access hLane.symm h ⟨loc,hb,ha⟩)))))).elim
    | cache hOther =>
      have hLo := (cacheWriteRange hp hX hOther hb).1
      obtain hLow | hStage := Thread.ordinarySharedWriteBelowOrStaging hp hX hw ha hs
      · omega
      · exact hfe (Protocol.Output.cacheCopyBeforeStagingOfSelectedExtent hp hX hFrame hExtent
          hOther hb hStage ha)
    | tensorInput hOther =>
      exact (hfe (tensorInputBeforeOrdinaryWrite hp hX ⟨rfl, hOther⟩ hb hw ha).2).elim
  | tensorInput hw =>
    cases hOther with
    | ordinary hOther =>
      exact (hef (tensorInputBeforeOrdinaryWrite hp hX ⟨rfl, hw⟩ ha hOther hb).2).elim
    | tensorInput hOther =>
      rcases tensorInputWritesOrdered hp hX hw ha hOther hb hNe with hOrder | hOrder
      · exact (hef hOrder).elim
      · exact (hfe hOrder).elim
    | cache hOther => exact (tensorInputOutsideCache hp hX hOther hb hw ha).elim
  | cache hw =>
    cases hOther with
    | ordinary hOther =>
      have hLo := (cacheWriteRange hp hX hw ha).1
      obtain hLow | hStage := Thread.ordinarySharedWriteBelowOrStaging hp hX hOther hb hs
      · omega
      · exact hef (Protocol.Output.cacheCopyBeforeStagingOfSelectedExtent hp hX hFrame hExtent
          hw ha hStage hb)
    | tensorInput hOther => exact (tensorInputOutsideCache hp hX hw ha hOther hb).elim
    | cache hOther =>
      rcases Protocol.LoaderReady.cacheCopyWriteOrder hp hX hw hOther ha hb with
        hSame | hBefore | hAfter
      · exact (hNe (congrArg (fun issue => Ref.async issue (.write .copy)) hSame)).elim
      · exact (hef (.direct hBefore)).elim
      · exact (hfe (.direct hAfter)).elim

/-- Every overlapping shared conflict has byte order in at least one direction. -/
theorem noUnorderedSharedConflict (hCuQ : Epilogue.DrainCuQProtected p X)
    (hFrame : OutputFootprint p X)
    (hExtent : ∀ final output, Thread.SecondOutputCommit X final output →
      final.1 / l.block < tilePrefix p p.batch * p.heads →
      Nonempty (Thread.Mma.SelectedCacheExtent l p X final)) {e f : Ref} {a b : Acc} {loc : Loc}
    (hs : loc.space = .shared) (ha : a.Covers loc) (hb : b.Covers loc) (h : Conflict X e f a b)
    (hef : ¬ ByteCausality l X loc e f) (hfe : ¬ ByteCausality l X loc f e) :
    False := by
  obtain ⟨hNe, wa, wb, he, hf, hWrite, _⟩ := h
  have hsA := ha.1.symm.trans hs
  have hsB := hb.1.symm.trans hs
  cases wa <;> cases wb
  · cases hWrite <;> contradiction
  · exact sharedWriteReadCases hp hX hCuQ hFrame hExtent hs hb ha hfe hef
      (sharedWriterOfIntent hX hf hsB) (sharedReaderOfIntent hX he hsA)
  · exact sharedWriteReadCases hp hX hCuQ hFrame hExtent hs ha hb hef hfe
      (sharedWriterOfIntent hX he hsA) (sharedReaderOfIntent hX hf hsB)
  · exact sharedWritePairCases hp hX hFrame hExtent hs ha hb hNe hef hfe
      (sharedWriterOfIntent hX he hsA) (sharedWriterOfIntent hX hf hsB)

end PTX.Kernels.TmlFa4Fwd.Safety
