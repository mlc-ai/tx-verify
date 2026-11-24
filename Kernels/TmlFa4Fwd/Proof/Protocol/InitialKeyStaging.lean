-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderOperandCoverage
public import Kernels.TmlFa4Fwd.Proof.Thread.InitialKeyOperandFrame
public import Kernels.TmlFa4Fwd.Proof.Thread.OutputCommitOrder
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionSecondOutputAcquire

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Output
open PTX PTX.AsyncCopy
open Thread (initialKeyByte)
open Thread.Loader (PublishedCopyGroup)
open Mma (qkByteIndex qkLoaderLane qkLoaderByte qkPlaneColumn qkPlaneColumn_lt)

noncomputable section

/-- Every byte of a physical slot-zero copy vector has an initial QK operand coordinate. -/
theorem initialKeyByteOfVector (l : Launch) (cta : Nat) (lane : Fin 64) (pair : Fin 16)
    (upper : Bool) {off : Nat} (hOff : off < 16) :
    ∃ fragment : Fin 8, ∃ row k byte : Nat, row < 128 ∧ k < 16 ∧ byte < 2 ∧
      initialKeyByte l cta fragment row k byte =
        ⟨.shared,cta,kvCopyAddress l.sharedBase 0 lane pair upper + off⟩ := by
  let row := 8*pair.val + lane.val/8
  let col := 8*(lane.val%8) + off/2
  have hLane := lane.isLt
  have hPair := pair.isLt
  have hCol : col < 64 := by dsimp [col]; omega
  let fragment : Fin 8 := ⟨col/16 + (if upper then 4 else 0),by split <;> omega⟩
  let k := col%16
  let byte := off%2
  refine ⟨fragment,row,k,byte,by dsimp [row]; omega,Nat.mod_lt _ (by decide),
    Nat.mod_lt _ (by decide),?_⟩
  have hFrag : qkPlaneColumn fragment k = col ∧ decide (4 ≤ fragment.val) = upper := by
    dsimp [qkPlaneColumn,fragment,k]
    cases upper <;> simp only [Bool.false_eq_true,↓reduceIte,Nat.add_zero,
      decide_eq_false_iff_not,decide_eq_true_eq] <;> exact ⟨by omega,by omega⟩
  have hLane' : qkLoaderLane fragment row k = lane.val := by
    dsimp only [qkLoaderLane]
    rw [hFrag.1]
    dsimp [row,col]
    omega
  have hPair' : row/8 = pair.val := by dsimp [row]; omega
  have hByte : qkLoaderByte fragment k byte = off := by
    rw [qkLoaderByte,hFrag.1]
    dsimp [col,byte]
    omega
  simp only [initialKeyByte,hLane',hPair',hFrag.2,hByte]

/-- An overlapping staging write follows the initial K copy through the actual QK read. -/
theorem initialKeyCopyBeforeSecondStaging {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {writer : EvId} {a : Acc} {data : List Byte}
    (hStage : Thread.StageStagingWrite X writer 1 a data)
    (fragment : Fin 8) {row k byte : Nat} (hRow : row < 128) (hK : k < 16) (hByte : byte < 2)
    (hStoreCovers : a.Covers (initialKeyByte l (writer.1/l.block) fragment row k byte)) :
    let loc := initialKeyByte l (writer.1/l.block) fragment row k byte
    ∃ (issue : EvId) (group : PublishedCopyGroup l X issue) (j : Nat) (s : Spec)
        (source : List Byte) (mma : EvId) (value : Option Byte),
      X.AsyncArrive issue (Thread.Loader.readyObject l writer.1 0) true ∧
      LoaderReady.generation l X issue 0 = 0 ∧ (j,s) ∈ group.copies ∧
      X.MemWrites (.async (issue.1,j) (.write .copy)) s.dst source ∧ s.dst.Covers loc ∧
      X.MmaRead mma true (qkByteIndex row k byte) loc value ∧
      ByteCausality l X loc (.async (issue.1,j) (.write .copy)) (.thread writer) := by
  let loc := initialKeyByte l (writer.1/l.block) fragment row k byte
  obtain ⟨oWait,hoWait,hLater⟩ := Thread.StageStagingWrite.secondAcquire hp hX hStage
  obtain ⟨commit,spec,scope,hCommit,hCta,hObserved⟩ :=
    Thread.secondOutputAcquireReads hp hX hoWait
  have gc := hCommit.issuerWarp hp hX
  obtain ⟨wait,mma,d,op,accum,mask,hMma,hCommitOrder,hReady,hReadyOrder,hFirst,hSource⟩ :=
    Thread.initialKeyByteReadBeforeSecondOutputCommit hp hX hCommit 0 fragment hRow hK hByte
  obtain ⟨completion⟩ := LoaderReady.completedForObservedIssuer hp hX gc
    (fun h hc => hCommit.sameReleaseIssuer hp hX h hc) hReady
    (LoaderReady.actualEmptyGuardLower hp hX commit.1 0)
  rw [hFirst] at completion
  have hSame : commit.1/l.block = writer.1/l.block := by
    rw [← hLater.1]
    exact hCta.2.2
  have hLoc : op.byteLoc .b (qkByteIndex row k byte) = some loc := by
    rw [hSource,hSame]
  have hCol := qkPlaneColumn_lt fragment hK
  let lane : Fin 64 := ⟨qkLoaderLane fragment row k,by dsimp [qkLoaderLane]; omega⟩
  let pair : Fin 16 := ⟨row/8,by omega⟩
  let off := qkLoaderByte fragment k byte
  have hOff : off < 16 := by dsimp [off,qkLoaderByte]; omega
  have hVector : loc = ⟨.shared,(commit.1,wait).1 / l.block,
      kvCopyAddress l.sharedBase (0 : Fin 3) lane pair (decide (4 ≤ fragment.val)) + off⟩ := by
    simp [loc,initialKeyByte,lane,pair,off,hSame]
  obtain ⟨publication,group,j,s,bytes,hPub,_,hGeneration,_,_,hMember,_,hCover,hWrite,hOrder⟩ :=
    completion.actualOperandCoveringCopyWithPublication hp hX (isB := true)
      (index := qkByteIndex row k byte) lane pair (decide (4 ≤ fragment.val)) hOff hMma
      hReadyOrder hLoc hVector
  obtain ⟨hObservedDone,hScope,hRead⟩ := hObserved (isB := true) hMma hCommitOrder.1
    hCommitOrder.2.1 hLoc
  obtain ⟨value,hValue⟩ := hRead
  have hStageWrite : X.MemWrites (.thread writer) a data := .inl hStage.writes
  have hPub' : X.AsyncArrive publication (Thread.Loader.readyObject l writer.1 0) true := by
    simpa only [Thread.Loader.readyObject,Prod.fst,hSame] using hPub
  exact ⟨publication,group,j,s,bytes,mma,value,hPub',hGeneration,hMember,hWrite,hCover,hValue,
    .commitOperand rfl ⟨s.dst,hWrite.intent,hCover⟩ (.inl ⟨d,op,accum,mask,hMma⟩)
      ⟨value,hValue⟩ (.direct hOrder) ⟨scope,hObservedDone,hScope⟩ hLater
      ⟨a,.inl ⟨true,hStageWrite.intent⟩,hStoreCovers⟩⟩

/-- An actual published phase-zero copy to slot zero precedes every overlapping
stage-one staging byte from the same CTA. The proof uses the actual QK read of that byte. -/
theorem initialKeyPublicationBeforeSecondStaging {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {publication writer : EvId} {j : Nat} {s : Spec} {a : Acc} {data : List Byte} {loc : Loc}
    (group : PublishedCopyGroup l X publication)
    (hPub : X.AsyncArrive publication (Thread.Loader.readyObject l writer.1 0) true)
    (hInitial : LoaderReady.generation l X publication 0 = 0) (hMember : (j,s) ∈ group.copies)
    (hCopy : s.dst.Covers loc) (hStage : Thread.StageStagingWrite X writer 1 a data)
    (hStore : a.Covers loc) :
    ByteCausality l X loc (.async (publication.1,j) (.write .copy)) (.thread writer) := by
  obtain ⟨pair,upper,hDest⟩ := group.destination hp hX hPub hMember
  have hSlot := group.slotFor hp hX hPub
  have hCta := LoaderReady.publicationCta hp hX hPub
  let lane : Fin 64 := ⟨(publication.1%l.block)%64,Nat.mod_lt _ (by decide)⟩
  let base := kvCopyAddress l.sharedBase 0 lane pair upper
  have hd : s.dst = {loc := ⟨.shared,writer.1/l.block,base⟩, size := 16} := by
    dsimp only at hDest
    rw [hSlot,← hCta] at hDest
    simpa [base,lane,kvCopyAddress,Nat.mod_mod] using hDest
  have hCover := hCopy
  rw [hd] at hCover
  obtain ⟨hs,hc,hLo,hHi⟩ := hCover
  let off := loc.addr-base
  have hOff : off < 16 := by
    change base ≤ loc.addr at hLo
    change loc.addr < base+16 at hHi
    dsimp [off]
    omega
  have hLoc : loc = ⟨.shared,writer.1/l.block,base+off⟩ := by
    have ha : loc.addr = base+off := by
      change base ≤ loc.addr at hLo
      dsimp only [off]
      omega
    cases loc
    congr
  obtain ⟨fragment,row,k,byte,hRow,hK,hByte,hAt⟩ :=
    initialKeyByteOfVector l (writer.1/l.block) lane pair upper hOff
  change initialKeyByte l (writer.1/l.block) fragment row k byte = _ at hAt
  rw [← hLoc] at hAt
  obtain ⟨other,selected,otherIndex,spec,bytes,mma,observed,
      hOther,hPhase,hSelected,_,hCover,_,hOrder⟩ :=
    initialKeyCopyBeforeSecondStaging hp hX hStage fragment hRow hK hByte (hAt.symm ▸ hStore)
  change spec.dst.Covers (initialKeyByte l (writer.1/l.block) fragment row k byte) at hCover
  rw [hAt] at hCover hOrder
  obtain ⟨rfl,rfl⟩ := LoaderReady.coveringCopyUniqueInGeneration hp hX group selected hPub hOther
    (hInitial.trans hPhase.symm) hMember hSelected hCopy hCover
  exact hOrder

end
end PTX.Kernels.TmlFa4Fwd.Protocol.Output
