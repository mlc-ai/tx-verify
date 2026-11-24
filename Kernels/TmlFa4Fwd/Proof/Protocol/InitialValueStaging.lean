-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderOperandCoverage
public import Kernels.TmlFa4Fwd.Proof.Thread.InitialValueByteOperands
public import Kernels.TmlFa4Fwd.Proof.Thread.OutputCommitOrder
public import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionSecondOutputAcquire

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Output
open PTX PTX.AsyncCopy
open Thread.Loader (PublishedCopyGroup)
open Mma (pvKeyRow pvValueByteLoc qkByteIndex)

noncomputable section

/-- The physical byte of the initial value packet addressed by one PV operand coordinate. -/
def initialValueByte (l : Launch) (cta : Nat) (fragment : Fin 8) (col k byte : Nat) : Loc :=
  let key := pvKeyRow fragment k
  ⟨.shared, cta, kvCopyAddress l.sharedBase 1 (8 * (key % 8) + (col % 64) / 8)
    (key / 8) (decide (64 ≤ col)) + 2 * (col % 8) + byte⟩

/-- Every byte of a physical slot-one copy vector has a PV operand coordinate. -/
theorem initialValueByteOfVector (l : Launch) (cta : Nat) (lane : Fin 64) (pair : Fin 16)
    (upper : Bool) {off : Nat} (hOff : off < 16) :
    ∃ fragment : Fin 8, ∃ col k byte : Nat, col < 128 ∧ k < 16 ∧ byte < 2 ∧
      initialValueByte l cta fragment col k byte =
        ⟨.shared,cta,kvCopyAddress l.sharedBase 1 lane pair upper + off⟩ := by
  let key := 8*pair.val + lane.val/8
  have hLane := lane.isLt
  have hPair := pair.isLt
  let fragment : Fin 8 := ⟨key/16,by dsimp [key]; omega⟩
  let col := (if upper then 64 else 0) + 8*(lane.val%8) + off/2
  let byte := off%2
  refine ⟨fragment,col,key%16,byte,?_,Nat.mod_lt _ (by decide),Nat.mod_lt _ (by decide),?_⟩
  · cases upper <;> simp [col] <;> omega
  have hKey : pvKeyRow fragment (key%16) = key := by
    dsimp [pvKeyRow,fragment]
    omega
  have hCoord : 8*(key%8)+(col%64)/8 = lane.val ∧ key/8 = pair.val ∧
      decide (64 ≤ col) = upper ∧ 2*(col%8)+byte = off := by
    dsimp [key,col,byte]
    cases upper <;> simp only [Bool.false_eq_true,↓reduceIte,Nat.zero_add,
      decide_eq_false_iff_not,decide_eq_true_eq] <;>
      exact ⟨by omega,by omega,by omega,by omega⟩
  simp only [initialValueByte,hKey,hCoord.1,hCoord.2.1,hCoord.2.2.1,Nat.add_assoc,hCoord.2.2.2]

/-- A byte of slot one's actual initial value copy is read by the first PV
group, and the final O1 acquisition orders its write before the overlapping
stage-one staging write. The witnesses describe one arbitrary operand coordinate. -/
theorem initialValueCopyBeforeSecondStaging {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {writer : EvId} {a : Acc} {data : List Byte}
    (hStage : Thread.StageStagingWrite X writer 1 a data)
    (fragment : Fin 8) {col k byte : Nat} (hCol : col < 128) (hK : k < 16) (hByte : byte < 2)
    (hStoreCovers : a.Covers (initialValueByte l (writer.1/l.block) fragment col k byte)) :
    let loc := initialValueByte l (writer.1/l.block) fragment col k byte
    ∃ (issue : EvId) (group : PublishedCopyGroup l X issue) (j : Nat) (s : Spec)
        (source : List Byte) (mma : EvId) (value : Option Byte),
      X.AsyncArrive issue (Thread.Loader.readyObject l writer.1 1) true ∧
      LoaderReady.generation l X issue 1 = 0 ∧ (j,s) ∈ group.copies ∧
      X.MemWrites (.async (issue.1,j) (.write .copy)) s.dst source ∧ s.dst.Covers loc ∧
      X.MmaRead mma true (qkByteIndex col k byte) loc value ∧
      ByteCausality l X loc (.async (issue.1,j) (.write .copy)) (.thread writer) := by
  let loc := initialValueByte l (writer.1/l.block) fragment col k byte
  obtain ⟨oWait,hoWait,hLater⟩ := Thread.StageStagingWrite.secondAcquire hp hX hStage
  obtain ⟨commit,spec,scope,hCommit,hCta,hObserved⟩ :=
    Thread.secondOutputAcquireReads hp hX hoWait
  have gc := hCommit.issuerWarp hp hX
  obtain ⟨cursor,hWord,wait,hReady,hBefore,hOrdinal⟩ :=
    Thread.initialValueMatchedReplyWithAcquire hp hX hCommit
  have hUse : MmaReady.uses (Thread.Mma.atPrefix l X commit.1 wait) = 1 := by
    have hTotal := Thread.Mma.readyUsesAtPrefix hp hX
      (PTX.Proof.event_thread_lt hX hCommit.decoded) gc wait
    exact hTotal.symm.trans hOrdinal
  have hCursor := (MmaReady.followsOperands hp hX gc).cursor wait
  rw [hUse] at hCursor
  have hZero : (Thread.Mma.atPrefix l X commit.1 wait).kvAcquires 1 = 0 := hCursor 1
  obtain ⟨completion⟩ := LoaderReady.completedForObservedIssuer hp hX gc
    (fun h hc => hCommit.sameReleaseIssuer hp hX h hc) hReady
    (LoaderReady.actualEmptyGuardLower hp hX commit.1 1)
  rw [hZero] at completion
  obtain ⟨mma,d,op,accum,mask,hIssue,hB,hReply,hCommitOrder⟩ :=
    cursor.actualValueFragmentB hp hX hCommit hWord 0 fragment
  have hMma : X.MmaIssue mma d op accum mask := ⟨_,hIssue⟩
  have hReadyOrder := hBefore.trans hReply
  have hOwner : mma.1 / l.block = writer.1 / l.block := by
    rw [hCommitOrder.1,← hLater.1]
    exact hCta.2.2
  let block := Thread.firstPvBlock cursor.steady 0
  have hLoc : op.byteLoc .b (qkByteIndex col k byte) = some loc := by
    rw [hIssue.valueByteLoc hp hX hB]
    change (Mma.pvOperands l mma.1 block fragment 1).byteLoc .b (qkByteIndex col k byte) = _
    rw [pvValueByteLoc l mma.1 block fragment 1 hp.shared.1 hCol hK hByte]
    simp [Mma.kvSlot,loc,initialValueByte,hOwner]
  let key := pvKeyRow fragment k
  have hKey : key < 128 := by
    have := fragment.isLt
    dsimp [key,pvKeyRow]
    omega
  let lane : Fin 64 := ⟨8*(key%8)+(col%64)/8,by omega⟩
  let pair : Fin 16 := ⟨key/8,by omega⟩
  let off := 2*(col%8)+byte
  have hOff : off < 16 := by dsimp [off]; omega
  have hVector : loc = ⟨.shared,(commit.1,wait).1 / l.block,
      kvCopyAddress l.sharedBase (1 : Fin 3) lane pair (decide (64≤col)) + off⟩ := by
    simp [loc,initialValueByte,key,lane,pair,off,← hCommitOrder.1,hOwner,Nat.add_assoc]
  obtain ⟨publication,group,j,s,bytes,hPub,_,hGeneration,_,_,hMember,_,hCover,hWrite,hOrder⟩ :=
    completion.actualOperandCoveringCopyWithPublication hp hX (isB := true)
      (index := qkByteIndex col k byte) lane pair (decide (64 ≤ col)) hOff hMma hReadyOrder hLoc
      hVector
  obtain ⟨hObservedDone,hScope,hRead⟩ := hObserved (isB := true) hMma hCommitOrder.1
    hCommitOrder.2.1 hLoc
  obtain ⟨value,hValue⟩ := hRead
  have hStageWrite : X.MemWrites (.thread writer) a data := .inl hStage.writes
  have hSame : commit.1/l.block = writer.1/l.block := by
    rw [← hCommitOrder.1]
    exact hOwner
  have hPub' : X.AsyncArrive publication (Thread.Loader.readyObject l writer.1 1) true := by
    simpa only [Thread.Loader.readyObject,Prod.fst,hSame] using hPub
  exact ⟨publication,group,j,s,bytes,mma,value,hPub',hGeneration,hMember,hWrite,hCover,hValue,
    .commitOperand rfl ⟨s.dst,hWrite.intent,hCover⟩ (.inl ⟨d,op,accum,mask,hMma⟩)
      ⟨value,hValue⟩ (.direct hOrder) ⟨scope,hObservedDone,hScope⟩ hLater
      ⟨a,.inl ⟨true,hStageWrite.intent⟩,hStoreCovers⟩⟩

/-- An actual published phase-zero copy to slot one precedes every overlapping
stage-one staging byte from the same CTA. The proof uses the actual PV read of that byte. -/
theorem initialValuePublicationBeforeSecondStaging {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {publication writer : EvId} {j : Nat} {s : Spec} {a : Acc} {data : List Byte} {loc : Loc}
    (group : PublishedCopyGroup l X publication)
    (hPub : X.AsyncArrive publication (Thread.Loader.readyObject l writer.1 1) true)
    (hInitial : LoaderReady.generation l X publication 1 = 0) (hMember : (j,s) ∈ group.copies)
    (hCopy : s.dst.Covers loc) (hStage : Thread.StageStagingWrite X writer 1 a data)
    (hStore : a.Covers loc) :
    ByteCausality l X loc (.async (publication.1,j) (.write .copy)) (.thread writer) := by
  obtain ⟨pair,upper,hDest⟩ := group.destination hp hX hPub hMember
  have hSlot := group.slotFor hp hX hPub
  have hCta := LoaderReady.publicationCta hp hX hPub
  let lane : Fin 64 := ⟨(publication.1%l.block)%64,Nat.mod_lt _ (by decide)⟩
  let base := kvCopyAddress l.sharedBase 1 lane pair upper
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
  obtain ⟨fragment,col,k,byte,hCol,hK,hByte,hAt⟩ :=
    initialValueByteOfVector l (writer.1/l.block) lane pair upper hOff
  change initialValueByte l (writer.1/l.block) fragment col k byte = _ at hAt
  rw [← hLoc] at hAt
  obtain ⟨other,selected,otherIndex,spec,bytes,mma,observed,
      hOther,hPhase,hSelected,_,hCover,_,hOrder⟩ :=
    initialValueCopyBeforeSecondStaging hp hX hStage fragment hCol hK hByte (hAt.symm ▸ hStore)
  change spec.dst.Covers (initialValueByte l (writer.1/l.block) fragment col k byte) at hCover
  rw [hAt] at hCover hOrder
  obtain ⟨rfl,rfl⟩ := LoaderReady.coveringCopyUniqueInGeneration hp hX group selected hPub hOther
    (hInitial.trans hPhase.symm) hMember hSelected hCopy hCover
  exact hOrder

end
end PTX.Kernels.TmlFa4Fwd.Protocol.Output
