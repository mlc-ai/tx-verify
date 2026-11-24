-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.ObservedPrimingKey
public import Kernels.TmlFa4Fwd.Proof.Protocol.OperandOutputReuse
public import Kernels.TmlFa4Fwd.Proof.Thread.InitialQueryStagingRoute
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaInitialKeyReady
import Kernels.TmlFa4Fwd.Proof.Thread.SingleVisitCacheCopies
import Kernels.TmlFa4Fwd.Proof.Thread.TerminalStatisticsWrites
import Kernels.TmlFa4Fwd.Proof.Thread.SharedScratchWrites
import Kernels.TmlFa4Fwd.Proof.InputActualSources
import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderPhaseAlignment
import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderReuseOrder
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderCopyPublicationGroup
import Kernels.TmlFa4Fwd.Proof.Thread.InitialKeyReleaseOrder

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX PTX.AsyncCopy Thread
open PTX.Kernels.TmlFa4Fwd.Mma

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

theorem observedInitialKeyPhase {stage : Fin 2} {mma final : EvId} {s : TcCommit.Spec}
    (hInit : Thread.Mma.InitialQueryFragment X stage mma) (hFinal : SecondOutputCommit X final s)
    (hLane : mma.1 = final.1) :
    ∃ wait, TraceBefore X (mma.1, wait) mma ∧
      Nonempty (LoaderReady.Completed l X (mma.1, wait) 0 0) := by
  obtain ⟨wait, hPoll, hBefore, hOrdinal⟩ := hInit.keyReady hp hX hFinal hLane
  have hWarp := hLane.symm ▸ hFinal.issuerWarp hp hX
  have hIssuer {g i : Nat} {form : Thread.Mma.ReleaseForm} {s' : TcCommit.Spec}
      (hRelease : Thread.Mma.ReleaseIssue X g i form s')
      (hCta : mma.1 / l.block = g / l.block) : mma.1 = g :=
    hLane.trans (hFinal.sameReleaseIssuer hp hX hRelease (hLane ▸ hCta))
  obtain ⟨complete⟩ := LoaderReady.completedForObservedIssuer hp hX hWarp hIssuer hPoll
    (LoaderReady.actualEmptyGuardLower hp hX mma.1 0)
  rw [hOrdinal] at complete
  exact ⟨wait, hBefore, ⟨complete⟩⟩

private theorem initialKeyReadBeforeSecondStaging {writer : EvId} {stage : Fin 2}
    {producer consumer commit wait issue d index : Nat} {op : TcMma.OperandSpec} {accum : Bool}
    {mask : List Nat} {a : Acc} {data : List Byte} {loc : Loc}
    (hPhase : Softmax.FirstQkPhase l X stage producer consumer commit wait)
    (hStore : StageStagingWrite X writer 1 a data)
    (hOwner : producer / l.block = writer.1 / l.block)
    (hMma : X.MmaIssue (producer, issue) d op accum mask) (hLoc : op.byteLoc .b index = some loc)
    (hShared : loc.space = .shared) (hLocCta : loc.cta = writer.1 / l.block) :
    modelCausality l X loc (.async (producer, issue) (.mmaRead true index)) (.thread writer) := by
  obtain ⟨wait₀, fence, hAcquire₀, _, hBefore, hAfter⟩ :=
    hStore.firstAcquireFenceBeforeSecond hp hX
  obtain ⟨first, s₀, _, hFirst, hCta₀, _⟩ := firstOutputAcquireReads hp hX hAcquire₀
  obtain ⟨wait₁, hAcquire₁, hLater⟩ := hStore.secondAcquire hp hX
  obtain ⟨second, s₁, _, hSecond, hCta₁, _⟩ := secondOutputAcquireReads hp hX hAcquire₁
  have hWait₀ : wait₀.1 = writer.1 := hBefore.1.trans hAfter.1
  have hCtaFirst : first.1 / l.block = writer.1 / l.block :=
    hCta₀.2.2.trans (congrArg (· / l.block) hWait₀)
  have hCtaSecond : second.1 / l.block = writer.1 / l.block :=
    hCta₁.2.2.trans (congrArg (· / l.block) hLater.1)
  have hCta : SameCta l first.1 second.1 :=
    ⟨hCta₀.1, hCta₁.1, hCtaFirst.trans hCtaSecond.symm⟩
  have hIssuer := firstQkOutputIssuer hp hX hPhase hFirst (hOwner.trans hCtaFirst.symm)
  have hLane := hIssuer.trans (finalOutputCommitsInOrder hp hX hCta hFirst hSecond).1
  have hWriter := hLater.1 ▸ hCta₁.2.1
  obtain ⟨_, _, hOrder⟩ := Protocol.Output.mmaOperandBeforeSecondStaging hp hX (isB := true)
    hStore hSecond ⟨hCta₁.1, hWriter, hCtaSecond⟩ hLane hMma hLoc hShared hLocCta
  exact hOrder

private theorem keyByteStableOfCacheOrder {stage : Fin 2}
    {producer consumer commit wait issue d index : Nat} {op : TcMma.OperandSpec} {accum : Bool}
    {mask : List Nat} (hPhase : Softmax.FirstQkPhase l X stage producer consumer commit wait)
    (hMma : X.MmaIssue (producer, issue) d op accum mask) {copy : EvId} {loc : Loc}
    (hCache : ∀ other s, X.Copy other s → s.dst.Covers loc →
      other = copy ∨ modelCausality l X loc
        (.async (producer, issue) (.mmaRead true index)) (.async other (.write .copy)))
    (hLoc : op.byteLoc .b index = some loc) (hShared : loc.space = .shared)
    (hLocCta : loc.cta = producer / l.block) (hLower : l.sharedBase + 68608 ≤ loc.addr)
    (hUpper : loc.addr < l.sharedBase + 166912) {other : Ref} {a : Acc} {bs : List Byte}
    (hWrite : X.MemWrites other a bs) (hCover : a.Covers loc) :
    other = .async copy (.write .copy) ∨
      modelCausality l X loc (.async (producer, issue) (.mmaRead true index)) other := by
  rcases sharedWriteSource hX hWrite hCover hShared with hThread | hTensor | hOrdinary
  · obtain ⟨writer, rfl, hWriter⟩ := hThread
    rcases ordinarySharedWriteBelowOrStaging hp hX hWriter hCover hShared with hScratch | hStaging
    · omega
    obtain ⟨out, box, col, row, hCol, hRow, rfl, hStage⟩ := hStaging.stageElement hp hX
    have hAt : loc.cta = writer.1 / l.block := hCover.2.1
    have hCta := hLocCta.symm.trans hAt
    have hOut : out = 1 := by
      by_contra hNe
      have hOut : out = 0 := Fin.ext (by have := out.isLt; omega)
      subst out
      have hXor : col / 4 ^^^ (row % 8) < 2 ^ 3 :=
        Nat.xor_lt_two_pow (by omega) (by omega)
      have hBox := box.isLt
      have hLimit := hCover.2.2.2
      change loc.addr < (Correction.outputElementAccess l writer.1 0 box col row).loc.addr + 4
        at hLimit
      simp only [Correction.outputElementAccess, Correction.outputChunkLoc, Epilogue.sharedSlot,
        Loc.at, Fin.val_zero, Nat.mul_zero, Nat.add_zero] at hLimit
      omega
    subst out
    exact .inr (initialKeyReadBeforeSecondStaging hp hX hPhase hStage hCta hMma hLoc hShared hAt)
  · obtain ⟨other, x, y, byte, rfl⟩ := hTensor
    exact (tensorInputWriteDoesNotCoverKv hp hX hWrite hLower hUpper hCover).elim
  · obtain ⟨other, s, rfl, hOther, rfl⟩ := hOrdinary
    exact (hCache other s hOther hCover).elim (fun hEq => .inl (by rw [hEq])) .inr

private theorem openingKeyCopyOrder (hDone : Complete l X) {stage : Fin 2}
    {mma final publication : EvId} {spec : TcCommit.Spec} {owner : Nat}
    (hInit : Thread.Mma.InitialQueryFragment X stage mma) (hFinal : SecondOutputCommit X final spec)
    (hIssuer : mma.1 = final.1) (hOwner : owner/l.block = mma.1/l.block)
    (group : Thread.Loader.PublishedCopyGroup l X publication)
    (hPub : X.AsyncArrive publication (Thread.Loader.readyObject l owner 0) true)
    (hGeneration : LoaderReady.generation l X publication 0 = 0) {j : Nat} {s : AsyncCopy.Spec}
    (hMember : (j,s) ∈ group.copies) {loc : Loc} (hCover : s.dst.Covers loc)
    {op : TcMma.OperandSpec} {d index : Nat} {accum : Bool} {mask : List Nat}
    (hMma : X.MmaIssue mma d op accum mask) (hAt : op.byteLoc .b index = some loc) {other : EvId}
    {t : AsyncCopy.Spec} (hOther : X.Copy other t) (hOverlap : t.dst.Covers loc) :
    other = (publication.1,j) ∨ modelCausality l X loc
      (.async mma (.mmaRead true index)) (.async other (.write .copy)) := by
  obtain ⟨otherPc,hGet⟩ := hOther
  have hExit := Thread.exitedOfComplete hX hDone (PTX.Proof.event_thread_lt hX hGet)
  obtain ⟨next,target,later,hLane,hNext,hLater⟩ :=
    Thread.Loader.copyPublicationMemberAtExit hp hX ⟨otherPc,hGet⟩ hExit
  have hNext' := group.overlappingReadySlot hp hX later hPub hNext hMember hLater hCover hOverlap
  rcases Nat.eq_zero_or_pos (LoaderReady.generation l X next 0) with hSame | hPositive
  · obtain ⟨hEqual,hIndex⟩ := LoaderReady.coveringCopyUniqueInGeneration hp hX
      group later hPub hNext' (hGeneration.trans hSame.symm)
      hMember hLater hCover hOverlap
    exact .inl (Prod.ext (hLane.symm.trans (congrArg Prod.fst hEqual).symm) hIndex.symm)
  · let n := LoaderReady.generation l X next 0 - 1
    have hSucc : LoaderReady.generation l X next 0 = n + 1 := by dsimp [n]; omega
    obtain ⟨guard,g,k,release,_,hSeen⟩ :=
      LoaderReady.actualReleaseForNextPublicationExact hp hX hNext' hSucc
    have hCta : owner/l.block = g/l.block := by
      rw [LoaderReady.publicationCta hp hX hNext',← guard.issuer,release.issuerCta hp hX]
    have hFinalCta : final.1/l.block = g/l.block :=
      (hOwner.trans (congrArg (· / l.block) hIssuer)).symm.trans hCta
    have hG := hIssuer.trans (hFinal.sameReleaseIssuer hp hX release.issue hFinalCta)
    have hRelease : Thread.Mma.ReleaseIssue X mma.1 release.index release.form release.spec :=
      (congrArg (fun lane => Thread.Mma.ReleaseIssue X lane release.index release.form
        release.spec) hG).mpr release.issue
    have hBefore : TraceBefore X mma (g,release.index) :=
      (congrArg (fun lane => TraceBefore X mma (lane,release.index)) hG).mp
        (hInit.beforeCacheRelease hX hRelease)
    have hOrder := LoaderReady.observedOperandBeforeGroupReuse hp hX (isB := true) (index := index)
      guard later release hSeen hMma hBefore hAt hLater hOverlap
    have hOtherId : (next.1,other.2) = other := Prod.ext hLane rfl
    exact .inr (hOtherId ▸ hOrder.2)

/-- The first actual K snapshot of any tile visit count reads the selected cache byte.
Every later overlapping loader vector follows that initial operand read. -/
theorem initialKeyOperandByte (hDone : Complete l X) (hFrame : OutputFootprint p X) {batch : Nat}
    {stage : Fin 2} {producer consumer commit wait issue : Nat} (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ producer / l.block)
    (hHi : producer / l.block < tilePrefix p (batch + 1) * p.heads)
    (hPhase : Softmax.FirstQkPhase l X stage producer consumer commit wait)
    (hInit : Thread.Mma.InitialQueryFragment X stage (producer,issue)) {final : EvId}
    {s : TcCommit.Spec} (hFinal : SecondOutputCommit X final s)
    (hFinalCta : producer / l.block = final.1 / l.block) (step : Fin 8) {row k byte : Nat}
    (hr : row < 128) (hk : k < 16) (hByte : byte < 2) {d : Nat} {accum : Bool} {mask : List Nat}
    (hMma : X.MmaIssue (producer,issue) d
      (qkOperands l producer (Softmax.firstQkBlock stage) step 0) accum mask) :
    let coords := Epilogue.assignedCoordinates p batch (producer / l.block)
    let key := 128 * (trips p batch coords.1 - 1) + row
    ∃ loc, (qkOperands l producer (Softmax.firstQkBlock stage) step 0).byteLoc .b
      (qkByteIndex row k byte) = some loc ∧
      OperandByteSource l X (producer,issue) true (qkByteIndex row k byte) loc
        (if key < p.kLength batch then
          (Value.float .bf16 (qkKey p batch coords.2 key (16 * step.val + k))).byteAt byte
        else zeroByte) := by
  dsimp only
  let block := Softmax.firstQkBlock stage
  have hLane := Thread.Mma.firstQkSecondOutputIssuer hp hX hPhase hFinal hFinalCta
  obtain ⟨ready,hAfter,⟨hReady⟩⟩ := observedInitialKeyPhase hp hX hInit hFinal hLane
  obtain ⟨loc,publication,group,j,spec,hPub,hGeneration,hMember,_,hCover,_,hAt,hValue⟩ :=
    hReady.initialKeyOperandWithPublication hp hX hFrame block step hb hLo hHi hr hk hByte
      hMma hAfter
  have hGeom := qkKCopyByteLoc l producer block step 0 hp.shared.1 hr hk hByte
  have hLoc := Option.some.inj (hAt.symm.trans hGeom)
  let lane := qkLoaderLane step row k
  let off := qkLoaderByte step k byte
  have hOff : off < 16 := by unfold off qkLoaderByte; omega
  have hBounds := kvCopyAddress_range (stage := 0) (lane := lane)
    (group := row / 8) (upper := decide (4 ≤ step.val)) hp.shared.1 (by decide) (by omega) hOff
  rw [hLoc] at hAt hCover hValue
  have hValue' := hValue (fun _ _ _ hw hc =>
    (keyByteStableOfCacheOrder hp hX hPhase hMma
      (fun _ _ hCopy hOverlap => openingKeyCopyOrder hp hX hDone hInit hFinal hLane rfl group hPub
        hGeneration hMember hCover hMma hAt hCopy hOverlap)
      hAt rfl rfl hBounds.1 hBounds.2 hw hc).elim .inl (.inr ∘ .inr))
  exact ⟨_,hAt,hValue'⟩

end PTX.Kernels.TmlFa4Fwd.Protocol
