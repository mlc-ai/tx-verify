-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.ObservedPrimingValue
public import Kernels.TmlFa4Fwd.Proof.Protocol.OperandOutputReuse
public import Kernels.TmlFa4Fwd.Proof.Thread.InitialValueTailAcquire
import Kernels.TmlFa4Fwd.Proof.Thread.SingleVisitCacheCopies
import Kernels.TmlFa4Fwd.Proof.Thread.InitialValuePhase
import Kernels.TmlFa4Fwd.Proof.Thread.InitialValueByteOperands
import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvPipeline
import Kernels.TmlFa4Fwd.Proof.Thread.TerminalStatisticsWrites
import Kernels.TmlFa4Fwd.Proof.Thread.SharedScratchWrites
import Kernels.TmlFa4Fwd.Proof.InputActualSources
import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderPhaseAlignment
import Kernels.TmlFa4Fwd.Proof.MmaValueBytes

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX PTX.Proof PTX.AsyncCopy Thread Prologue Epilogue
open Mma (trips pvOperands pvKeyRow pvLoaderLane pvLoaderByte pvValue
  pvValueByteLoc qkByteIndex sharedDescriptor kvStart pvFragment)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (hDone : Complete l X)
include hp hX hDone

private theorem singleVisitValueByteStable (hFrame : OutputFootprint p X) {batch : Nat} {mma : EvId}
    {d index : Nat} {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat} (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ mma.1/l.block)
    (hHi : mma.1/l.block < tilePrefix p (batch+1) * p.heads)
    (hTrip : trips p batch (assignedCoordinates p batch (mma.1/l.block)).1 = 1)
    (hMma : X.MmaIssue mma d op accum mask) {copy : EvId} {spec : AsyncCopy.Spec}
    (hCopy : X.Copy copy spec) {loc : Loc} (hSource : spec.dst.Covers loc)
    (hOwner : copy.1/l.block = mma.1/l.block) (hLoc : op.byteLoc .b index = some loc)
    (hShared : loc.space = .shared) (hLocCta : loc.cta = mma.1/l.block)
    (hLower : l.sharedBase + 68608 ≤ loc.addr) (hUpper : loc.addr < l.sharedBase + 166912)
    {other : Ref} {a : Acc} {bs : List Byte} (hWrite : X.MemWrites other a bs)
    (hCover : a.Covers loc) :
    other = .async copy (.write .copy) ∨
      modelCausality l X loc (.async mma (.mmaRead true index)) other := by
  rcases sharedWriteSource hX hWrite hCover hShared with hThread | hTensor | hOrdinary
  · obtain ⟨writer,rfl,hWriter⟩ := hThread
    rcases ordinarySharedWriteBelowOrStaging hp hX hWriter hCover hShared with hScratch | hStaging
    · omega
    obtain ⟨out,box,col,row,hCol,hRow,rfl,hStage⟩ := hStaging.stageElement hp hX
    have hAt : loc.cta = writer.1/l.block := hCover.2.1
    have hCta := hLocCta.symm.trans hAt
    have hOut : out = 1 := by
      by_contra hNe
      have hOut : out = 0 := Fin.ext (by have := out.isLt; omega)
      subst out
      have hXor : col/4 ^^^ (row%8) < 2^3 :=
        Nat.xor_lt_two_pow (by omega) (by omega)
      have hBox := box.isLt
      have hLimit := hCover.2.2.2
      change loc.addr < (Correction.outputElementAccess l writer.1 0 box col row).loc.addr + 4
        at hLimit
      simp only [Correction.outputElementAccess,Correction.outputChunkLoc,Epilogue.sharedSlot,
        Loc.at,Fin.val_zero,Nat.mul_zero,Nat.add_zero] at hLimit
      omega
    subst out
    obtain ⟨wait,hWait,hLater⟩ := hStage.secondAcquire hp hX
    obtain ⟨output,s,_,hSecond,hSame,_⟩ := secondOutputAcquireReads hp hX hWait
    have hSame : SameCta l output.1 writer.1 := hLater.1 ▸ hSame
    obtain ⟨steady,hIssue⟩ := initialValueIssuesBeforeSecondOutputCommitExact hp hX hSecond
    obtain ⟨peer,_,_,_,_,_,hPeer,_,hTrace⟩ := hIssue 0 0
    have hPeerCta : mma.1/l.block = peer.1/l.block := by
      rw [hTrace.1]
      exact hCta.trans hSame.2.2.symm
    have hLane := (mmaIssueSameThread hp hX hMma hPeer hPeerCta).trans hTrace.1
    obtain ⟨_,_,hOrder⟩ := Output.mmaOperandBeforeSecondStaging hp hX (isB := true)
      hStage hSecond hSame hLane hMma hLoc hShared hAt
    exact .inr hOrder
  · obtain ⟨other,x,y,byte,rfl⟩ := hTensor
    exact (tensorInputWriteDoesNotCoverKv hp hX hWrite hLower hUpper hCover).elim
  · obtain ⟨other,s,rfl,hOther,rfl⟩ := hOrdinary
    have hEq := Thread.Loader.singleVisitCacheCopyUnique hp hX hDone hFrame
      hb (hOwner.symm ▸ hLo) (hOwner.symm ▸ hHi) (hOwner.symm ▸ hTrip)
      hCopy hOther hSource hCover
    exact .inl (by rw [hEq])

/-- The initial V operand of an actual single-visit PV fragment reads the selected
value-cache byte or its explicit zero fill. The first output proxy fence orders
writes that reuse the same shared region. -/
theorem singleVisitInitialValueOperandByte (hFrame : OutputFootprint p X) {batch : Nat}
    {mma output : EvId} {s : TcCommit.Spec} {d : Nat} {op : TcMma.OperandSpec} {accum : Bool}
    {mask : List Nat} (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ mma.1/l.block)
    (hHi : mma.1/l.block < tilePrefix p (batch+1) * p.heads)
    (hTrip : trips p batch (assignedCoordinates p batch (mma.1/l.block)).1 = 1)
    (hOutput : SecondOutputCommit X output s) (hLane : mma.1 = output.1) (stage : Fin 2)
    (step : Fin 8) {col k byte : Nat} (hc : col < 128) (hk : k < 16) (hByte : byte < 2)
    (hFragment : InitialValueFragment X mma false stage step d op accum mask)
    (hB : op.b = sharedDescriptor (kvStart l 1 + pvFragment step) 16384)
    (hMma : X.MmaIssue mma d op accum mask) :
    let head := (assignedCoordinates p batch (mma.1/l.block)).2
    let key := pvKeyRow step k
    ∃ loc, op.byteLoc .b (qkByteIndex col k byte) = some loc ∧
      Mma.OperandByteSource l X mma true (qkByteIndex col k byte) loc
        (if key < p.kLength batch then
          (Value.float .bf16 (pvValue p batch head key col)).byteAt byte
        else zeroByte) := by
  dsimp only
  obtain ⟨wait,hPoll,hAfter,hOrdinal⟩ := hFragment.readyBeforeTail hp hX hOutput hLane
  have hWarp := hLane.symm ▸ hOutput.issuerWarp hp hX
  have hIssuer {g i : Nat} {form : Thread.Mma.ReleaseForm} {spec : TcCommit.Spec}
      (hRelease : Thread.Mma.ReleaseIssue X g i form spec)
      (hCta : mma.1/l.block = g/l.block) : mma.1 = g :=
    hLane.trans (hOutput.sameReleaseIssuer hp hX hRelease (hLane ▸ hCta))
  obtain ⟨_,hEvent⟩ := hMma
  have hThread := event_thread_lt hX hEvent
  obtain ⟨hReady⟩ := LoaderReady.completedForObservedIssuer hp hX hWarp hIssuer hPoll
    (LoaderReady.actualEmptyGuardLower hp hX mma.1 1)
  rw [Mma.initialValueReadyPhaseZero hp hX hThread hWarp hOrdinal] at hReady
  obtain ⟨loc,copy,spec,hCopy,hCover,hOwner,hAt,hValue⟩ :=
    hReady.initialValueOperand hp hX hFrame stage step hb hLo hHi hc hk hByte hFragment
      hB ⟨_,hEvent⟩ hAfter
  have hPhysical := Thread.InitialValueFragment.valueByteLoc hp hX hFragment hB
    (qkByteIndex col k byte)
  rw [pvValueByteLoc l mma.1 (firstPvBlock false stage) step 1 hp.shared.1 hc hk hByte]
    at hPhysical
  have hLoc := Option.some.inj (hAt.symm.trans hPhysical)
  let lane := pvLoaderLane step col k
  let off := pvLoaderByte col byte
  have hOff : off < 16 := by unfold off pvLoaderByte; omega
  have hRow : pvKeyRow step k < 128 := by unfold pvKeyRow; have := step.isLt; omega
  have hBounds := kvCopyAddress_range (stage := 1) (lane := lane)
    (group := pvKeyRow step k / 8) (upper := decide (64 ≤ col)) hp.shared.1
    (by decide) (by omega) hOff
  have hExact : loc = ⟨.shared,mma.1/l.block,
      kvCopyAddress l.sharedBase 1 lane (pvKeyRow step k / 8) (decide (64 ≤ col)) + off⟩ := by
    simpa [off,lane,pvLoaderLane,pvLoaderByte,Mma.kvSlot,Nat.add_assoc] using hLoc
  rw [hExact] at hAt hCover hValue
  have hValue' := hValue (fun _ _ _ hw hc =>
    (singleVisitValueByteStable hp hX hDone hFrame hb hLo hHi hTrip ⟨_,hEvent⟩ hCopy hCover hOwner
      hAt rfl rfl hBounds.1 hBounds.2 hw hc).elim .inl (.inr ∘ .inr))
  exact ⟨_,hAt,by simpa only [hTrip,Nat.sub_self,Nat.mul_zero,Nat.zero_add] using hValue'⟩

end PTX.Kernels.TmlFa4Fwd.Protocol
