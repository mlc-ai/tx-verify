-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.ObservedCacheOperandElements
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPublishedValueCopySize
import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderCopyBytes
import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderPhaseAlignment
import Kernels.TmlFa4Fwd.Proof.MmaValueBytes
public import Kernels.TmlFa4Fwd.Proof.MmaPvResult

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.AsyncCopy PTX.TcMma Thread Thread.Loader
open PTX.Kernels.TmlFa4Fwd.Mma
  (qkByteIndex pvLoaderByte pvLoaderLane pvLoaderCoordinates pvKeyRow pvValue
  pvOperands pvValueByteLoc kvSlot trips)
open PTX.Kernels.TmlFa4Fwd.Loader (kvUseStage kvUseStage_val)
open Epilogue (assignedCoordinates assignedCoordinates_valid)

/-- A recurring PV B byte selects the launch V value at the fragment's exact
logical visit. Every overlapping writer is ordered around that read. -/
theorem recurringValueOperandByteInPrefix {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g index : Nat} {block : Fin 4} {step : Fin 8}
    {d : Nat} {op : OperandSpec} {accum : Bool} {mask : List Nat}
    (hIssue : PvInstruction X (g,index) block step d op accum mask)
    {use batch col k byte : Nat} (hUse : Thread.Mma.LatestValueReadyUse l X g index use)
    (hRepeat : 2 ≤ use) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hc : col < 128) (hk : k < 16) (hbByte : byte < 2) :
    let co := assignedCoordinates p batch (g/l.block)
    let key := 128*(trips p batch co.1-1-use/2)+pvKeyRow step k
    key < p.kLength batch ∧
      ∃ loc, op.byteLoc .b (qkByteIndex col k byte) = some loc ∧
        Mma.OperandByteSource l X (g,index) true (qkByteIndex col k byte) loc
          ((Value.float .bf16 (pvValue p batch co.2 key col)).byteAt byte) := by
  let co := assignedCoordinates p batch (g/l.block)
  let tile := trips p batch co.1-1-use/2
  let key := 128*tile+pvKeyRow step k
  obtain ⟨actual,wait,hActual,⟨hReady⟩,hEarlier,hBytes⟩ :=
    valueOperandReadyInPrefix hp hX hIssue
  have hExact := hActual.unique hUse
  rw [hExact] at hReady hBytes
  have hRowBound : pvKeyRow step k < 128 := by unfold pvKeyRow; have := step.isLt; omega
  let lane : Fin 64 := ⟨pvLoaderLane step col k,by unfold pvLoaderLane; omega⟩
  let pair : Fin 16 := ⟨pvKeyRow step k/8,by omega⟩
  let upper := decide (64 ≤ col)
  let off := pvLoaderByte col byte
  let dst := kvCopyAddress l.sharedBase (kvUseStage use) lane pair upper
  let loc : Loc := ⟨.shared,g/l.block,dst+off⟩
  have hAt : op.byteLoc .b (qkByteIndex col k byte) = some loc := by
    rw [hBytes]
    change (pvOperands l g block step use).byteLoc .b (qkByteIndex col k byte) = some loc
    simpa only [loc,dst,lane,pair,upper,off,kvUseStage_val,kvSlot,pvLoaderLane,pvLoaderByte,
      Nat.add_assoc] using pvValueByteLoc l g block step use hp.shared.1 hc hk hbByte
  obtain ⟨hRow,hColumn,hBit,hOff⟩ := pvLoaderCoordinates step tile (k := k) hc hbByte
  have hMma : X.MmaIssue (g,index) d op accum mask := ⟨_,hIssue.decoded⟩
  obtain ⟨pub,group,j,spec,bs,hPub,hLane,hPhase,_,hPlane,hMember,hLoc,hCover,hWrite,hOrder⟩ :=
    hReady.actualOperandCoveringCopyWithPublication hp hX
      (isB := true) lane pair upper hOff hMma hEarlier hAt rfl
  have hPub' : X.AsyncArrive pub (readyObject l g (kvUseStage use)) true := hPub
  have hOwner : pub.1/l.block = g/l.block := (publicationCta hp hX hPub').symm
  have hOdd : use%2 = 1 := by obtain ⟨_,_,_,hOdd,_,_⟩ := hUse; exact hOdd
  have hValue : group.publication.packet.plane = .value := by
    change group.publication.packet.plane =
      (if (3*(use/3)+(kvUseStage use).val)%2 = 0 then .key else .value) at hPlane
    rw [kvUseStage_val,show 3*(use/3)+use%3 = use by omega,hOdd] at hPlane
    exact hPlane
  obtain ⟨supplier,publication⟩ := pub
  obtain ⟨b,hB,visit,otherPair,otherUpper,hSource,hVisit,hDst⟩ :=
    group.memberValueLocation hp hX hFrame hPub' hPhase hRepeat hValue hMember
  have hFull := group.recurringValueMemberFullSize hp hX hFrame hPub' hPhase hRepeat hValue hMember
  have hActive : g/l.block < tilePrefix p p.batch*p.heads :=
    hHi.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p (by omega)))
  obtain ⟨_,_,hUnique⟩ := tileBatch_existsUnique p hActive
  obtain ⟨hLo',hHi'⟩ := hSource.selected
  rw [hOwner] at hLo' hHi'
  have hBatch := (hUnique b ⟨hB,hLo',hHi'⟩).trans (hUnique batch ⟨hb,hLo,hHi⟩).symm
  subst b
  have hTid : (supplier%l.block)%64 = lane.val := by
    have hSupplier : supplier = producer l (g/l.block) lane := hLane
    rw [hSupplier]
    exact producerLaneMod hp _ _
  have hAddresses := congrArg Loc.addr hLoc
  rw [hDst] at hAddresses
  change kvCopyAddress l.sharedBase (kvUseStage use) (supplier%l.block) otherPair otherUpper+off =
    dst+off at hAddresses
  have hTarget : kvCopyAddress l.sharedBase (kvUseStage use) (supplier%l.block) pair upper =
      dst := by unfold dst kvCopyAddress; rw [hTid,Nat.mod_eq_of_lt lane.isLt]
  have hCoords : otherPair = pair ∧ otherUpper = upper := by
    by_contra! hApart
    have hDifferent : otherPair.val ≠ pair.val ∨ otherUpper ≠ upper := by
      by_cases eq : otherPair.val = pair.val
      · exact .inr (hApart (Fin.ext eq))
      · exact .inl eq
    have hGap := kvCopyAddress_apart (stage := kvUseStage use) (lane := supplier%l.block)
      hp.shared.1 otherPair.isLt pair.isLt hDifferent
    omega
  obtain ⟨rfl,rfl⟩ := hCoords
  obtain ⟨hValid,hSrc⟩ := hSource.address
  have hVisit' : visit = use/2 := by omega
  subst visit
  have hRow' : kvCopyRow tile (supplier%l.block) pair.val = key := by
    have hMod := congrArg (fun n : Nat => n/8%8) hTid
    have hRed : (supplier%l.block%64)/8%8 = (supplier%l.block)/8%8 := by omega
    rw [hRed] at hMod
    change kvCopyRow tile lane.val pair.val = key at hRow
    unfold kvCopyRow at hRow ⊢
    omega
  change kvCopyRow (trips p batch (assignedCoordinates p batch (supplier/l.block)).1-1-use/2)
    (supplier%l.block) pair.val < p.kLength batch at hValid
  rw [hOwner] at hValid hSrc
  change kvCopyRow tile (supplier%l.block) pair.val < p.kLength batch at hValid
  change spec.src.loc = p.vLayout.loc (p.page batch (kvCopyRow tile (supplier%l.block) pair.val/16))
    (co.2/6) (kvCopyRow tile (supplier%l.block) pair.val%16)
    (kvCopyColumn (supplier%l.block) upper) at hSrc
  rw [hRow'] at hValid hSrc
  have hDimension : kvCopyColumn (supplier%l.block) upper+off/2 = col := by
    have hMod := congrArg (fun n : Nat => n%8) hTid
    rw [Nat.mod_mod_of_dvd _ (by decide : 8 ∣ 64)] at hMod
    unfold kvCopyColumn at hColumn ⊢
    exact hMod.symm ▸ hColumn
  have hHead := (assignedCoordinates_valid hp hLo hHi).2
  have hh : co.2/6 < p.kvHeads := by unfold Params.heads at hHead; unfold co; omega
  have hSize : spec.src.size = if key < p.kLength batch then 16 else 0 := by
    rw [hFull,ite_eq_left hValid]
  have hSourceLoc : spec.src.loc = cacheVector p group.publication.packet.plane batch (co.2/6)
      key (supplier%l.block) upper := by
    rw [hValue]
    exact hSrc
  have hStable := fun other a data hWriter hOverlap =>
    valueOperandWriterOrder hp hX hIssue hUse hPub' hPhase hMember hAt hCover
      (other := other) (a := a) (data := data) hWriter hOverlap
  have hResult := publishedCopyOperandByteSource hp hX hFrame group hMember hb hh upper
    (fun _ => hSourceLoc) hSize hOff hWrite (hLoc.symm ▸ hOrder) (hLoc.symm ▸ hStable)
  rw [hLoc,hValue,ite_eq_left hValid] at hResult
  change off%2 = byte at hBit
  change Mma.OperandByteSource l X (g,index) true (qkByteIndex col k byte) loc
    ((Value.float .bf16 (p.v (p.page batch (key/16)) (co.2/6) (key%16)
      (kvCopyColumn (supplier%l.block) upper+off/2))).byteAt (off%2)) at hResult
  rw [hDimension,hBit] at hResult
  refine ⟨hValid,loc,hAt,?_⟩
  change Mma.OperandByteSource l X (g,index) true (qkByteIndex col k byte) loc
    ((Value.float .bf16 (pvValue p batch co.2 key col)).byteAt byte)
  simpa only [pvValue,ite_eq_left hValid] using hResult

end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
