-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.RecurringKeyReadyWords
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPublishedKeyLocation
public import Kernels.TmlFa4Fwd.Proof.MmaKeyValues
import Kernels.TmlFa4Fwd.Proof.Protocol.CacheSourceBytes

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.AsyncCopy PTX.TcMma PTX.Flow PTX.Proof Thread Thread.Loader
open Mma (qkByteIndex qkLoaderByte qkLoaderLane qkLoaderCoordinates qkPlaneColumn_lt
  recurringKeyBlock qkKCopyByteLoc qkOperands)
open Loader (kvUseStage kvUseStage_val)
open Epilogue (assignedCoordinates assignedCoordinates_valid)

noncomputable section

/-- An actual recurring B read selects its launch key byte at the ready cursor's visit.
The source-length alternative follows the recorded copy's decoded size. -/
theorem recurringKeyOperandCopyValue {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) (stage : Fin 2) {g index : Nat} {step : Fin 8}
    {d : Nat} {op : OperandSpec} {accum : Bool} {mask : List Nat}
    (hIssue : QkInstruction X (g,index) (recurringKeyBlock stage) step d op accum mask)
    {batch row k byte : Nat} (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (hr : row < 128) (hk : k < 16) (hbByte : byte < 2) :
    let a := Thread.Mma.atPrefix l X g index
    let use := a.kvAcquires 0+a.kvAcquires 1+a.kvAcquires 2-1
    let co := assignedCoordinates p batch (g/l.block)
    let key := 128*(Mma.trips p batch co.1-1-use/2)+row
    let expected := (Value.float .bf16
      (p.k (p.page batch (key/16)) (co.2/6) (key%16) (16*step.val+k))).byteAt byte
    ∃ (pub : EvId) (group : PublishedCopyGroup l X pub) (j : Nat) (spec : Spec)
        (bs : List Byte) (loc : Loc),
      X.AsyncArrive pub (readyObject l g (kvUseStage use)) true ∧
      generation l X pub (kvUseStage use) = use/3 ∧ (j,spec) ∈ group.copies ∧
      key < p.kLength batch ∧ op.byteLoc .b (qkByteIndex row k byte) = some loc ∧
      X.MemWrites (.async (pub.1,j) (.write .copy)) spec.dst bs ∧ spec.dst.Covers loc ∧
      modelCausality l X loc (.async (pub.1,j) (.write .copy))
        (.async (g,index) (.mmaRead true (qkByteIndex row k byte))) ∧
      wbyte spec.dst bs loc = some
        (if qkLoaderByte step k byte < spec.src.size then expected else zeroByte) := by
  let state := Thread.Mma.atPrefix l X g index
  let use := state.kvAcquires 0+state.kvAcquires 1+state.kvAcquires 2-1
  obtain ⟨_,_,hUse⟩ := hIssue.recurringKeyOperandOfPositiveEvenReadyUse hp hX stage
  obtain ⟨wait,actual,⟨hReady⟩,hEarlier,hActual,hEven,hBytes⟩ :=
    recurringKeyFragmentReadyBytesOfEvenUse hp hX stage hIssue
  change actual = use at hActual
  rw [hActual] at hReady hEven hBytes
  let lane : Fin 64 := ⟨qkLoaderLane step row k,by
    have hColumn := qkPlaneColumn_lt step hk
    unfold qkLoaderLane
    omega⟩
  let pair : Fin 16 := ⟨row/8,by omega⟩
  let upper := decide (4 ≤ step.val)
  let off := qkLoaderByte step k byte
  let dst := kvCopyAddress l.sharedBase (kvUseStage use) lane pair upper
  let loc : Loc := ⟨.shared,g/l.block,dst+off⟩
  let co := assignedCoordinates p batch (g/l.block)
  let tile := Mma.trips p batch co.1-1-use/2
  let key := 128*tile+row
  have hAt : op.byteLoc .b (qkByteIndex row k byte) = some loc := by
    rw [hBytes]
    change (qkOperands l g (recurringKeyBlock stage) step use).byteLoc .b
      (qkByteIndex row k byte) = some loc
    rw [qkKCopyByteLoc l g _ step use hp.shared.1 hr hk hbByte]
    rfl
  have hMma : X.MmaIssue (g,index) d op accum mask := ⟨_,hIssue.decoded⟩
  obtain ⟨hRow,hDim,hByte,hOff⟩ := qkLoaderCoordinates step tile (row := row) hk hbByte
  obtain ⟨pub,group,j,spec,bs,hPub,hLane,hPhase,_,hPlane,hMember,hLoc,hCover,hWrite,hOrder⟩ :=
    hReady.actualOperandCoveringCopyWithPublication hp hX
      (isB := true) lane pair upper hOff hMma hEarlier hAt rfl
  have hPub' : X.AsyncArrive pub (readyObject l g (kvUseStage use)) true := hPub
  have hOwner : pub.1/l.block = g/l.block := (publicationCta hp hX hPub').symm
  have hKey : group.publication.packet.plane = .key := by
    change group.publication.packet.plane =
      (if (3*(use/3)+(kvUseStage use).val)%2 = 0 then .key else .value) at hPlane
    rw [kvUseStage_val,show 3*(use/3)+use%3 = use by omega,hEven] at hPlane
    exact hPlane
  obtain ⟨supplier,index'⟩ := pub
  obtain ⟨b,hB,visit,other,plane,hSource,hVisit,hDst⟩ :=
    group.memberKeyLocation hp hX hFrame hPub' hPhase hUse hKey hMember
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
  change kvCopyAddress l.sharedBase (kvUseStage use) (supplier%l.block) other plane+off =
    dst+off at hAddresses
  have hTarget : kvCopyAddress l.sharedBase (kvUseStage use) (supplier%l.block) pair upper =
      dst := by
    unfold dst kvCopyAddress
    rw [hTid,Nat.mod_eq_of_lt lane.isLt]
  have hPair : other.val = pair.val ∧ plane = upper := by
    by_contra! hApart
    have hDifferent : other.val ≠ pair.val ∨ plane ≠ upper := by
      by_cases eq : other.val = pair.val
      · exact .inr (hApart eq)
      · exact .inl eq
    have hGap := kvCopyAddress_apart (stage := kvUseStage use) (lane := supplier%l.block)
      hp.shared.1 other.isLt pair.isLt hDifferent
    omega
  have hPair' : other = pair := Fin.ext hPair.1
  obtain ⟨_,rfl⟩ := hPair
  subst other
  obtain ⟨hValid,hSrc⟩ := hSource.address
  have hVisit' : visit = use/2 := by omega
  subst visit
  have hRow' : kvCopyRow tile (supplier%l.block) pair.val = key := by
    have hMod : (supplier%l.block)/8%8 = lane.val/8%8 := by
      have hEq := congrArg (fun n : Nat => n/8%8) hTid
      have hRed : (supplier%l.block%64)/8%8 = (supplier%l.block)/8%8 := by omega
      rw [hRed] at hEq
      exact hEq
    change kvCopyRow tile lane.val pair.val = key at hRow
    unfold kvCopyRow at hRow ⊢
    omega
  change kvCopyRow (Mma.trips p batch (assignedCoordinates p batch (supplier/l.block)).1-1-use/2)
    (supplier%l.block) pair.val < p.kLength batch at hValid
  rw [hOwner] at hValid hSrc
  change kvCopyRow tile (supplier%l.block) pair.val < p.kLength batch at hValid
  change spec.src.loc = p.kLayout.loc (p.page batch (kvCopyRow tile (supplier%l.block) pair.val/16))
    (co.2/6) (kvCopyRow tile (supplier%l.block) pair.val%16)
    (kvCopyColumn (supplier%l.block) upper) at hSrc
  rw [hRow'] at hValid hSrc
  have hColumn : kvCopyColumn (supplier%l.block) upper+off/2 = 16*step.val+k := by
    have hMod := congrArg (fun n : Nat => n%8) hTid
    rw [Nat.mod_mod_of_dvd _ (by decide : 8 ∣ 64)] at hMod
    unfold kvCopyColumn at hDim ⊢
    exact hMod.symm ▸ hDim
  have hCopy := ((group.member j spec).mp hMember).2.2
  have hShape := actualCopyShape hX hCopy
  have hWritten := ((Execution.memWrites_write_copy_of_whole hCopy hShape.whole).mp hWrite).2
  have hWidth : off < spec.dst.size := by rw [hShape.widthEq]; exact hOff
  obtain ⟨_,hValues⟩ := Protocol.cacheCopySourceBytes hp hX hFrame hCopy hWritten
  obtain ⟨hMem,hZero⟩ := hValues off hWidth
  refine ⟨(supplier,index'),group,j,spec,bs,loc,hPub',hPhase,hMember,hValid,hAt,hWrite,hCover,
    hOrder,?_⟩
  change spec.dst.loc.at off = loc at hLoc
  rw [← hLoc]
  simp only [wbyte,Loc.at,Nat.add_sub_cancel_left]
  by_cases hSize : off < spec.src.size
  · rw [ite_eq_left hSize]
    obtain ⟨b,hB,hVal⟩ := hMem hSize
    rw [hSrc,p.kLayout.loc_copy_byte,hColumn,hByte] at hB
    have hPage : p.page batch (key/16) < p.pages :=
      ((hp.pageTable batch hb).2 _ (by omega)).1
    have hHead := (assignedCoordinates_valid hp hLo hHi).2
    have hh : co.2/6 < p.kvHeads := by unfold Params.heads at hHead; unfold co; omega
    have hDim' : 16*step.val+k < 128 := by have := step.isLt; omega
    have hExpected := (hp.kvBytes (p.page batch (key/16)) hPage (co.2/6) hh
      (key%16) (Nat.mod_lt key (by decide)) (16*step.val+k) hDim').1
      byte (by simp [Value.bytes,FloatFmt.bytes]; omega)
    rw [hExpected] at hB
    injection hB with hEq
    injection hEq with hEq
    exact hEq ▸ hVal
  · rw [ite_eq_right hSize]
    exact hZero (Nat.le_of_not_gt hSize)

end
end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
