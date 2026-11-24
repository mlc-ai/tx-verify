-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.RecurringKeyOperandValues
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPublishedKeyCopySize

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.AsyncCopy PTX.TcMma PTX.Flow PTX.Proof Thread Thread.Loader
open Mma (qkByteIndex qkLoaderByte qkLoaderCoordinates recurringKeyBlock)
open Loader (kvUseStage kvUseStage_val)
open Epilogue (assignedCoordinates)

noncomputable section

/-- The actual copy serving a recurring QK read writes its expected launch byte. -/
theorem recurringKeyOperandLaunchByte {p : Params} {l : Launch} {m : Mem0} {X : Execution}
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
      wbyte spec.dst bs loc = some expected := by
  dsimp only
  obtain ⟨pub,group,j,spec,bs,loc,hPub,hPhase,hMember,hValid,hLoc,hWrite,hCovers,hOrder,hValue⟩ :=
    recurringKeyOperandCopyValue hp hX hFrame stage hIssue hb hLo hHi hr hk hbByte
  obtain ⟨_,hEven,hUse⟩ := hIssue.recurringKeyOperandOfPositiveEvenReadyUse hp hX stage
  let a := Thread.Mma.atPrefix l X g index
  let use := a.kvAcquires 0+a.kvAcquires 1+a.kvAcquires 2-1
  change use%2 = 0 at hEven
  change 2 ≤ use at hUse
  change X.AsyncArrive pub (readyObject l g (kvUseStage use)) true at hPub
  change generation l X pub (kvUseStage use) = use/3 at hPhase
  obtain ⟨issuer,i⟩ := pub
  have hSlot := group.slotFor hp hX hPub
  have hPlane := publicationPlaneOfGeneration hp hX hPub group.published
  have hKey : group.publication.packet.plane = .key := by
    dsimp only at hPlane
    rw [hSlot] at hPlane
    change group.publication.packet.plane =
      (if (3*generation l X (issuer,i) (kvUseStage use)+(kvUseStage use).val)%2 = 0 then
        .key else .value) at hPlane
    rw [hPhase,kvUseStage_val,show 3*(use/3)+use%3 = use by omega,hEven] at hPlane
    exact hPlane
  have hFull := group.recurringKeyMemberFullSize hp hX hFrame hPub hPhase hUse hKey hMember
  obtain ⟨_,_,_,hOff⟩ := qkLoaderCoordinates step 0 (row := row) hk hbByte
  rw [hFull,ite_eq_left hOff] at hValue
  exact ⟨(issuer,i),group,j,spec,bs,loc,hPub,hPhase,hMember,hValid,hLoc,hWrite,
    hCovers,hOrder,hValue⟩

end
end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
