-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.TmemProbabilityReadGeometry
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaTerminalProbabilityAcquire

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.TcMma
open PTX.Kernels.TmlFa4Fwd.Mma

/-- An actual PV site uses its stage's early acquire and also the tail acquire
when the fragment covers the last quarter. -/
theorem PvInstruction.probabilityAcquire {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {b : Fin 4} {frag : Fin 8} {d : Nat}
    {op : OperandSpec} {acc : Bool} {mask : List Nat}
    (hi : PvInstruction X i b frag d op acc mask) (packet : Fin 2)
    (hPacket : packet.val = 0 ∨ 6 ≤ frag.val) :
    ∃ wait, MmaProbabilityAcquire l X i (pvSite b).stage packet wait := by
  have hBlock : ∃ steady : Bool, b = firstPvBlock steady (pvSite b).stage := by
    fin_cases b <;> first | exact ⟨true,rfl⟩ | exact ⟨false,rfl⟩
  let stage := (pvSite b).stage
  change ∃ wait, MmaProbabilityAcquire l X i stage packet wait
  change ∃ steady, b = firstPvBlock steady stage at hBlock
  obtain ⟨steady,hSite⟩ := hBlock
  have hPv : PvInstruction X i (firstPvBlock steady stage) frag d op acc mask := hSite ▸ hi
  cases steady
  · exact hPv.tailPacketProbabilityAcquire hp hX stage packet hPacket
  · exact hPv.steadyProbabilityAcquire hp hX stage packet hPacket

/-- A PV A read in a probability cell has the returning guard of the packet
covering that cell. The read and store belong to the same CTA. -/
theorem probabilityAReadGuardOfStore {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage packet : Fin 2) {reader store : EvId} {cell : Cell}
    (hRead : MmaAOnProbabilityStage X reader cell stage)
    (hStore : StoreCell l X store cell)
    (hFoot : TensorStoreFootprint l store cell (.probability stage))
    (hPacket : packet.val = 0 ∨ probabilityColumn stage+48 ≤ cell.column) :
    ∃ d op acc mask wait, X.MmaIssue reader d op acc mask ∧
      SameCta l reader.1 store.1 ∧ MmaProbabilityAcquire l X reader stage packet wait := by
  obtain ⟨b,frag,d,op,acc,mask,index,byte,hStage,hPv,hCell⟩ := hRead
  let hMma : X.MmaIssue reader d op acc mask := ⟨_,hPv.decoded⟩
  let hA : X.MmaACell reader cell := ⟨d,op,acc,mask,index,byte,hMma,hCell⟩
  have hOwner := mmaAOperandCta hp hX hA
  obtain ⟨_,_,_,_,⟨_,he⟩,_,_⟩ := hStore
  have hSame : SameCta l reader.1 store.1 :=
    ⟨event_thread_lt hX hPv.decoded,event_thread_lt hX he,hOwner.symm.trans hFoot.cta⟩
  have hAddress := hPv.probabilityAddress hp hX
  rw [hStage] at hAddress
  have hRange := (probabilityReadColumn hMma stage frag hAddress hA).2
  have hFrag : packet.val = 0 ∨ 6 ≤ frag.val :=
    hPacket.imp_right (fun h => by omega)
  obtain ⟨wait,hAcquire⟩ := hPv.probabilityAcquire hp hX packet hFrag
  exact ⟨d,op,acc,mask,wait,hMma,hSame,hStage ▸ hAcquire⟩

end PTX.Kernels.TmlFa4Fwd.Thread
