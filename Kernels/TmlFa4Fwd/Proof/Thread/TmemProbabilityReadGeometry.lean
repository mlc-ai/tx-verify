-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.TmemConflictGeometry
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyProbabilityColumn
import Kernels.TmlFa4Fwd.Proof.TmemGeometry
import Kernels.TmlFa4Fwd.Proof.Thread.MmaQueryBank
import Lemmas.Tcgen05.TcMmaACell

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.TcMma
open PTX.Kernels.TmlFa4Fwd.Mma

/-- A PV A fragment with its observed tile address reads eight consecutive probability words. -/
theorem probabilityReadColumn {X : Execution} {i : EvId} {d : Nat} {op : OperandSpec}
    {accum : Bool} {mask : List Nat} (hi : X.MmaIssue i d op accum mask)
    (stage : Fin 2) (frag : Fin 8)
    (hA : op.aTmem = some (probabilityColumn stage+8*frag.val))
    {cell : Cell} (hRead : X.MmaACell i cell) :
    probabilityColumn stage+8*frag.val ≤ cell.column ∧
      cell.column < probabilityColumn stage+8*frag.val+8 := by
  obtain ⟨d',op',acc',mask',index,byte,⟨site,he⟩,hCell⟩ := hRead
  obtain ⟨_,hi⟩ := hi
  have hKind := congrArg Event.kind (Option.some.inj (hi.symm.trans he))
  obtain ⟨rfl,rfl,rfl,rfl⟩ := TcKind.mma.inj (Kind.tc.inj hKind)
  have hRange := probabilityColumn_range stage
  have hScore := scoreColumn_range stage
  have hFrag := frag.isLt
  have hAddr : probabilityColumn stage+8*frag.val < 65536 := by omega
  unfold aCell at hCell
  simp only [hA,Option.bind_some,row_bytes] at hCell
  split at hCell
  · obtain ⟨rfl,_⟩ := Prod.mk.inj (Option.some.inj hCell)
    dsimp only
    omega
  · cases hCell

/-- The actual PV A cell of a physical probability tile. -/
def MmaAOnProbabilityStage (X : Execution) (reader : EvId) (cell : Cell) (stage : Fin 2) : Prop :=
  ∃ block frag d op acc mask index byte, (pvSite block).stage = stage ∧
    PvInstruction X reader block frag d op acc mask ∧ aCell op index = some (cell,byte)

/-- Every actual Tensor Memory A read is from its stage's probability half-tile. -/
theorem mmaAProbabilityTile {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {reader : EvId} {cell : Cell} (hr : X.MmaACell reader cell) :
    ∃ stage, MmaAOnProbabilityStage X reader cell stage ∧
      probabilityColumn stage ≤ cell.column ∧ cell.column < probabilityColumn stage+64 := by
  obtain ⟨d,op,acc,mask,index,byte,hMma,hCell⟩ := hr
  rcases actualMmaInstruction hX hMma with ⟨block,frag,hQk⟩ | ⟨block,frag,hPv⟩
  · have hShared := (hQk.queryOperand hp hX).shared
    simp [aCell,hShared] at hCell
  · let stage := (pvSite block).stage
    have hAddr := hPv.probabilityAddress hp hX
    have h := probabilityReadColumn hMma stage frag hAddr ⟨_,_,_,_,_,_,hMma,hCell⟩
    have hFrag := frag.isLt
    exact ⟨stage,⟨block,frag,d,op,acc,mask,index,byte,rfl,hPv,hCell⟩,by omega,by omega⟩

end PTX.Kernels.TmlFa4Fwd.Thread
