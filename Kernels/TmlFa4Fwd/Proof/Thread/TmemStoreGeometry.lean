-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.TmemCellBounds
public import Core.Tc.TcMmaOrder
import Kernels.TmlFa4Fwd.Proof.Thread.BiasReadAddress
import Kernels.TmlFa4Fwd.Proof.Thread.TensorStoreSites
import Kernels.TmlFa4Fwd.Proof.TmemGeometry
import Lemmas.Order.OrderBaseCausality

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.TcMma
open Prologue (warpIndex)

/-- A probability half-tile or a full output tile written by an ordinary Tensor Memory store. -/
inductive TensorStoreTile where
  | probability (stage : Fin 2)
  | rescale (stage : Fin 2)
  deriving DecidableEq

/-- The physical column interval of the store's tile. -/
def TensorStoreTile.columns : TensorStoreTile → Nat × Nat
  | .probability stage => (probabilityColumn stage, probabilityColumn stage+64)
  | .rescale stage => (outputColumn stage, outputColumn stage+128)

/-- The four-warp cohort that issues stores into this tile. -/
def TensorStoreTile.warpGroup : TensorStoreTile → Nat
  | .probability stage => stage.val
  | .rescale _ => 2

/-- The actual store's issuing thread, physical tile and lane geometry. -/
structure TensorStoreFootprint (l : Launch) (i : EvId) (cell : Cell)
    (tile : TensorStoreTile) : Prop where
  cta : cell.cta = i.1/l.block
  lane : cell.lane = Correction.rowOf l i.1
  columnLo : tile.columns.1 ≤ cell.column
  columnHi : cell.column < tile.columns.2
  warpGroup : (i.1 % l.block)/128 = tile.warpGroup

private theorem storeRow (l : Launch) (g : Nat) :
    laneBase l g + laneOf l g = Correction.rowOf l g := by
  unfold laneBase laneOf Correction.rowOf
  omega

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- Each observed rescale store belongs to the correction warp group. -/
theorem correctionStoreWarpGroup (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} (stage : Fin 2) (chunk : Fin 8) {address : Nat} {vals : List Value} {shape : TcShape}
    (he : X.get i = some ⟨Correction.rescaleStorePc stage chunk,.tc (.st address vals shape)⟩) :
    (i.1 % l.block)/128 = 2 := by
  let site := Correction.rescaleStorePc stage chunk
  have hs : 8006 ≤ site ∧ site < 9057 ∧ site ∉ registerHintSites := by
    fin_cases stage <;> fin_cases chunk <;> decide
  have hRole := roleBodyPcOfEvent hp hX he (by change 173 < site; omega) hs.2.2
  change roleBodyPc (warpIndex l i.1) site at hRole
  unfold roleBodyPc at hRole
  have hWarp : 8 ≤ warpIndex l i.1 ∧ warpIndex l i.1 < 12 := by
    rcases hRole with hExit | hBody
    · change site = 9205 at hExit
      omega
    · change (if 14 ≤ warpIndex l i.1 then _ else _) at hBody
      split_ifs at hBody <;> omega
  unfold warpIndex at hWarp
  omega

/-- Every actual store cell lies in the tile and row of its physical issuer. -/
theorem tensorStoreFootprint (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {cell : Cell} (h : StoreCell l X i cell) :
    ∃ tile, TensorStoreFootprint l i cell tile := by
  obtain ⟨address,vals,shape,j,⟨site,he⟩,hj,rfl⟩ := h
  rcases tensorStoreSite hX he with ⟨round,q,rfl⟩ | ⟨stage,chunk,rfl⟩
  · obtain ⟨w,hWarp,rfl,hLength,rfl⟩ := Scores.probabilityStoreAddress hp hX round q he
    let stage := Softmax.stageOf w
    have hStage := probabilityColumn_range stage
    have hLimit := scoreColumn_range stage
    have hQ := q.isLt
    rw [hLength] at hj
    change ∃ tile, TensorStoreFootprint l i
      (tcDataCell l i.1 .s32x32b (2^16*laneBase l i.1+(probabilityColumn stage+16*q.val)) j) tile
    have hCol : probabilityColumn stage+16*q.val < 512 := by omega
    rw [tcDataCell_warp32 l i.1 j hCol]
    refine ⟨.probability stage,rfl,storeRow l i.1,?_,?_,?_⟩
    · change probabilityColumn stage ≤ probabilityColumn stage+16*q.val+j
      omega
    · change (probabilityColumn stage+16*q.val)+j < probabilityColumn stage+64
      omega
    · change (i.1%l.block)/128 = w.val / 4
      rw [hWarp]
      unfold warpIndex
      omega
  · have hWarp := correctionStoreWarpGroup hp hX stage chunk he
    obtain ⟨rfl,rfl,hLength⟩ := Correction.rescaleStoreActualAddress hp hX stage chunk he
    have hStage := outputColumn_range stage
    have hChunk := chunk.isLt
    rw [hLength] at hj
    change ∃ tile, TensorStoreFootprint l i
      (tcDataCell l i.1 .s32x32b (2^16*laneBase l i.1+(outputColumn stage+16*chunk.val)) j) tile
    have hCol : outputColumn stage+16*chunk.val < 512 := by omega
    rw [tcDataCell_warp32 l i.1 j hCol]
    refine ⟨.rescale stage,rfl,storeRow l i.1,?_,?_,hWarp⟩
    · change outputColumn stage ≤ outputColumn stage+16*chunk.val+j
      omega
    · change (outputColumn stage+16*chunk.val)+j < outputColumn stage+128
      omega

private theorem storeTilesDisjoint {a b : TensorStoreTile} {col : Nat}
    (ha : a.columns.1 ≤ col ∧ col < a.columns.2)
    (hb : b.columns.1 ≤ col ∧ col < b.columns.2) : a = b := by
  cases a <;> cases b
  all_goals
    simp only [TensorStoreTile.columns,probabilityColumn,scoreColumn,outputColumn] at ha hb
  case probability.probability a b =>
    congr
    apply Fin.ext
    omega
  case rescale.rescale a b =>
    congr
    apply Fin.ext
    omega
  case probability.rescale a b =>
    have hA := a.isLt
    omega
  case rescale.probability a b =>
    have hB := b.isLt
    omega

/-- Two stores covering the same cell belong to exactly one physical lane. -/
theorem sameTensorStoreLane (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i j : EvId} {cell : Cell} (hi : StoreCell l X i cell) (hj : StoreCell l X j cell) :
    i.1 = j.1 := by
  obtain ⟨tile,hi⟩ := tensorStoreFootprint hp hX hi
  obtain ⟨tile',hj⟩ := tensorStoreFootprint hp hX hj
  obtain rfl := storeTilesDisjoint ⟨hi.columnLo,hi.columnHi⟩ ⟨hj.columnLo,hj.columnHi⟩
  have hCta := hi.cta.symm.trans hj.cta
  have hRow := hi.lane.symm.trans hj.lane
  have hGroup := hi.warpGroup.trans hj.warpGroup.symm
  unfold Correction.rowOf at hRow
  have hRem : i.1 % l.block = j.1 % l.block := by omega
  calc
    i.1 = i.1 % l.block + l.block*(i.1/l.block) := (Nat.mod_add_div _ _).symm
    _ = j.1 % l.block + l.block*(j.1/l.block) := by rw [hRem,hCta]
    _ = j.1 := Nat.mod_add_div _ _

/-- Overlapping ordinary stores are issued by one thread and use the store pipeline. -/
theorem tensorStoreWritesOrdered (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i j : EvId} {cell : Cell} (hi : StoreCell l X i cell) (hj : StoreCell l X j cell) :
    i = j ∨ WriteBefore l X i j ∨ WriteBefore l X j i := by
  have hLane := sameTensorStoreLane hp hX hi hj
  obtain ⟨a,v,s,_,⟨pi,hi⟩,_,_⟩ := hi
  obtain ⟨b,w,t,_,⟨pj,hj⟩,_,_⟩ := hj
  rcases lt_trichotomy i.2 j.2 with hLt | hEq | hGt
  · have hPo := po_of_not_access hLane hLt (len_of_get hj) (by rw [hj]; rfl)
    have hw : SameWarp l i.1 j.1 :=
      ⟨⟨event_thread_lt hX hi,event_thread_lt hX hj,congrArg (·/l.block) hLane⟩,
        by rw [hLane]⟩
    have hPipe : Pipelined l X .stWrite i .stWrite j :=
      ⟨hw,.inl (.single (.inl hPo)),⟨a,v,s,pi,hi⟩,b,w,t,pj,hj⟩
    exact .inr (.inl (.inr (.inl ⟨⟨a,v,s,pi,hi⟩,.inr (.inr hPipe)⟩)))
  · exact .inl (Prod.ext hLane hEq)
  · have hPo := po_of_not_access hLane.symm hGt (len_of_get hi) (by rw [hi]; rfl)
    have hw : SameWarp l j.1 i.1 :=
      ⟨⟨event_thread_lt hX hj,event_thread_lt hX hi,congrArg (·/l.block) hLane.symm⟩,
        by rw [hLane]⟩
    have hPipe : Pipelined l X .stWrite j .stWrite i :=
      ⟨hw,.inl (.single (.inl hPo)),⟨b,w,t,pj,hj⟩,a,v,s,pi,hi⟩
    exact .inr (.inr (.inr (.inl ⟨⟨b,w,t,pj,hj⟩,.inr (.inr hPipe)⟩)))

end PTX.Kernels.TmlFa4Fwd.Thread
