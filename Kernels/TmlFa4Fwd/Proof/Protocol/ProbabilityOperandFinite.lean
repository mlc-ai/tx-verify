-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Safety.MmaOperandCoverage
public import Kernels.TmlFa4Fwd.Proof.Protocol.ProbabilitySourceOrder
import Kernels.TmlFa4Fwd.Proof.SoftmaxTmemCells
import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueFrame
import Kernels.TmlFa4Fwd.Proof.MmaOperandValues

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Scores
open PTX PTX.TcMma PTX.AsyncCopy Thread Softmax
open Mma (pvSite qkByteIndex idealBf16Element_of_bytes)

/-- The cell of a recorded packed vector contains its two probability reals. -/
theorem probabilityStoreWordOfPackedVector {l : Launch} {X : Execution} {store : EvId}
    {address : Nat} {shape : TcShape} {weights : Nat → ℝ} {cell : Cell}
    (hStore : X.TSt store address ((List.range 16).map (probabilityWord weights)) shape)
    (hCell : StoreCell l X store cell) :
    ∃ lo hi : ℝ, StoreValue l X store cell (.pair (.float .bf16 lo) (.float .bf16 hi)) := by
  obtain ⟨address', values, shape', j, ⟨site', he'⟩, hj, hLoc⟩ := hCell
  obtain ⟨site, he⟩ := hStore
  have hKind := congrArg Event.kind (Option.some.inj (he.symm.trans he'))
  obtain ⟨rfl, rfl, rfl⟩ := TcKind.st.inj (Kind.tc.inj hKind).symm
  have hj' : j < 16 := by simpa using hj
  refine ⟨weights (2 * j), weights (2 * j + 1), address', _, shape', j, ⟨site, he⟩, ?_, hLoc⟩
  simp [List.getElem?_range hj', probabilityWord]

/-- Both bytes of a completed PV input are directed to one physical probability cell. -/
theorem pvProbabilityCell {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j d row col k : Nat} {result : Cell} {block : Fin 4} {step : Fin 8}
    {op : OperandSpec} {acc : Bool} {mask : List Nat}
    (hPv : PvInstruction X (g,j) block step d op acc mask)
    (hWrite : writeCell op d mask row col = some result) (hk : k < 16) :
    ∃ cell, ∀ b : Fin 2, aCell op (qkByteIndex row k b.val) = some (cell,2*(k%2)+b.val) := by
  let stage := (pvSite block).stage
  let producer := probabilityProducer l (g/l.block) stage row
  obtain ⟨_,_,hDesc,hOwner,_⟩ := hPv.valueOperand hp hX
  have hr := (resultCell_rowcol (writeCell_resultCell hWrite)).1
  rw [hDesc] at hr
  change row < 128 at hr
  have hCta : producer/l.block = g/l.block := by
    unfold producer probabilityProducer
    rw [hp.block]
    have := stage.isLt
    omega
  have hRow : (tmemRow l producer).val = row := by
    change laneBase l producer + laneOf l producer = row
    unfold producer probabilityProducer laneBase laneOf
    rw [hp.block]
    have := stage.isLt
    omega
  let cell := tcDataCell l producer .s32x32b
    (probabilityAddress l producer stage (pvQuarter step)) (8*(step.val%2)+k/2)
  have hAddress := hPv.probabilityAddress hp hX
  have hCell (b : Fin 2) :
      aCell op (qkByteIndex row k b.val) = some (cell,2*(k%2)+b.val) := by
    let offset : Fin 32 := ⟨2*k+b.val,by have := b.isLt; omega⟩
    have hIndex : 32*(tmemRow l producer).val+offset.val = qkByteIndex row k b.val := by
      simp only [hRow,qkByteIndex,offset,Nat.add_assoc]
    have hWord : offset.val/4 = k/2 := by have := b.isLt; dsimp [offset]; omega
    have hByte : offset.val%4 = 2*(k%2)+b.val := by have := b.isLt; dsimp [offset]; omega
    have hLoc := pvFromProbability hDesc (hOwner.trans hCta.symm) stage step offset hAddress
    rw [hIndex,hWord,hByte] at hLoc
    exact hLoc
  exact ⟨cell,hCell⟩

/-- The two bytes selected from an actual completed packed store give the real
BF16 value read at this PV operand position. -/
theorem pvProbabilityElementOfStoreWord {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X)
    {i : EvId} {d row k : Nat} {cell : Cell}
    {op : OperandSpec} {acc : Bool} {mask : List Nat} {ops : MmaOperands}
    (hIssue : X.MmaIssue i d op acc mask)
    (hCell : ∀ b : Fin 2, aCell op (qkByteIndex row k b.val) = some (cell,2*(k%2)+b.val))
    (hOps : X.async.mmaOperands i = some ops) (seen : ProbabilityCellPublication l X i cell)
    {lo hi : ℝ}
    (hWord : StoreValue l X seen.store cell (.pair (.float .bf16 lo) (.float .bf16 hi))) :
    ∃ x, Assumption.idealMmaElement (.f16 .bf16 .f32) .a ops.a row k = .ok x := by
  have hRead : X.MmaACell i cell := ⟨_,_,_,_,_,_,hIssue,hCell 0⟩
  have hStable := seen.readSource hp hX hCuQ hRead
  let word := Value.pair (.float .bf16 lo) (.float .bf16 hi)
  let value := if k%2 = 0 then lo else hi
  have hBytes (b : Fin 2) :
      ops.a[qkByteIndex row k b.val]? = some (some ((Value.float .bf16 value).byteAt b.val)) := by
    have hb := b.isLt
    have hWithin : 2*(k%2)+b.val < word.bytes := by
      change 2*(k%2)+b.val < 4
      omega
    have hValue := hX.tcRead.2 i (qkByteIndex row k b.val) cell
      (2*(k%2)+b.val) seen.store word ops
      ⟨d,op,acc,mask,hIssue,hCell b⟩ hStable (.inr (.inl hWord)) hOps hWithin
    change ops.a[qkByteIndex row k b.val]? = some (some (word.byteAt (2*(k%2)+b.val))) at hValue
    rw [hValue]
    change some (some (if 2*(k%2)+b.val < 2 then
      (Value.float .bf16 lo).byteAt (2*(k%2)+b.val)
      else (Value.float .bf16 hi).byteAt (2*(k%2)+b.val-2))) = _
    by_cases hLow : k%2 = 0
    · simp [hLow,hb,value]
    · have hHigh : k%2 = 1 := by omega
      rw [hHigh, ite_eq_right (show ¬ 2*1+b.val < 2 by omega)]
      simp [hHigh,value,show 2+b.val-2 = b.val by omega]
  exact ⟨value,idealBf16Element_of_bytes (hBytes 0) (hBytes 1)⟩

end PTX.Kernels.TmlFa4Fwd.Protocol.Scores
