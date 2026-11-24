-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxTmemCells
public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstPublication
public import Kernels.TmlFa4Fwd.Proof.MmaQkInputLayout
import Lemmas.Tcgen05.TcMmaRead

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.TcMma

private theorem packedProbabilityByte (weights : Nat → ℝ) (step : Fin 8)
    {k byte : Nat} (hb : byte < 2) :
    let index := 2*k+byte
    let offset := 8 * (step.val % 2) + index / 4
    let q := pvQuarter step
    (probabilityWord (fun i => weights (32*q.val+i)) offset).byteAt (index % 4) =
      (Value.float .bf16 (weights (16*step.val+k))).byteAt byte := by
  dsimp only
  have hParity := Nat.mod_lt k (by decide : 0 < 2)
  have hBase : 32 * (pvQuarter step).val + 16 * (step.val % 2) = 16 * step.val := by
    change 32*(step.val/2) + 16*(step.val%2) = 16*step.val
    omega
  have hWord : (2*k+byte)/4 = k/2 := by omega
  have hByte : (2*k+byte)%4 = 2*(k%2)+byte := by omega
  rw [hWord,hByte]
  unfold probabilityWord
  change (if 2*(k%2)+byte < 2 then
      (Value.float .bf16 (weights (32*(pvQuarter step).val +
        2*(8*(step.val%2)+k/2)))).byteAt (2*(k%2)+byte)
    else (Value.float .bf16 (weights (32*(pvQuarter step).val +
        (2*(8*(step.val%2)+k/2)+1)))).byteAt (2*(k%2)+byte-2)) = _
  by_cases hEven : k%2 = 0
  · rw [ite_eq_left (by omega)]
    have hKey : 32*(pvQuarter step).val + 2*(8*(step.val%2)+k/2) = 16*step.val+k := by
      omega
    have hAt : 2*(k%2)+byte = byte := by omega
    rw [hKey,hAt]
  · rw [ite_eq_right (by omega)]
    have hKey :
        32*(pvQuarter step).val + (2*(8*(step.val%2)+k/2)+1) = 16*step.val+k := by
      omega
    have hAt : 2*(k%2)+byte-2 = byte := by omega
    rw [hKey,hAt]

/-- A packed probability store supplies the exact BF16 A byte selected by a PV fragment
when the corresponding tensor cell observes that store. -/
theorem probabilityOperandByteOfStore {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g : Nat} (stage : Fin 2) (step : Fin 8) (weights : Nat → ℝ)
    {k byte : Nat} (hk : k < 16) (hb : byte < 2)
    {i source : EvId} {d : Nat} {op : OperandSpec} {acc : Bool} {mask : List Nat}
    (hIssue : X.MmaIssue i d op acc mask) (hDesc : op.descriptor = pvDescriptor)
    (hCta : op.lowCta = g / l.block)
    (hAddr : op.aTmem = some (probabilityColumn stage + 8 * step.val))
    (hOwner : source.1 = g)
    (hStore : X.TSt source (probabilityAddress l g stage (pvQuarter step))
      ((List.range 16).map (probabilityWord (fun i => weights (32*(pvQuarter step).val+i))))
      .s32x32b)
    {operands : AsyncCopy.MmaOperands} (hOperands : X.async.mmaOperands i = some operands)
    (hSource : ReadSource l X .a source i (tcDataCell l g .s32x32b
      (probabilityAddress l g stage (pvQuarter step)) (8 * (step.val % 2) + (2*k+byte)/4))) :
    operands.a[Mma.qkByteIndex (tmemRow l g).val k byte]? =
      some (some ((Value.float .bf16 (weights (16*step.val+k))).byteAt byte)) := by
  let index : Fin 32 := ⟨2*k+byte,by omega⟩
  let offset := 8*(step.val%2) + index.val/4
  let values := probabilityWord (fun i => weights (32*(pvQuarter step).val+i))
  have hOffset : offset < 16 := by
    have := Nat.mod_lt step.val (by decide : 0 < 2)
    dsimp [offset,index]
    omega
  have hCell := pvFromProbability hDesc hCta stage step index hAddr
  have hValue : StoreValue l X source (tcDataCell l g .s32x32b
      (probabilityAddress l g stage (pvQuarter step)) offset) (values offset) := by
    refine ⟨_,_,_,offset,hStore,?_,by rw [hOwner]⟩
    simp [hOffset,values]
  have hBytes : (values offset).bytes = 4 := rfl
  have hLen : index.val % 4 < (values offset).bytes :=
    hBytes.symm ▸ Nat.mod_lt _ (by decide)
  have hIndex : Mma.qkByteIndex (tmemRow l g).val k byte = 32*(tmemRow l g).val+index.val :=
    by simp [Mma.qkByteIndex,index,Nat.add_assoc]
  have hCell := hIndex.symm ▸ hCell
  have h := hX.tcRead.2 i (Mma.qkByteIndex (tmemRow l g).val k byte) _ _ source _ operands
    ⟨d,op,acc,mask,hIssue,hCell⟩ hSource (.inr (.inl hValue)) hOperands hLen
  change operands.a[Mma.qkByteIndex (tmemRow l g).val k byte]? =
    some (some ((values offset).byteAt ((2*k+byte)%4))) at h
  rw [packedProbabilityByte weights step hb] at h
  exact h

end PTX.Kernels.TmlFa4Fwd.Softmax
