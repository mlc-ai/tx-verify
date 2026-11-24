-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.InitialCacheOperandValues
public import Kernels.TmlFa4Fwd.Proof.Protocol.RecurringValueLaunchValue

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.Proof PTX.AsyncCopy PTX.TcMma Thread
open PTX.Kernels.TmlFa4Fwd.Mma (pvValue pvKeyRow trips qkByteIndex)
open Epilogue (assignedCoordinates)

/-- Both bytes of an observed PV element come from its actual ready visit's
launch V value, with zero fill at the masked edge of the first visit. -/
theorem valueOperandElementOfLaunch {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {g index d batch : Nat} {block : Fin 4} {step : Fin 8}
    {op : OperandSpec} {accum : Bool} {mask : List Nat}
    (hValue : PvInstruction X (g,index) block step d op accum mask)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads)
    {row k : Nat} (hr : row < 128) (hk : k < 16)
    {ops : MmaOperands} (hOps : X.async.mmaOperands (g,index) = some ops) :
    ∃ use, Thread.Mma.LatestValueReadyUse l X g index use ∧
      let co := assignedCoordinates p batch (g/l.block)
      let key := 128*(trips p batch co.1-1-use/2)+pvKeyRow step k
      Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b row k =
        .ok (if key < p.kLength batch then pvValue p batch co.2 key row else 0) := by
  obtain ⟨use,_,hUse,_,_,_⟩ := valueOperandReadyInPrefix hp hX hValue
  let co := assignedCoordinates p batch (g/l.block)
  let key := 128*(trips p batch co.1-1-use/2)+pvKeyRow step k
  have hPositive : 1 ≤ use := by obtain ⟨_,_,_,hOdd,_,_⟩ := hUse; omega
  refine ⟨use,hUse,?_⟩
  change Assumption.idealMmaElement (.f16 .bf16 .f32) .b ops.b row k =
    .ok (if key < p.kLength batch then pvValue p batch co.2 key row else 0)
  have hMma : X.MmaIssue (g,index) d op accum mask := ⟨_,hValue.decoded⟩
  rcases Nat.eq_or_lt_of_le hPositive with hFirst | hRepeat
  · subst use
    let steady := decide (block.val < 2)
    let stage : Fin 2 := ⟨block.val%2,Nat.mod_lt _ (by decide)⟩
    have hBlock : block = firstPvBlock steady stage := by fin_cases block <;> rfl
    have hPv := hBlock ▸ hValue
    have hSeen (b : Fin 2) : ops.b[qkByteIndex row k b.val]? = some (some
        (if key < p.kLength batch then
          (Value.float .bf16 (pvValue p batch co.2 key row)).byteAt b.val else zeroByte)) := by
      obtain ⟨loc,hLoc,hByte⟩ := initialValueOperandByteInPrefix hp hX hFrame hb hLo hHi
        steady stage step hr hk b.isLt hPv hUse
      have hKey : key = 128*(trips p batch co.1-1)+pvKeyRow step k := by
        dsimp only [key]; omega
      rw [hKey]
      exact Mma.operandByte_observed hX hMma hOps (isB := true) hLoc hByte
    by_cases hIn : key < p.kLength batch
    · rw [ite_eq_left hIn]
      exact Mma.idealBf16Element_of_bytes
        (by simpa only [hIn,↓reduceIte,Fin.val_zero] using hSeen 0)
        (by simpa only [hIn,↓reduceIte,Fin.val_one] using hSeen 1)
    · rw [ite_eq_right hIn]
      exact Mma.idealBf16Element_of_zeroBytes
        (by simpa only [hIn,↓reduceIte,Fin.val_zero] using hSeen 0)
        (by simpa only [hIn,↓reduceIte,Fin.val_one] using hSeen 1)
  · have hSeen (b : Fin 2) : key < p.kLength batch ∧
        ops.b[qkByteIndex row k b.val]? = some
          (some ((Value.float .bf16 (pvValue p batch co.2 key row)).byteAt b.val)) := by
      obtain ⟨hIn,loc,hLoc,hByte⟩ :=
        recurringValueOperandByteInPrefix hp hX hFrame hValue hUse hRepeat hb hLo hHi
          hr hk b.isLt
      exact ⟨hIn,Mma.operandByte_observed hX hMma hOps (isB := true) hLoc hByte⟩
    rw [ite_eq_left (hSeen 0).1]
    exact Mma.idealBf16Element_of_bytes (hSeen 0).2 (hSeen 1).2

end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
