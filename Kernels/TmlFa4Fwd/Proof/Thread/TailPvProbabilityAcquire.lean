-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSharedFootprint
public import Kernels.TmlFa4Fwd.Proof.Thread.InitialValueOperands
public import Kernels.TmlFa4Fwd.Proof.Thread.ProbabilityCredits
import Kernels.TmlFa4Fwd.Proof.MmaReadyRelease
import Kernels.TmlFa4Fwd.Proof.MmaMbarAddress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.AsyncCopy
open _root_.PTX.Kernels.TmlFa4Fwd.Mma
open Scores (probabilityObject)

/-- A returning probability acquire for one tail PV fragment. -/
structure TailPvProbabilityAcquire (l : Launch) (X : Execution) (i : EvId)
    (stage packet : Fin 2) (wait : Nat) : Prop where
  event : ∃ e parity, X.get (i.1,wait) = some e ∧
    e.kind = .wait (probabilityObject l (i.1/l.block) stage packet) parity true true .cta
  resume : Resumes kernel X (i.1,wait) i

/-- Every tail PV fragment uses the early packet, and its last two fragments
also require the successful tail-packet acquire. -/
theorem PvInstruction.tailProbabilityAcquire {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage packet : Fin 2) {i : EvId} {frag : Fin 8} {d : Nat}
    {op : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (he : PvInstruction X i (firstPvBlock false stage) frag d op acc mask)
    (hPacket : packet.val = 0 ∨ 6 ≤ frag.val) :
    ∃ wait, TailPvProbabilityAcquire l X i stage packet wait := by
  obtain ⟨g,j⟩ := i
  let select : Fin 4 := ⟨2 * stage.val + packet.val,by
    have := stage.isLt
    have := packet.isLt
    omega⟩
  have hBounds : probabilityPc select true + 3 ≤ pvPc (firstPvBlock false stage) frag ∧
      pvPc (firstPvBlock false stage) frag ≤ if select.val < 2 then 2594 else 2634 := by
    revert hPacket
    dsimp only [select]
    fin_cases stage <;> fin_cases packet <;> fin_cases frag <;> decide
  obtain ⟨wait,_,loc,parity,hWait,hResume⟩ :=
    tailProbabilityWaitBeforeGate hp hX select he.decoded hBounds.1 hBounds.2
  have hHead : probabilityPc select true ∈
      [2141,2145,2210,2297,2335,2419,2450,2548,2586,2595,2626] := by
    dsimp only [select]
    fin_cases stage <;> fin_cases packet <;> decide
  have hAddr := mmaFixedWaitAddress hp hX hWait hHead
  have hOffset : fixedMmaWaitOffset (probabilityPc select true) =
      96 + 8*stage.val + 16*packet.val := by
    dsimp only [select]
    fin_cases stage <;> fin_cases packet <;> decide
  rw [hOffset] at hAddr
  change loc = probabilityObject l (g/l.block) stage packet at hAddr
  subst loc
  exact ⟨wait,⟨_,parity,hWait,rfl⟩,hResume⟩

end PTX.Kernels.TmlFa4Fwd.Thread
