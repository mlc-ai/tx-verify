-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaProbabilityOperand
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaRecurringKeyFrame
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueFrame

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX

/-- Every actual or pending shared MMA operand byte lies in its CTA's allocated banks. -/
theorem mmaSharedByteRange {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {isB : Bool} {index : Nat} {loc : Loc}
    (h : X.MmaFootprint i isB index loc) : Mma.SharedOperandRange l i.1 loc := by
  cases isB
  · exact mmaSharedAByteRange hp hX h
  · obtain ⟨_,d,op,accum,mask,hIssue,hByte⟩ := mmaSharedFootprintIssue hX h
    rcases actualMmaInstruction hX hIssue with ⟨_,_,hQk⟩ | ⟨_,_,hPv⟩
    · exact hQk.keyByteRange hp hX hByte
    · exact hPv.valueByteRange hp hX hByte

/-- Shared A bytes are in the Q banks. Shared B bytes are in the paged K/V ring. -/
theorem mmaSharedOperandBand {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i : EvId} {isB : Bool} {index : Nat} {loc : Loc}
    (h : X.MmaFootprint i isB index loc) :
    if isB then l.sharedBase + 68608 ≤ loc.addr else loc.addr < l.sharedBase + 68608 := by
  obtain ⟨_,d,op,accum,mask,hIssue,hByte⟩ := mmaSharedFootprintIssue hX h
  rcases actualMmaInstruction hX hIssue with ⟨block,step,hQk⟩ | ⟨block,step,hPv⟩
  · cases isB
    · have hLoc := ((hQk.queryOperand hp hX).operandBankRange hp hByte).2.2
      change loc.addr < l.sharedBase+68608
      apply hLoc.trans_le
      have hStage := (PTX.Kernels.TmlFa4Fwd.Mma.qkStage block).isLt
      have hStep := step.isLt
      unfold PTX.Kernels.TmlFa4Fwd.Mma.qStart PTX.Kernels.TmlFa4Fwd.Mma.qkPlane
      omega
    · exact (hQk.keyByteBank hp hX hByte).2
  · have hB := hPv.sharedOperandB hX hByte
    subst isB
    exact (hPv.valueByteBank hp hX hByte).2

end PTX.Kernels.TmlFa4Fwd.Thread
