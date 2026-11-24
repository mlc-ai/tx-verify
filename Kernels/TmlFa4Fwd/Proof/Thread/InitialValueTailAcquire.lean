-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.InitialValueOperands
public import Kernels.TmlFa4Fwd.Proof.Thread.InitialValueAcquire

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof
open PTX.Kernels.TmlFa4Fwd.Mma (pvPc readyEvent)

/-- Every actual fragment in a tail PV group follows the initial slot-one acquire
on the contributing warp's trace, when the CTA traverses its tail directly. -/
theorem InitialValueFragment.readyBeforeTail {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {i commit : EvId} {spec : TcCommit.Spec} (hCommit : SecondOutputCommit X commit spec)
    (hLane : i.1 = commit.1)
    {stage : Fin 2} {step : Fin 8} {d : Nat} {op : TcMma.OperandSpec}
    {accum : Bool} {mask : List Nat}
    (hFragment : InitialValueFragment X i false stage step d op accum mask) :
    ∃ wait, Mma.ReadyPoll l X i.1 wait 1 0 true .cta ∧
      TraceBefore X (i.1,wait) i ∧
      (((X.tr i.1).take wait).filterMap readyEvent).length = 1 := by
  obtain ⟨g,j⟩ := i
  obtain ⟨h,finish⟩ := commit
  change g = h at hLane
  subst h
  have he : X.get (g,j) = some ⟨pvPc (firstPvBlock false stage) step,.tc (.mma d op accum mask)⟩ :=
    hFragment
  have hBounds : 2548 ≤ pvPc (firstPvBlock false stage) step ∧
      pvPc (firstPvBlock false stage) step ≤ 2646 := by
    fin_cases stage <;> fin_cases step <;> decide
  exact initialValueAcquireBeforeTailEvent hp hX hCommit he hBounds.1 hBounds.2

end PTX.Kernels.TmlFa4Fwd.Thread
