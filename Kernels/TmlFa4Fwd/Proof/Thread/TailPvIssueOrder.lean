-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvOperandFields
import Kernels.TmlFa4Fwd.Proof.Thread.MmaPvPipeline
import Kernels.TmlFa4Fwd.Proof.MmaReadyReleaseElection
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpReady
import Kernels.TmlFa4Fwd.Proof.OutputAssignedBox
import Kernels.TmlFa4Fwd.Proof.EpiloguePrefixStartup
import Kernels.TmlFa4Fwd.Proof.EpilogueCuts
import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.MmaLoopEntryBound
import Lemmas.Flow.NotClc
import Lemmas.Step.CtaBar
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopEvents
import Kernels.TmlFa4Fwd.Proof.RoleDispatch
import Kernels.TmlFa4Fwd.Proof.PrologueDispatchTrace
import Kernels.TmlFa4Fwd.Proof.PrologueWarp0Prefix
import Kernels.TmlFa4Fwd.Proof.SoftmaxLoopFlow
import Kernels.TmlFa4Fwd.Proof.LoaderCountExit
import Kernels.TmlFa4Fwd.Proof.Thread.DecodedEventFrame
import Kernels.TmlFa4Fwd.Proof.Thread.TraceFloor

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.EventFrame
open PTX.Kernels.TmlFa4Fwd.Mma

set_option maxRecDepth 100000 in
private theorem tailFragmentFloor (stage : Fin 2) (step : Fin 8) :
    let floor := pvPc (firstPvBlock false stage) step+1
    (kernel.code.drop floor).all (fun ins => staysPastEvent floor ins.op) = true := by
  fin_cases stage <;> fin_cases step <;> kernel_rfl

set_option maxRecDepth 100000 in
private theorem tailFragmentSegments :
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some s => decide (2635 ≤ s.stop)
      | none => false) = true := by kernel_rfl

private theorem tailFragmentSegmentFloor (stage : Fin 2) (step : Fin 8) :
    let floor := pvPc (firstPvBlock false stage) step+1
    Assumptions.swExp2Sites.all (fun site => match cuteExp2.matchAt kernel site with
      | some s => decide (floor ≤ s.stop)
      | none => false) = true := by
  let floor := pvPc (firstPvBlock false stage) step+1
  have hFloor : floor ≤ 2635 := by fin_cases stage <;> fin_cases step <;> decide
  apply List.all_eq_true.mpr
  intro site hSite
  have h := List.all_eq_true.mp tailFragmentSegments site hSite
  cases he : cuteExp2.matchAt kernel site with
  | none => simp [he] at h
  | some seg =>
    simp only [he,decide_eq_true_eq] at h ⊢
    exact hFloor.trans h

/-- Actual fragments in a tail stage occur in ascending fragment order. -/
theorem PvInstruction.tailTraceOrder {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) {i j : EvId} {a b : Fin 8} {d d' : Nat}
    {op op' : TcMma.OperandSpec} {acc acc' : Bool} {mask mask' : List Nat}
    (hi : PvInstruction X i (firstPvBlock false stage) a d op acc mask)
    (hj : PvInstruction X j (firstPvBlock false stage) b d' op' acc' mask')
    (hCta : i.1/l.block = j.1/l.block) (hLt : a.val < b.val) : TraceBefore X i j := by
  obtain ⟨g,k⟩ := i
  obtain ⟨h,n⟩ := j
  have hLane : g = h := mmaIssueSameThread hp hX ⟨_,hi.decoded⟩ ⟨_,hj.decoded⟩ hCta
  subst h
  have hPc : pvPc (firstPvBlock false stage) a+1 ≤ pvPc (firstPvBlock false stage) b := by
    unfold pvPc
    split <;> split <;> omega
  have hi' := hi.decoded
  have hj' := hj.decoded
  have hk := traceOrderOfPcFloor hX (tailFragmentFloor stage a)
    (tailFragmentSegmentFloor stage a) hi' hj' (Nat.lt_succ_self _) hPc
  exact ⟨rfl,hk,len_of_get hj'⟩

private theorem tailFragmentCannotRepeat {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) (stage : Fin 2) (step : Fin 8)
    {g i j d d' : Nat} {op op' : TcMma.OperandSpec}
    {acc acc' : Bool} {mask mask' : List Nat}
    (hi : PvInstruction X (g,i) (firstPvBlock false stage) step d op acc mask)
    (hj : PvInstruction X (g,j) (firstPvBlock false stage) step d' op' acc' mask')
    (hlt : i < j) : False := by
  have hi' := hi.decoded
  have hj' := hj.decoded
  have hg := event_thread_lt hX hi'
  have hLen : j < (X.tr g).length := len_of_get hj'
  obtain ⟨_,hr⟩ := hX.thr g hg
  obtain ⟨s,u,hStep,hRun⟩ := hr.after_event hi' (by omega)
  have hRet := (pvFieldsOfStep hg (firstPvBlock false stage) step hStep).2.2.2
  obtain rfl := Option.some.inj hRet
  obtain ⟨_,hWalk⟩ := walkFromRun hRun
  have hStart : pvPc (firstPvBlock false stage) step+1 ≤ (next s).pc :=
    Nat.le_of_eq (congrArg (·+1) (estep_source_pc hStep))
  have hMem : ⟨pvPc (firstPvBlock false stage) step,.tc (.mma d' op' acc' mask')⟩ ∈
      (X.tr g).drop (i+1) := by
    apply List.mem_of_getElem? (i := j-(i+1))
    rwa [List.getElem?_drop,Nat.add_sub_of_le (by omega)]
  have hBad := eventTailEvents (tailFragmentFloor stage step)
    (tailFragmentSegmentFloor stage step) hWalk hStart _ hMem
  exact (Nat.not_succ_le_self _) hBad

/-- A tail fragment occurs at most once on the implementing lane of its CTA. -/
theorem PvInstruction.tailUnique {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (stage : Fin 2) {i j : EvId} {step : Fin 8} {d d' : Nat}
    {op op' : TcMma.OperandSpec} {acc acc' : Bool} {mask mask' : List Nat}
    (hi : PvInstruction X i (firstPvBlock false stage) step d op acc mask)
    (hj : PvInstruction X j (firstPvBlock false stage) step d' op' acc' mask')
    (hCta : i.1/l.block = j.1/l.block) : i = j := by
  obtain ⟨g,k⟩ := i
  obtain ⟨h,n⟩ := j
  have hLane : g = h := mmaIssueSameThread hp hX ⟨_,hi.decoded⟩ ⟨_,hj.decoded⟩ hCta
  subst h
  rcases lt_trichotomy k n with h | rfl | h
  · exact (tailFragmentCannotRepeat hX stage step hi hj h).elim
  · rfl
  · exact (tailFragmentCannotRepeat hX stage step hj hi h).elim

end PTX.Kernels.TmlFa4Fwd.Thread
