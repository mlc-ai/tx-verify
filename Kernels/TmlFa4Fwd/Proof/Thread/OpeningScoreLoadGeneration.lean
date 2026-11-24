-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxScorePhase
public import Kernels.TmlFa4Fwd.Proof.Thread.OpeningScoreOrdinal
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
import Kernels.TmlFa4Fwd.Proof.Thread.MmaScoreRounds
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaInitialQueryAcquire
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaQueryRounds

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.Proof PTX.AsyncCopy PTX.Assumption
open PTX.Kernels.TmlFa4Fwd.Mma

set_option maxRecDepth 100000 in
private theorem openingLoadsBeforeBias : (kernel.code.drop 3498).all
    (fun i => Thread.staysPastEvent 3498 i.op) = true := by
  kernel_rfl

set_option maxRecDepth 100000 in
private theorem openingLoadsBeforeExp :
    Assumptions.swExp2Sites.all (fun pc =>
      match cuteExp2.matchAt kernel pc with
      | some seg => decide (3498 ≤ seg.stop)
      | none => false) = true := by
  kernel_rfl

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

/-- The opening score loads precede every packet-zero publication in their own lane. -/
theorem openingScoreLoadGeneration {g j address : Nat} {words : List Value} {shape : TcShape}
    (stage : Fin 2) (hRole : Prologue.warpIndex l g/4 = stage.val) (quarter : Fin 4)
    (he : X.get (g,j) = some ⟨Softmax.scorePc .first quarter,.tc (.ld address words shape)⟩) :
    probabilityOrdinal l X (g/l.block) stage 0 (g,j) = 0 := by
  have hWarp : Prologue.warpIndex l g < 8 := by have := stage.isLt; omega
  rw [← earlyProbabilityCount hp hX stage hWarp hRole (len_of_get he)]
  apply List.countP_eq_zero.mpr
  intro e hMem hMark
  obtain ⟨i,hGet⟩ := List.mem_iff_getElem?.mp hMem
  have hEarlier : i < j := (List.getElem?_eq_some_iff.mp hGet).1.trans_le (List.length_take_le ..)
  rw [List.getElem?_take_of_lt hEarlier] at hGet
  change X.get (g,i) = some e at hGet
  have hLate : 3498 ≤ e.pc := by
    simp [Softmax.earlyProbabilityMark] at hMark
    omega
  have hEarly : Softmax.scorePc .first quarter < 3498 := by fin_cases quarter <;> decide
  have hOrder : j < i := traceOrderOfPcFloor hX (floor := 3498)
    openingLoadsBeforeBias openingLoadsBeforeExp he hGet hEarly hLate
  exact (Nat.not_lt_of_ge hEarlier.le) hOrder

/-- A decoded commit block of ordinal zero is the opening QK block of that stage. -/
theorem scoreBlockOfOrdinalZero {g j : Nat} {spec : TcCommit.Spec} (stage : Fin 2) (block : Fin 4)
    (hStage : block.val % 2 = stage.val)
    (he : X.get (g,j) = some ⟨(commitSite (qkCommitSite block)).pc,.tc (.commit spec)⟩)
    (hOrdinal : scoreCommitOrdinal l X (g/l.block) stage (g,j) = 0) :
    block = initialQkBlock stage := by
  by_contra hn
  have hBlock : block = recurringKeyBlock stage := by
    fin_cases stage <;> fin_cases block <;> first | rfl | contradiction
  subst block
  have hPositive := recurringScoreExactOrdinal hp hX stage he
  omega

/-- The bank of a generation-zero score commit has the opening block at its last issue. -/
theorem ScoreCommit.lastFragmentOpeningBlock {commit : EvId} {stage : Fin 2} {spec : TcCommit.Spec}
    {rank : Fin 16} (hScore : ScoreCommit l X commit (commit.1/l.block) stage spec rank)
    (hGen : scoreCommitOrdinal l X (commit.1/l.block) stage commit = 0) {block : Fin 4} {j d : Nat}
    {op : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (hLast : QkInstruction X (commit.1,j) block 7 d op acc mask) (hAdjacent : j + 2 = commit.2)
    : block = initialQkBlock stage := by
  obtain ⟨b,hStage,hCommit⟩ := scoreCommitSite hp hX hScore
  have hb := scoreBlockOfOrdinalZero hp hX stage b hStage hCommit hGen
  obtain ⟨i,hPos,_,_,_,_,hi⟩ := qkLastFragmentAdjacentToScoreCommit hp hX b hCommit
  have hSame : i = j := by omega
  subst i
  have hPc : qkPc b + 7 = qkPc block + 7 :=
    congrArg Event.pc (Option.some.inj (hi.decoded.symm.trans hLast.decoded))
  have hEq : b = block := by fin_cases b <;> fin_cases block <;> first | rfl | contradiction
  exact hEq.symm.trans hb

end PTX.Kernels.TmlFa4Fwd.Thread.Scores

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX
open PTX.Kernels.TmlFa4Fwd.Mma (initialQkBlock)

theorem QkInstruction.initialQueryFragment {X : Execution} {i : EvId} {stage : Fin 2}
    {step : Fin 8} {d : Nat} {op : TcMma.OperandSpec} {acc : Bool} {mask : List Nat}
    (h : QkInstruction X i (initialQkBlock stage) step d op acc mask) :
    Mma.InitialQueryFragment X stage i :=
  ⟨step,d,op,acc,mask,h.decoded⟩

end PTX.Kernels.TmlFa4Fwd.Thread
