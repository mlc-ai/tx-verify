-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstScoreValues
public import Kernels.TmlFa4Fwd.Proof.SoftmaxObservedScores
import Lemmas.Tcgen05.TcFence
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

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.TcMma PTX.Assumption

set_option maxRecDepth 100000 in
private theorem firstQkCommitFloor (stage : Fin 2) :
    let commitPc := (Mma.commitSite (Mma.qkCommitSite (firstQkBlock stage))).pc
    (kernel.code.drop commitPc).all (fun i => Thread.staysPastEvent commitPc i.op) = true := by
  fin_cases stage <;> kernel_rfl

set_option maxRecDepth 100000 in
private theorem firstQkCommitFloorSegments (stage : Fin 2) :
    let commitPc := (Mma.commitSite (Mma.qkCommitSite (firstQkBlock stage))).pc
    Assumptions.swExp2Sites.all (fun pc =>
      match cuteExp2.matchAt kernel pc with
      | some seg => decide (commitPc ≤ seg.stop)
      | none => false) = true := by
  fin_cases stage <;> kernel_rfl

/-- Each issued fragment of an initial QK block precedes its actual score-ready commit. -/
theorem firstObservedQkBeforeCommit {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {stage : Fin 2} {producer consumer start commit wait use : Nat}
    (hPhase : FirstQkPhase l X stage producer consumer commit wait)
    (step : Fin 8)
    (hIssue : X.get (producer, start + step.val) =
      some (Mma.qkIssueEvent l producer (firstQkBlock stage) step use)) :
    start + step.val < commit := by
  apply Thread.traceOrderOfPcFloor hX (firstQkCommitFloor stage)
    (firstQkCommitFloorSegments stage) hIssue hPhase.commitEvent _ le_rfl
  change Mma.qkPc (firstQkBlock stage) + step.val <
    (Mma.commitSite (Mma.qkCommitSite (firstQkBlock stage))).pc
  have hStep := step.isLt
  fin_cases stage
  · change 2197 + step.val < 2208
    omega
  · change 2259 + step.val < 2270
    omega

/-- An actual first score word holds its dot product when the selected QK operands and
competing cell accesses satisfy their provenance and ordering conditions. The observed QK
commit supplies completion and the operand snapshots for every one of its eight fragments. -/
theorem firstObservedQkScoreWord {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {stage : Fin 2} {producer consumer start commit wait read use batch head firstQ firstK : Nat}
    (hPhase : FirstQkPhase l X stage producer consumer commit wait)
    (hAfter : wait < read)
    (hIssues : ∀ step : Fin 8, X.get (producer, start + step.val) =
      some (Mma.qkIssueEvent l producer (firstQkBlock stage) step use))
    (q : Fin 4) (word : Fin 32) {vals : List Value}
    (he : X.get (consumer, read) = some
      ⟨scorePc .first q, .tc (.ld (scoreAddress l consumer stage q) vals .s32x32b)⟩)
    (hIn : Mma.QkCellInputs p l X producer (firstQkBlock stage) use batch head firstQ firstK
      (tmemRow l consumer) (firstScoreColumn q word) (fun step => (producer, start + step.val)))
    (hPrior : ∀ step : Fin 8, step.val ≠ 0 →
      ReadSource l X .acc (producer, start + (step.val - 1)) (producer, start + step.val)
        (tcDataCell l consumer .s32x32b (scoreAddress l consumer stage q) word.val))
    (hOutside : ∀ other,
      let cell := tcDataCell l consumer .s32x32b (scoreAddress l consumer stage q) word.val
      (X.MmaCell other cell ∨ StoreCell l X other cell) →
      (∀ step : Fin 8, other ≠ (producer, start + step.val)) →
      WriteBefore l X other (producer, start + 7) ∨ ReadBefore l X .ld (consumer, read) other)
    (hLive : SourceLive l X (producer, start + 7) (consumer, read)
      (tcDataCell l consumer .s32x32b (scoreAddress l consumer stage q) word.val)) :
    vals[word.val]? =
      some (.float .f32 (firstScoreDot p l consumer batch head firstQ firstK q word)) := by
  have hBefore := firstObservedQkBeforeCommit hX hPhase 7 (hIssues 7)
  have hSnapshots (step : Fin 8) :
      ∃ ops, X.async.mmaOperands (producer, start + step.val) = some ops := by
    have hMma : X.TcAsync (producer, start + step.val) := .inl ⟨_, _, _, _, _, hIssues step⟩
    have hCommit := firstObservedQkBeforeCommit hX hPhase step (hIssues step)
    have hDone := (firstScoreDoneBefore hX hPhase hMma hCommit q he hAfter).done hX.tcCommit
    have hStarted := hX.tma.2.1.2 _ hDone
    rcases hX.tma.2.1.1 _ hStarted with ⟨_, _, _, _, ops, _, hs, _⟩ |
      ⟨_, ops, _, hs, _⟩ | ⟨_, ops, _, hs, _⟩
    all_goals exact ⟨ops, hs⟩
  have hResult := firstQkScoreResult hX hPhase.sameCta hIssues hSnapshots q word hIn hPrior
  exact firstObservedScoreWord hX hPhase hBefore hAfter q word he hResult
    (firstQkOtherWrites hX hPhase.sameCta.1 stage hIssues _ _ hOutside) hLive

end PTX.Kernels.TmlFa4Fwd.Softmax
