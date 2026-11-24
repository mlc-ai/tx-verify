-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.RepeatedTerminalStatistics
public import Kernels.TmlFa4Fwd.Proof.Thread.RepeatedFirstStageStaging
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaTerminalOutputNotification
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaTerminalIssueTrace
public import Kernels.TmlFa4Fwd.Proof.Protocol.TerminalOutputPhase
import Kernels.TmlFa4Fwd.Proof.Progress.Async
import Kernels.TmlFa4Fwd.Proof.Progress.SyncGuarded
import Kernels.TmlFa4Fwd.Proof.MmaLayoutSafety
import Kernels.TmlFa4Fwd.Proof.Protocol.RepeatedProbabilityHistory
import Kernels.TmlFa4Fwd.Proof.Protocol.RescalePublicationValues
import Kernels.TmlFa4Fwd.Proof.Safety.TmemRescaleStoreValues
import Kernels.TmlFa4Fwd.Proof.Safety.MmaOperandCoverage
import Kernels.TmlFa4Fwd.Proof.OutputProtection

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Flow PTX.Proof Prologue Epilogue Thread
open _root_.PTX.Kernels.TmlFa4Fwd.Correction

/-- Either output phase is available to correction after the MMA warp's terminal commits. -/
theorem outputPhaseOfTerminalIssues {p : Params} {l : Launch} {m : Mem0} {X Y : Execution}
    (hp : Pre p l m) (hY : Maximal l kernel Assumptions.all m Y)
    (frame : OutputFootprint p Y) (tr : Y.tr = X.tr) {g cta : Nat} (hc : g/l.block = cta)
    (issues : Mma.TerminalOutputIssues l X g) (stage : Fin 2) :
    let log := Y.objects (outputCompletionObject l cta stage)
    ∃ state, MBarrier.stateBefore log log.length = some state ∧ state.phase = 1 := by
  obtain ⟨r,hr,ha⟩ := terminalOutputNotification hY.1 (issues.ofTrace tr) stage
    (mmaAndCommitsDrained hp hY frame).2
  rw [hc] at hr
  exact Protocol.Output.terminalOutputPhaseOfNotification hp hY.1 stage hr ha

theorem repeatedFirstStageStagingOfRows {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (frame : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {g batch issuer : Nat} (hg : g < l.threads) (hw : 8 ≤ warpIndex l g ∧ warpIndex l g < 12)
    (hb : batch < p.batch) (lo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hi : g/l.block < tilePrefix p (batch+1)*p.heads)
    (multiple : 2 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (rows : TerminalRowPublications l X (g/l.block)
      (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1))
    (cta : issuer/l.block = g/l.block) (issues : Mma.TerminalOutputIssues l X issuer) :
    Nonempty (FirstStageStagingDone p l X g batch) := by
  have f := frame X hMax.1
  have operands := Safety.mmaOperandsOfProbabilities hp hMax.1 f
    (Protocol.Scores.completedPvProbabilitiesOfExecution hp hMax.1 frame)
  have values := Safety.mmaCompletedValuesOfOperandsAndRescaleStores hp hMax.1
    (f.metadataProtected hp).1 operands
    (Protocol.Statistics.rescaleStoreValuesOfOutputFootprint hp hMax.1 frame)
  apply firstStageStagingOfIssuedLoads hp hMax f values hw _ g ⟨⟨hg,hg,rfl⟩,rfl⟩
  intro h same
  have owner := same.1.2.2
  have active := same.1.2.1
  have w : warpIndex l g = warpIndex l h := same.2
  have role : 8 ≤ warpIndex l h ∧ warpIndex l h < 12 := w ▸ hw
  obtain ⟨Y,hY,tr,_,⟨words⟩⟩ := repeatedFirstTerminalWordsOfRows hp hMax frame active role hb
    (owner ▸ lo) (owner ▸ hi) (owner ▸ multiple) (owner ▸ rows)
  have phase := outputPhaseOfTerminalIssues hp hY (frame Y hY.1) tr (cta.trans owner) issues 0
  have self : warpLane l h (laneOf l h) = h :=
    Step.warpLane_of_sameWarp ⟨⟨active,active,rfl⟩,rfl⟩
  obtain ⟨acquired⟩ := words.acquireFirstOutputOfMaximal hp hY (self.symm ▸ active)
    (by simpa only [self] using phase)
  exact ⟨Y,tr,acquired.issueLoadOfMaximal hp hY (syncGuarded hp hY.1
    ((frame Y hY.1).metadataProtected hp).1) (Mma.actualMmaLayoutInjective hY.1)
    (self.symm ▸ active) (self.symm ▸ role)⟩

end PTX.Kernels.TmlFa4Fwd.Progress
