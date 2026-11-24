-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MetadataReads
import Kernels.TmlFa4Fwd.Proof.EpilogueWarpStartup
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
import Kernels.TmlFa4Fwd.Proof.RegisterHintBody
import Lemmas.Flow.ContinuingEvent

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Output
open PTX PTX.Flow PTX.Proof Prologue Epilogue

private theorem outputSchedulerSuffix {l : Launch} {g : Nat}
    {s : TState} {events : List Event} {o : Option TState}
    (hs : 2777 ≤ s.pc) (hr : Run kernel Assumptions.all l g s events o) :
    ∀ e ∈ events, 2777 ≤ e.pc := by
  obtain ⟨_, hWalk⟩ := Mma.walkFromRun hr
  exact eventTailEvents (floor := 2777) (by decide +kernel) (by decide +kernel) hWalk hs

/-- The drain scheduler's first observed CuQ access addresses its lane's launch word.
The address follows from the prefix, with arbitrary bytes returned by that read. -/
theorem firstSchedulerCuQFootprint {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} {a : Acc} {bs : List (Option Byte)} (he : X.get (g, j) = some ⟨2776, .rd a bs⟩) :
    j = 6 ∧ laneOf l g ≤ p.batch ∧
      a = {loc := globalLoc (p.cuQBase + 4 * laneOf l g), size := 4} := by
  have hRole := roleBodyPcOfEvent hp hX he (by change 173 < 2776; decide)
    (by change 2776 ∉ registerHintSites; decide)
  have hw : warpIndex l g = 13 := by
    change roleBodyPc (warpIndex l g) 2776 at hRole
    unfold roleBodyPc at hRole
    rcases hRole with h | h
    · cases h
    · split_ifs at h <;> omega
  have hg := event_thread_lt hX he
  have hj := warp13StartupBeforeEvent hp hX hg hw he (.inl (by change 2769 < 2776; decide))
  have hLen : j < (X.tr g).length := len_of_get he
  obtain ⟨t, o, hr, ht, hf, hBatch, hBase⟩ :=
    warp13SchedulerEntryOfNonemptyPrefix hp hX hg hw (hj.trans_lt hLen)
  have hMore : (X.tr g).drop 6 ≠ [] :=
    fun h => Nat.not_le_of_lt hLen ((List.drop_eq_nil_iff.mp h).trans hj)
  obtain ⟨u, hLocal, hClean, hPc, hLaneReg, _, hPart, _, hKeep⟩ :=
    enterSchedulerWith (A := Assumptions.all) hp g t ht hf hBatch
  by_cases hLane : laneOf l g ≤ p.batch
  · have hu : u.pc = 2774 := by simpa [Nat.not_lt_of_ge hLane] using hPc
    obtain ⟨v, hAddr, hv, _, _, _, hOut⟩ := schedulerLaneReadWith (A := Assumptions.all) hp g u
      hLane hu hClean (hPart hLane).1 (hPart hLane).2 hLaneReg
      ((hKeep 7506 (by decide)).trans hBase)
    let expected : Acc := {loc := globalLoc (p.cuQBase + 4 * laneOf l g), size := 4}
    have hNext : Next kernel Assumptions.all l g t v (.read expected (afterLoad v [7217])) :=
      ⟨run_rtg (run_comp hLocal hAddr), hOut⟩
    obtain ⟨hPos, hAcc⟩ := hNext.uniqueScalarReadAt hv hr hj he
      (fun _ _ => outputSchedulerSuffix)
    exact ⟨hPos, hLane, hAcc⟩
  · have hu : u.pc = 2777 := by simpa [Nat.lt_of_not_ge hLane] using hPc
    have hIndexed : ((X.tr g).drop 6)[j - 6]? = some ⟨2776, .rd a bs⟩ := by
      rw [List.getElem?_drop, Nat.add_sub_of_le hj]
      exact he
    have hBad := outputSchedulerSuffix hu.ge (hr.after_local_nonempty (run_rtg hLocal) hMore)
      _ (List.mem_of_getElem? hIndexed)
    change 2777 ≤ 2776 at hBad
    omega

end PTX.Kernels.TmlFa4Fwd.Thread.Output
