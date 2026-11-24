-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.InitialValueAcquire
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
import Kernels.TmlFa4Fwd.Proof.MmaReleaseOrdinals

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.Assumption PTX.Flow Prologue
open PTX.Kernels.TmlFa4Fwd.Mma (initialQueryOperandsBeforeFinalCommit initialQkBlock
  qkPc slotWait slotElect pendingReadyOrdinal readyHead readyEvent initialReadyPollOperands
  readyWaitBeforeGate waitSite commitSite releaseWaitSite releaseCommitSite)
open Mma.Observation (readyObject)

/-- Two recorded successful ready events require at least two projected observations. -/
theorem twoReadyProjections {xs : List Event} {i j stop : Nat}
    {e f : Event} {a b : Loc × Nat}
    (he : xs[i]? = some e) (hf : xs[j]? = some f) (hij : i < j) (hj : j < stop)
    (ha : readyEvent e = some a) (hb : readyEvent f = some b) :
    1 < ((xs.take stop).filterMap readyEvent).length := by
  have hA : a ∈ (xs.take j).filterMap readyEvent := by
    apply List.mem_filterMap.mpr
    refine ⟨e, List.mem_of_getElem? (i := i) (by rwa [List.getElem?_take_of_lt hij]), ha⟩
  obtain ⟨suffix, hSplit⟩ := List.take_prefix (j + 1) (xs.take stop)
  simp only [List.take_take, Nat.min_eq_left (show j + 1 ≤ stop by omega)] at hSplit
  have hStep : xs.take (j + 1) = xs.take j ++ [f] := by simp [List.take_add_one, hf]
  rw [← hSplit, hStep, List.filterMap_append, List.filterMap_append]
  simp only [List.filterMap_cons, hb, List.filterMap_nil, List.length_append,
    List.length_cons, List.length_nil]
  have := List.length_pos_of_mem hA
  omega

end PTX.Kernels.TmlFa4Fwd.Thread
