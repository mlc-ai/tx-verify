-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.IdleAllocationExits
import Kernels.TmlFa4Fwd.Proof.Thread.EpilogueScanProgress
import Kernels.TmlFa4Fwd.Proof.Progress.IdleLoader
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderIdleElection
import Kernels.TmlFa4Fwd.Proof.Protocol.IdleLoaderRelease

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX Prologue Epilogue

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g : Nat} (hg : g < l.threads)
include hp hMax hg

/-- Every lane of a CTA with no assigned tile exits in a maximal execution. -/
theorem idleCtaExitsOfAllGroups (hCuQ : DrainCuQProtected p X)
    (hIdle : tilePrefix p p.batch * p.heads ≤ g/l.block) :
    ∃ j e, X.get (g,j) = some e ∧ e.kind = .exit := by
  by_cases hParticipants : warpIndex l g < 13
  · exact idleAllocationParticipantsExitOfAllGroups hp hMax hg hParticipants hCuQ hIdle
  by_cases hOutput : warpIndex l g = 13
  · exact Epilogue.idleWarp13ExitOfAllGroups hp hMax hg hOutput hCuQ hIdle
  · exact idleLoaderExitsForBatches hp hMax hg (by omega) hCuQ hIdle

end PTX.Kernels.TmlFa4Fwd.Progress
