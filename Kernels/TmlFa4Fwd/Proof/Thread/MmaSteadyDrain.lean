-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyTailAssembly
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaActiveDrainSearch
import Kernels.TmlFa4Fwd.Proof.Thread.MmaActiveDrainStart

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Proof Prologue Epilogue

/-- For any recurring trip count, the final terminal output cursor enters the
normal MMA retirement scan and reaches the actual relinquish collective. -/
theorem relinquishAfterSteadyTerminalOutput {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) {g visit shuffles votes : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 12) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 2647
      (fun _ => steadyTerminalPvFrame l visit) shuffles votes ends) :
    MmaRelinquishPrefix l X g := by
  obtain ⟨words⟩ := drainWordsAtOutputCursor hp hMax hCuQ hg hw cur
  obtain ⟨neighbors⟩ := words.shuffleOfMaximal hp hMax hg
  exact neighbors.relinquishOfMaximal hp hMax hCuQ hg hw

end PTX.Kernels.TmlFa4Fwd.Mma
