-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.NamedBarriers
public import Kernels.TmlFa4Fwd.Proof.Thread.NamedBarrierProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Statistics
open PTX Thread Prologue

/-- A statistics synchronization in a maximal prefix either has a lagging participant or can
be released by recording the arrived peers. The release preserves all writes. -/
theorem synchronizationFrontier {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    (hCuQ : Epilogue.DrainCuQProtected p X)
    {g : Nat} (hg : g < l.threads) (w : Fin 8)
    (hWait : BarrierArrival X (g,(X.tr g).length - 1) (3 + w.val) (some 64) .sync) :
    (∃ lane < l.block, lane / 32 ∈ statsParticipants w ∧
      (X.tr (g / l.block * l.block + lane)).countP (Execution.isBarId (3 + w.val)) ≤
        observedBarrierOrdinal X (g,(X.tr g).length - 1) (3 + w.val)) ∨
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧
      Y.MemWrites = X.MemWrites ∧ Step.Released l Y g := by
  classical
  by_cases hArrivals : ∀ lane < l.block, lane / 32 ∈ statsParticipants w →
      observedBarrierOrdinal X (g,(X.tr g).length - 1) (3 + w.val) <
        (X.tr (g / l.block * l.block + lane)).countP (Execution.isBarId (3 + w.val))
  · right
    refine releaseSynchronization hMax (fun Y hY _ hWrites => ?_) hg (statsBarrierShape hp w)
      (statsBarrierSources hp hMax.1 w) hWait hArrivals
    exact noActualNamedBarrierFault hp hY (fun i hi k hk ref a bytes hWrite =>
      hCuQ i hi k hk ref a bytes (hWrites ▸ hWrite))
  · left
    push Not at hArrivals
    exact hArrivals

end PTX.Kernels.TmlFa4Fwd.Protocol.Statistics
