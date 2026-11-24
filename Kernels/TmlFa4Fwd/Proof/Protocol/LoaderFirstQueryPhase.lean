-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderQueryStartProgress
import Kernels.TmlFa4Fwd.Proof.Protocol.IdleLoaderRelease

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Loader
open PTX PTX.MBarrier Prologue Thread.Output Thread.Loader

/-- Before the first query has been observed, its empty object remains in the opening phase. -/
theorem firstQueryEmptyBeforeAcquire {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {cta : Nat} (hc : cta < l.grid)
    (hBefore : ¬ ∃ r ∈ X.objects (queryObject l cta 0), r.reply.waited = some true) :
    let log := X.objects (queryEmptyObject l cta 0)
    ∃ s, stateBefore log log.length = some s ∧ s.phase = 0 := by
  obtain ⟨hFirst,hInit⟩ :=
    PTX.Kernels.TmlFa4Fwd.Loader.firstQueryEmptyInitializedOfMaximal hp hMax hc
  exact releasePhaseZeroOfInitialized hMax.1 hFirst hInit (fun _ hr hUpdate =>
    hBefore (PTX.Kernels.TmlFa4Fwd.Loader.firstQueryObservedOfEmptyUpdate hp hMax.1 hr hUpdate))

end PTX.Kernels.TmlFa4Fwd.Protocol.Loader
