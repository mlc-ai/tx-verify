-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderDrainLaterSelection
public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderDrainGenerations

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX Prologue Epilogue Thread.Loader Protocol.Loader

/-- A scheduled loader retires when its producer loop and the corresponding release
credits are recorded, independently of the number of KV visits or request groups. -/
theorem cacheLoaderExitOfCompletedCredits {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g use : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    (hCuQ : DrainCuQProtected p X) (hActive : g/l.block < tilePrefix p p.batch*p.heads)
    (hReached : CacheDrainEntry p l X g use)
    (hCredits : CacheReleaseCounts l X g use)
    (hQuery : warpIndex l g = 14 → UnitRelease X (secondQueryEmpty l (g/l.block))) :
    Thread.Exited X g :=
  cacheDrainExitOfMaximal hp hMax hg hw hCuQ hActive hReached
    (cacheDrainReadyOfCreditCount hp hMax hg hCredits)
    (fun hWarp => queryDrainReadyOfUnitRelease hp hMax hg (hQuery hWarp))

end PTX.Kernels.TmlFa4Fwd.Progress
