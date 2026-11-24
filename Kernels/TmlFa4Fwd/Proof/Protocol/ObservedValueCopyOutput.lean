-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.ObservedValueReadyOutput
public import Kernels.TmlFa4Fwd.Proof.Protocol.RecurringCacheOutput
public import Kernels.TmlFa4Fwd.Proof.Protocol.ObservedCacheCopyCoordinates

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX PTX.Proof PTX.AsyncCopy Thread
open PTX.Kernels.TmlFa4Fwd.Mma
open PTX.Kernels.TmlFa4Fwd.Loader (kvUseStage)

namespace Output

/-- A V copy that covers a byte of the staging area has an actual consuming
PV fragment before the final output whenever that generation has reached the final issuer. -/
theorem observedValueCopyUseBeforeFinal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g wait final : Nat} {output : TcCommit.Spec}
    (hFinal : SecondOutputCommit X (g,final) output)
    {copy : EvId} {event : Event} (he : X.get copy = some event)
    (hVector : Thread.Loader.recurringVectorEvent event) {spec : Spec}
    (hKind : event.kind = .copy spec) (hCta : copy.1 / l.block = g / l.block)
    {loc : Loc} (hCover : spec.dst.Covers loc)
    (hOdd : Thread.Loader.recurringUseBefore X copy % 2 = 1)
    (hReady : Thread.Mma.ReadyPoll l X g wait
      (readyStage (Thread.Loader.recurringUseBefore X copy))
      (readyWord (Thread.Loader.recurringUseBefore X copy)) true .cta)
    (hRank : Thread.Mma.readyCount X g wait = Thread.Loader.recurringUseBefore X copy)
    (hBefore : TraceBefore X (g,wait) (g,final)) :
    let use := Thread.Loader.recurringUseBefore X copy
    CacheUseBeforeCommit l X (g,final) (kvUseStage use) (use/3) loc := by
  obtain ⟨done⟩ := LoaderReady.completedAtFinalReady hp hX hFinal hReady hRank
  obtain ⟨lane,pair,upper,offset,hOffset,hLoc⟩ :=
    done.recurringCopyCoveredCoordinates hp hX he hVector hKind rfl hCta hCover
  rw [hLoc]
  exact observedValueReadyBeforeFinal hp hX hFinal hReady hRank hOdd hBefore 0
    lane pair upper hOffset

end Output
end PTX.Kernels.TmlFa4Fwd.Protocol
