-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.ObservedCacheCopyCoordinates
public import Kernels.TmlFa4Fwd.Proof.Protocol.ObservedValueReadyOutput
public import Kernels.TmlFa4Fwd.Proof.Protocol.RecurringCacheOutput
public import Kernels.TmlFa4Fwd.Proof.Protocol.RecurringCacheCoverage
import Kernels.TmlFa4Fwd.Proof.Thread.MmaKeyReleaseDescriptor

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Output
open PTX PTX.AsyncCopy Thread
open Mma (readyStage readyWord)
open Loader (kvUseStage)

/-- An actual recurring key copy is covered by a consuming QK fragment before
final O1 when its logical ready occurrence is present on the final issuer. -/
theorem observedKeyCopyUseBeforeFinal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g wait final : Nat} {output : TcCommit.Spec}
    (hFinal : SecondOutputCommit X (g,final) output)
    {copy : EvId} {event : Event} (he : X.get copy = some event)
    (hVector : Thread.Loader.recurringVectorEvent event) {spec : Spec}
    (hKind : event.kind = .copy spec) (hCta : copy.1 / l.block = g / l.block)
    {loc : Loc} (hCover : spec.dst.Covers loc)
    (hEven : Thread.Loader.recurringUseBefore X copy % 2 = 0)
    (hReady : Thread.Mma.ReadyPoll l X g wait
      (readyStage (Thread.Loader.recurringUseBefore X copy))
      (readyWord (Thread.Loader.recurringUseBefore X copy)) true .cta)
    (hRank : Thread.Mma.readyCount X g wait = Thread.Loader.recurringUseBefore X copy)
    (hBefore : TraceBefore X (g,wait) (g,final)) :
    let use := Thread.Loader.recurringUseBefore X copy
    CacheUseBeforeCommit l X (g,final) (kvUseStage use) (use/3) loc := by
  let use := Thread.Loader.recurringUseBefore X copy
  have hPositive : 0 < use := by
    unfold use Thread.Loader.recurringUseBefore
    omega
  obtain ⟨complete⟩ := LoaderReady.completedAtFinalReady hp hX hFinal hReady hRank
  obtain ⟨lane,pair,upper,offset,hOffset,hLoc⟩ :=
    complete.recurringCopyCoveredCoordinates hp hX he hVector hKind rfl hCta hCover
  obtain ⟨release,commit,matched,hRelease,hWait,hSlot,hEarlier⟩ :=
    Thread.Mma.keyReadyMatchBeforeFinal hp hX hFinal hReady hRank hPositive hEven hBefore
  obtain ⟨step,index,d,byte,op,accum,mask,hKey,hAfter,hBeforeRelease,hByte⟩ :=
    recurringKeyVectorReadOfMatch hp hX hRelease matched rfl 0 lane pair upper hOffset
  change loc = ⟨.shared,g/l.block,
    kvCopyAddress l.sharedBase (readyStage use) lane pair upper + offset⟩ at hLoc
  rw [hSlot,← hLoc] at hByte
  rw [hWait] at hAfter
  exact ⟨(g,wait),(g,index),d,op,accum,mask,byte,⟨complete⟩,hAfter,
    hBeforeRelease.trans hEarlier,⟨_,hKey.decoded⟩,hByte⟩

end PTX.Kernels.TmlFa4Fwd.Protocol.Output
