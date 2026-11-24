-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.TrackedCacheOverwrite
public import Kernels.TmlFa4Fwd.Proof.Protocol.PendingCacheExact
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPendingCopyCoordinates
import Kernels.TmlFa4Fwd.Proof.Thread.MmaReleaseUse

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.AsyncCopy
open Thread.Loader (recurringUseBefore recurringVectorEvent)
open PTX.Kernels.TmlFa4Fwd.Loader (kvUseStage)

/-- A later recurring copy that overlaps an older recurring copy observes an
actual same-slot release, which orders the old and new writes byte by byte. -/
theorem recurringCopyBeforeLaterRecurringCopy {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {old new : EvId} {a b : Event} (ha : X.get old = some a) (hb : X.get new = some b)
    (hOldVector : recurringVectorEvent a) (hNewVector : recurringVectorEvent b)
    {s t : Spec} (hs : a.kind = .copy s) (ht : b.kind = .copy t)
    {loc : Loc} (hOldCover : s.dst.Covers loc) (hNewCover : t.dst.Covers loc)
    (hOlder : recurringUseBefore X old < recurringUseBefore X new) :
    modelCausality l X loc (.async old (.write .copy)) (.async new (.write .copy)) := by
  obtain ⟨g,index⟩ := new
  let use := recurringUseBefore X (g,index)
  let slot := kvUseStage use
  have hSlot := Thread.Loader.pendingCopiesSameSlot hp hX ha hb hOldVector hNewVector hs ht
    hOldCover hNewCover
  have hMod := congrArg Fin.val hSlot
  change recurringUseBefore X old % 3 = use % 3 at hMod
  change recurringUseBefore X old < use at hOlder
  have hPositive : 0 < use/3 := by omega
  obtain ⟨wait,issuer,position,release,hEmpty,hGuard,hOrdinal,hObserved⟩ :=
    pendingCacheGuardObservedReleaseExact hp hX hb hNewVector ht hPositive
  have hRank : recurringUseBefore X old ≤ 3 * release.ordinal + slot.val := by
    change recurringUseBefore X old ≤ 3 * release.ordinal + use%3
    rw [hOrdinal]
    omega
  have hOld := Thread.Loader.actualCopyOfRecurringVector ha hOldVector hs
  have hNew := Thread.Loader.actualCopyOfRecurringVector hb hNewVector ht
  obtain ⟨lane,pair,upper,off,hOff,hLoc⟩ :=
    Thread.Loader.pendingCopyCoveredCoordinates hp hX hb hNewVector ht hNewCover
  have hOwner : g/l.block = issuer/l.block :=
    (congrArg (· / l.block) hGuard.1.1.symm).trans (release.issuerCta hp hX)
  change loc = ⟨.shared,g/l.block,kvCopyAddress l.sharedBase slot lane pair upper+off⟩ at hLoc
  rw [hOwner] at hLoc
  rw [hLoc] at hOldCover hNewCover ⊢
  cases hForm : release.form with
  | firstKey =>
    have hZero := release.firstKeyUse hp hX hForm
    change 3 * release.ordinal + slot.val = 0 at hZero
    have hLower : 2 ≤ recurringUseBefore X old := by unfold recurringUseBefore; omega
    omega
  | loopValue =>
    exact earlierRecurringCopyBeforeValueGuardedCopy hp hX release true hForm hObserved hEmpty
      hGuard hNew hOld hRank 0 lane pair upper hOff hOldCover hNewCover
  | loopKey =>
    exact earlierRecurringCopyBeforeKeyGuardedCopy hp hX release hForm hObserved hEmpty
      hGuard hNew hOld hRank 0 lane pair upper hOff hOldCover hNewCover
  | tailValue =>
    exact earlierRecurringCopyBeforeValueGuardedCopy hp hX release false hForm hObserved hEmpty
      hGuard hNew hOld hRank 0 lane pair upper hOff hOldCover hNewCover

end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
