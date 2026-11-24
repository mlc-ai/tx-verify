-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.RecurringCacheCoverage
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaValueUseRelease
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPendingCursor
import Kernels.TmlFa4Fwd.Proof.Protocol.PendingCacheExact
import Kernels.TmlFa4Fwd.Proof.Thread.MmaCacheReleaseIssuer
import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderReuseOrder

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX PTX.Proof PTX.AsyncCopy PTX.TcMma Thread
open PTX.Kernels.TmlFa4Fwd.Mma
open PTX.Kernels.TmlFa4Fwd.Loader (kvUseStage)

namespace LoaderReady

/-- A later pending same-slot copy is ordered after the actual V fragment whose
empty release permits the copy. The later publication may remain open. -/
theorem valueBeforePendingCacheCopy {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {block : Fin 4} {step : Fin 8} {d : Nat} {op : OperandSpec}
    {accum : Bool} {mask : List Nat}
    (hValue : PvInstruction X (g,index) block step d op accum mask)
    {producer copyIndex : Nat} {event : Event} (hEvent : X.get (producer,copyIndex) = some event)
    (hVector : Thread.Loader.recurringVectorEvent event)
    {byte use : Nat} {loc : Loc} {copy : Spec} (hKind : event.kind = .copy copy)
    (hUse : Thread.Mma.LatestValueReadyUse l X g index use)
    (hOperand : op.byteLoc .b byte = some loc) (hCover : copy.dst.Covers loc)
    (hSlot : kvUseStage (Thread.Loader.recurringUseBefore X (producer,copyIndex)) =
      kvUseStage use)
    (hLater : use < Thread.Loader.recurringUseBefore X (producer,copyIndex)) :
    X.AsyncPresent (g,index) (.mmaRead true byte) ∧
      modelCausality l X loc (.async (g,index) (.mmaRead true byte))
        (.async (producer,copyIndex) (.write .copy)) := by
  let next := Thread.Loader.recurringUseBefore X (producer,copyIndex)
  have hMod : next % 3 = use % 3 := congrArg Fin.val hSlot
  change use < next at hLater
  have hPositive : 0 < next/3 := by omega
  obtain ⟨wait,issuer,position,release,hWait,hResume,hPhase,hSeen⟩ :=
    pendingCacheGuardObservedReleaseExact hp hX hEvent hVector hKind hPositive
  have hMma : X.MmaIssue (g,index) d op accum mask := ⟨_,hValue.decoded⟩
  have hCopy := Thread.Loader.actualCopyOfRecurringVector hEvent hVector hKind
  obtain ⟨_,_,_,_,hDst⟩ := Thread.Loader.copyDestination hp hX hCopy
  have hCopyCta : loc.cta = producer/l.block := by
    have hCovered := hDst ▸ hCover
    exact hCovered.2.1
  have hMmaCta := (hValue.valueByteRange hp hX hOperand).cta
  have hOwner : g/l.block = issuer/l.block := by
    rw [← release.issuerCta hp hX, hResume.1.1, ← hCopyCta, hMmaCta]
  obtain rfl := Thread.Mma.sameCacheReleaseIssuer hp hX hMma release.issue hOwner
  have hUseBound : use ≤ 3 * release.ordinal + (kvUseStage next).val := by
    change release.ordinal = next/3-1 at hPhase
    change use ≤ 3 * release.ordinal + next % 3
    omega
  have hEarlier := Thread.Mma.valueBeforeReleaseOfUse hp hX hValue release hUse hSlot hUseBound
  exact observedOperandBeforeReuse hp hX release hSeen hWait hMma hEarlier hOperand hResume hCopy
    hCover

end LoaderReady

namespace Output

end Output
end PTX.Kernels.TmlFa4Fwd.Protocol
