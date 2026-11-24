-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.ObservedKeyCopyOutput
public import Kernels.TmlFa4Fwd.Proof.Protocol.ObservedValueCopyOutput
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSelectedCacheExtent

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Output
open PTX PTX.AsyncCopy Thread
open Loader (kvUseStage)

/-- Before the final output commit, the selected request has consumed every
recurring cache copy covering the byte through its own K or V generation. -/
theorem recurringCopyUseBeforeSelectedFinal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {final : EvId} {output : TcCommit.Spec}
    (hFinal : SecondOutputCommit X final output)
    (extent : Thread.Mma.SelectedCacheExtent l p X final)
    {copy : EvId} {e : Event} (he : X.get copy = some e)
    (hVector : Thread.Loader.recurringVectorEvent e) {spec : Spec}
    (hKind : e.kind = .copy spec) (hCta : copy.1 / l.block = final.1 / l.block)
    {loc : Loc} (hCover : spec.dst.Covers loc) :
    let use := Thread.Loader.recurringUseBefore X copy
    CacheUseBeforeCommit l X final (kvUseStage use) (use/3) loc := by
  obtain ⟨g,index⟩ := final
  obtain ⟨wait,hReady,hUse,hBefore⟩ :=
    extent.readyForRecurringCopy hp hX hFrame hFinal he hVector hKind hCta
  by_cases hEven : Thread.Loader.recurringUseBefore X copy % 2 = 0
  · exact observedKeyCopyUseBeforeFinal hp hX hFinal he hVector hKind hCta hCover
      hEven hReady hUse hBefore
  · exact observedValueCopyUseBeforeFinal hp hX hFinal he hVector hKind hCta hCover
      (by omega) hReady hUse hBefore

/-- A selected request extent for each actual final issuer supplies the
cache operand observation for the second staging write and pending output reads. -/
theorem recurringCopyUsesBeforeSelectedFinal {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X)
    (hExtent : ∀ final output, SecondOutputCommit X final output →
      final.1 / l.block < tilePrefix p p.batch * p.heads →
      Nonempty (Thread.Mma.SelectedCacheExtent l p X final))
    {copy : EvId} {e : Event} (he : X.get copy = some e)
    (hVector : Thread.Loader.recurringVectorEvent e) {spec : Spec}
    (hKind : e.kind = .copy spec) {loc : Loc} (hCover : spec.dst.Covers loc) :
    ∀ final commit, SecondOutputCommit X final commit → copy.1 / l.block = final.1 / l.block →
      ∃ (slot : Fin 3) (phase : Nat),
        Thread.Loader.recurringUseBefore X copy ≤ 3 * phase + slot.val ∧
        CacheUseBeforeCommit l X final slot phase loc := by
  intro final commit hFinal hCta
  have hWork := Thread.Mma.recurringVectorHasWork hp hX hFrame he hVector hKind
  obtain ⟨extent⟩ := hExtent final commit hFinal (hCta ▸ hWork)
  let use := Thread.Loader.recurringUseBefore X copy
  refine ⟨kvUseStage use,use/3,?_,?_⟩
  · change use ≤ 3 * (use/3) + use%3
    omega
  · exact recurringCopyUseBeforeSelectedFinal hp hX hFrame hFinal extent he hVector hKind
      hCta hCover

end PTX.Kernels.TmlFa4Fwd.Protocol.Output
