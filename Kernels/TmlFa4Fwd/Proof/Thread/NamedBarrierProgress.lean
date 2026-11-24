-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.NamedBarrierSemantics
public import Lemmas.Step.CtaBarFinishExit

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX NamedBar

/-- Record and release an observed sync once all of its participant lanes have arrived. -/
theorem releaseSynchronization {l : Launch} {m : Mem0} {X : Execution}
    (hMax : Maximal l kernel Assumptions.all m X)
    (hFault : ∀ Y, Consistent l kernel Assumptions.all m Y → Y.tr = X.tr →
      Y.MemWrites = X.MemWrites → ¬ CtaBarFault l Y)
    {members : Finset Nat} {id : Nat} {count : Option Nat} {g : Nat} (hg : g < l.threads)
    (hShape : Shape l count members id) (hSources : Sources l X count members id)
    (hWait : BarrierArrival X (g,(X.tr g).length - 1) id count .sync)
    (hArrivals : ∀ lane < l.block, lane / 32 ∈ members →
      observedBarrierOrdinal X (g,(X.tr g).length - 1) id <
        (X.tr (g / l.block * l.block + lane)).countP (Execution.isBarId id)) :
    ∃ Y, Maximal l kernel Assumptions.all m Y ∧ Y.tr = X.tr ∧
      Y.MemWrites = X.MemWrites ∧ Step.Released l Y g := by
  obtain ⟨⟨site, kind⟩, hGet, hKind⟩ := hWait
  change kind = _ at hKind
  subst kind
  refine sync_release_preserving_writes hMax Assumptions.wfStep.ctaHistory hFault hShape hSources
    hg hGet ?_
  intro lane hLane hMember
  let thread := g / l.block * l.block + lane
  obtain ⟨pos, event, hEvent, hId, hOrdinal⟩ :=
    exists_ordinal (Execution.isBarId id) (X.tr thread) (hArrivals lane hLane hMember)
  obtain ⟨source, operand, mode, rfl⟩ := isBarId_form hId
  have hCount := (hSources (thread, pos) source operand ⟨mode, hEvent⟩
    (cta_thread_lt (cta_lt hg) hLane)).2
  subst operand
  exact ⟨pos, source, mode, hEvent, hOrdinal⟩

end PTX.Kernels.TmlFa4Fwd.Thread
