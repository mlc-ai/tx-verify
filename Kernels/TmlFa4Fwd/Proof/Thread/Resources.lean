-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.MmaResources
public import Kernels.TmlFa4Fwd.Proof.Thread.Exit
public import Lemmas.Tmem.TmemPairRecord
public import Core.Assembly.SharedLifetime

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX

/-- Exit observations of the lane machines account for their CTA's exits. -/
theorem ctaExited {l : Launch} {m : Mem0} {X : Execution} {owner : Nat}
    (hX : Consistent l kernel Assumptions.all m X)
    (hExit : ∀ g < l.threads, Exited X g) : CtaExited l X owner :=
  fun g hg _ => (hExit g hg).lastEvent hX hg

/-- A single-CTA allocator record completes its warp's request as soon as it is performed. -/
theorem allocatorRecordSingle {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {cta : Nat} {r : Tmem.Pair.Requests} (hr : r ∈ X.tmemHistory cta) :
    r.group = .one :=
  (Mma.actualResourceRequest hX (((hX.tmemPair.1 cta).1 r hr).2.2.2.2.1 0)).1

/-- If a thread exited, its allocator requests have all completed. -/
theorem resourceReturnedBeforeExit {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {i : EvId} {g : CtaGroup}
    {dst : Option Loc} {request : Tmem.Request}
    (he : ∃ e, X.get i = some e ∧ e.kind = .tc (.resource g dst request))
    (hExit : Exited X i.1) : Tmem.Pair.Covered l X i := by
  obtain ⟨⟨_, _⟩, he, rfl⟩ := he
  obtain ⟨last, hLast, hKind⟩ :=
    hExit.last hX (Step.CtaBar.thread_lt_of_get hX he)
  have hN := (List.getElem?_eq_some_iff.mp he).1
  have hPrev : i.2 + 1 < (X.tr i.1).length := by
    by_contra! h
    rw [List.getLast?_eq_getElem?, show (X.tr i.1).length - 1 = i.2 by omega] at hLast
    have hLastGet : X.get i = some last := hLast
    rw [← (Option.some.inj (he.symm.trans hLastGet))] at hKind
    cases hKind
  obtain ⟨cta, r, hr, hLane⟩ := hX.tmemPairBlocking.performed he hPrev
  exact ⟨[r.own], .inl ⟨cta, r, hr, allocatorRecordSingle hX hr, rfl⟩,
    r.own, List.mem_singleton_self _, hLane⟩

end PTX.Kernels.TmlFa4Fwd.Thread
