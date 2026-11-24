-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderReadyGate
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReleaseCapacity

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.AsyncCopy PTX.MBarrier PTX.MbarRing

namespace Loader
open Mma.Observation (emptyObject)

/-- The history observation of an empty acquire belongs to its own initialized slot. -/
theorem EmptyAcquire.observedInSlot {l : Launch} {X : Execution}
    {wait : EvId} {slot : Fin 3} {parity : Nat} {notify : Ref}
    (h : EmptyAcquire l X wait slot parity) (hObserved : MbarObserved X notify (.thread wait)) :
    MBarrier.UpdateBeforeWait (X.objects (emptyObject l wait.1 slot)) notify (.thread wait) := by
  obtain ⟨_, j, loc, _, _, hj, ⟨⟨_, _, hEmpty⟩, hUpdate⟩, _⟩ := hObserved
  have hj' : j = wait := Ref.thread.inj hj.symm
  subst j
  obtain ⟨ev, he, hk⟩ := h
  rw [← Option.some.inj (hEmpty.symm.trans he)] at hk
  obtain rfl : loc = emptyObject l wait.1 slot := (Kind.wait.inj hk).1
  exact hUpdate

end Loader

namespace Mma
open Observation (emptyObject)

/-- On one empty slot a release ordinal identifies at most one raw history record. -/
theorem EmptyReleaseAt.position_eq_of_ordinal_eq {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {owner g h k k' : Nat} {slot : Fin 3}
    (a : EmptyReleaseAt l X (emptyObject l owner slot) g k)
    (b : EmptyReleaseAt l X (emptyObject l owner slot) h k')
    (hOrdinal : a.ordinal = b.ordinal) : k = k' := by
  have hIssue := a.issue_eq_of_ordinal_eq hp hX b rfl hOrdinal
  obtain ⟨hIssuer, hIndex⟩ := Prod.mk.inj hIssue
  subst h
  have hSpec : a.spec = b.spec := by
    have ha := a.issue
    have hb := b.issue
    unfold ReleaseIssue at ha hb
    rw [hIndex] at ha
    have he := congrArg Event.kind (Option.some.inj (ha.symm.trans hb))
    exact TcKind.commit.inj (Kind.tc.inj he)
  have hRank := MbarRing.Notify.rank_eq a.target (hSpec ▸ b.target)
  apply ObjectInit.checked_record_index_eq (X.objects_checked hX _) a.atIndex b.atIndex
  rw [a.notification, b.notification, hIndex, hRank]

end Mma
end PTX.Kernels.TmlFa4Fwd.Thread
