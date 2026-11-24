-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderReadyGate
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReleaseSource
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderEmptyChronology
public import Lemmas.Order.DependencyWitness

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
open PTX PTX.AsyncCopy
open Thread.Loader (readyObject EmptyAcquire emptyObjectSlotEq
  earlierPublication guardedCopyBeforePublication GuardedReuse OrderedGuardedReuse
  AlternatesEmptyThrough emptyOrdinal)
open Thread.Mma (ReleaseForm ReleaseMatch)
open Thread.Mma.Observation (emptyObject)

/-- A loader reuse observes the actual notification through its successful empty wait,
then issues a group copy tracked by the new publication. -/
structure EmptyReuseWitness (X : Execution) (notify : Ref) (publication : EvId) where
  acquire : EvId
  copy : EvId
  observed : MbarObserved X notify (.thread acquire)
  guarded : Resumes kernel X acquire copy
  tracked : TracksCpAsync X copy publication

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- An MMA ready observation that enables the notification also enables any completed
publication reached through the loader's empty wait. -/
theorem EmptyReuseWitness.afterReady {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {ready publication : EvId} {notify : Ref}
    (h : EmptyReuseWitness X notify publication)
    (hReady : Relation.TransGen (DepStep l kernel X) (.thread ready, true) (notify, false))
    (hDone : X.async.arrived publication = true) :
    Relation.TransGen (DepStep l kernel X) (.thread ready, true)
      (.async publication .arriveOn, false) :=
  (hReady.tail (DepStep.of_witness l (Witness.of_mbarObserved h.observed))).trans
    (guardedCopyBeforePublication hX h.guarded h.tracked hDone)

/-- On the release issuer's lane, any successful acquisition up to the matched ordinal
precedes the reuse publication. -/
theorem EmptyReuseWitness.afterIssuerReady {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {publication : EvId} {g index wait parity : Nat} {rank : Fin 16}
    {form : ReleaseForm} {spec : TcCommit.Spec} {target : Loc}
    (h : EmptyReuseWitness X (.async (g, index) (.tcNotify rank)) publication)
    (hIssue : Thread.Mma.ReleaseIssue X g index form spec)
    (w : ReleaseMatch l X g index form target)
    (hPoll : Thread.Mma.ReadyPoll l X g wait w.slot parity true .cta)
    (hOrdinal : (Thread.Mma.atPrefix l X g wait).kvAcquires w.slot ≤
      (Thread.Mma.atPrefix l X g w.wait).kvAcquires w.slot)
    (hDone : X.async.arrived publication = true) :
    Relation.TransGen (DepStep l kernel X) (.thread (g, wait), true)
      (.async publication .arriveOn, false) := by
  have hIssueStage : DepStep l kernel X (.thread (g, index), false)
      (.async (g, index) (.tcNotify rank), false) := by
    exact DepStep.issue ⟨_, hIssue⟩ h.observed.1
      (by intro t ht; cases ht) (by intro e; cases e) (by intro e; cases e) (by intro e; cases e)
  refine h.afterReady hX ?_ hDone
  exact (Relation.TransGen.single (DepStep.of_resumes l
    (w.resumesOfEarlierReady hX hPoll hOrdinal))).tail hIssueStage

/-- Matching the notifications observed by the loader's guarded reuses with the ready
observation supplies the cross-warp reuse gate for the ready-object history. -/
theorem causalReuseOfEmptyWitnesses {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {ready : EvId} {slot : Fin 3} {phase : Nat}
    (hWitness : ∀ publication, X.AsyncArrive publication (readyObject l ready.1 slot) true →
      X.async.arrived publication = true → phase < generation l X publication slot →
      ∃ notify : Ref, Nonempty (EmptyReuseWitness X notify publication) ∧
        Relation.TransGen (DepStep l kernel X) (.thread ready, true) (notify, false)) :
    CausalReuse l X ready slot phase := by
  intro publication hPub hDone hGeneration
  obtain ⟨_, ⟨h⟩, hReady⟩ := hWitness publication hPub hDone hGeneration
  exact h.afterReady hX hReady hDone

/-- The first reuse in a producer suffices. Its guarded copy is also tracked by each
subsequent publication of that producer, even if the first reuse has not completed. -/
theorem causalReuseOfNextWitness (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {ready : EvId} {slot : Fin 3} {phase : Nat}
    (hNext : ∀ next, X.AsyncArrive next (readyObject l ready.1 slot) true →
      generation l X next slot = phase + 1 →
      ∃ notify : Ref, Nonempty (EmptyReuseWitness X notify next) ∧
        Relation.TransGen (DepStep l kernel X) (.thread ready, true) (notify, false)) :
    CausalReuse l X ready slot phase := by
  apply causalReuseOfEmptyWitnesses hX
  intro publication hPub _ hLater
  by_cases hSame : generation l X publication slot = phase + 1
  · exact hNext publication hPub hSame
  have hBefore : phase + 1 < generation l X publication slot := by omega
  obtain ⟨i, hI, hPub', hFirst⟩ := earlierPublication hp hX hPub hBefore
  let next := (publication.1, i)
  obtain ⟨notify, ⟨h⟩, hReady⟩ := hNext next hPub' hFirst
  have hTrack : TracksCpAsync X h.copy publication :=
    ⟨h.tracked.1, lt_trans h.tracked.2.1 hI, h.tracked.2.2.1, _, true, hPub⟩
  exact ⟨notify, ⟨⟨h.acquire, h.copy, h.observed, h.guarded, hTrack⟩⟩, hReady⟩

end PTX.Kernels.TmlFa4Fwd.Protocol.LoaderReady
