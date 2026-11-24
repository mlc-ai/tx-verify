-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.Mma
public import Kernels.TmlFa4Fwd.Proof.MmaInitialReadyRelease
public import Kernels.TmlFa4Fwd.Proof.MmaReadyHistory

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX PTX.MBarrier PTX.MbarRing PTX.AsyncCopy
open Observation (readyObject emptyObject)

noncomputable section

/-- A successful poll of a ready slot, with its requested parity and scope. -/
def ReadyPoll (l : Launch) (X : Execution) (g index : Nat) (slot : Fin 3)
    (parity : Nat) (acquire : Bool) (scope : MbarScope) : Prop :=
  ∃ e, X.get (g, index) = some e ∧
    e.kind = .wait (readyObject l g slot) parity true acquire scope

/-- The pipeline's initial K release. The thread proof recognizes its decoded issue. -/
def InitialRelease (X : Execution) (g index : Nat) (spec : TcCommit.Spec) : Prop :=
  X.get (g, index) = some ⟨2274, .tc (.commit spec)⟩

/-- A successful ready poll updates the slot's abstract ordinal and parity. -/
theorem ReadyPoll.step {l : Launch} {X : Execution} {g index parity : Nat} {slot : Fin 3}
    {acquire : Bool} {scope : MbarScope}
    (h : ReadyPoll l X g index slot parity acquire scope) :
    (atPrefix l X g (index + 1)).kvAcquires slot =
      (atPrefix l X g index).kvAcquires slot + 1 ∧
    (atPrefix l X g (index + 1)).latestKvParity slot = some parity := by
  obtain ⟨⟨pc, kind⟩, he, hk⟩ := h
  dsimp only at hk
  subst kind
  exact (readyAcquireStep (i := slot) he).2

/-- An observed ready poll changes only its own slot's counted successful polls. -/
theorem ReadyPoll.stepSlots {l : Launch} {X : Execution} {g index parity : Nat} {slot : Fin 3}
    {acquire : Bool} {scope : MbarScope}
    (h : ReadyPoll l X g index slot parity acquire scope) (i : Fin 3) :
    (atPrefix l X g (index + 1)).kvAcquires i =
      (atPrefix l X g index).kvAcquires i + if slot = i then 1 else 0 := by
  obtain ⟨⟨pc, kind⟩, he, hk⟩ := h
  dsimp only at hk
  subst kind
  have hLoc : readyObject l g slot = readyObject l g i ↔ slot = i := by
    refine ⟨fun h => ?_, fun h => congrArg (readyObject l g) h⟩
    by_contra hBad
    have hSlot : Loader.readySlot slot ≠ Loader.readySlot i := by
      intro heq
      apply hBad
      have hv := congrArg Fin.val heq
      change 4 + slot.val = 4 + i.val at hv
      exact Fin.ext (by omega)
    exact Prologue.initObject_ne hSlot h
  rw [prefixStep he]
  simp [advance, Observation.tick, Flow.okPoll, sourceWaitSuccess, hLoc]

/-- A completed release identifies the empty object and the successful ready poll in its past. -/
theorem InitialRelease.notification {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} {spec : TcCommit.Spec} {rank : Fin 16} {loc : Loc} {r : Record Ref}
    (he : InitialRelease X g index spec) (hTarget : TcCommit.target spec rank = some loc)
    (hr : r ∈ X.objects loc) (hId : r.id = .async (g, index) (.tcNotify rank)) :
    loc = emptyObject l g 0 ∧ 0 < (atPrefix l X g index).kvAcquires 0 ∧
      ∃ j < index, ReadyPoll l X g j 0 0 true .cta ∧
        Relation.TransGen (DepStep l kernel X) (.thread (g, j), true) (r.id, false) := by
  obtain ⟨hLoc, j, hj, hGet, hDep⟩ :=
    PTX.Kernels.TmlFa4Fwd.Mma.initialReadyBeforeEmptyNotification hp hX he hTarget hr hId
  exact ⟨hLoc, initialReleaseGuard hp hX he, j, hj, ⟨_, hGet, rfl⟩, hDep⟩

/-- Each actual successful ready poll has a clean object record and a successful reply. -/
theorem ReadyPoll.record {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index parity : Nat} {slot : Fin 3} {acquire : Bool} {scope : MbarScope}
    (h : ReadyPoll l X g index slot parity acquire scope) :
    ∃ (j : Nat) (r : Record Ref), (X.objects (readyObject l g slot))[j]? = some r ∧
      r.id = .thread (g, index) ∧ r.fault = none ∧ r.reply.waited = some true := by
  obtain ⟨⟨pc, kind⟩, he, hk⟩ := h
  dsimp only at hk
  subst kind
  obtain ⟨j, r, hj, hi, _, hf, hReply⟩ := actualPollRecordClean hp hX he
  exact ⟨j, r, hj, hi, hf, hReply⟩

/-- The ready history observes the abstract ordinal under parity alternation and causal reuse. -/
theorem ReadyPoll.generationOfReuse {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index parity : Nat} {slot : Fin 3} (h : ReadyPoll l X g index slot parity true .cta)
    (hAlt : ∀ j q acquire scope, ReadyPoll l X g j slot q acquire scope →
      q % 2 = (atPrefix l X g j).kvAcquires slot % 2)
    (hReuse : ∀ issue, X.AsyncArrive issue (readyObject l g slot) true →
      X.async.arrived issue = true →
      (atPrefix l X g index).kvAcquires slot < Loader.readyOrdinal X (readyObject l g slot) issue →
      Relation.TransGen (DepStep l kernel X) (.thread (g, index), true)
        (.async issue .arriveOn, false)) :
    ∃ (j : Nat) (r : Record Ref), (X.objects (readyObject l g slot))[j]? = some r ∧
      r.id = .thread (g, index) ∧ r.reply.waited = some true ∧
      observedAt (X.objects (readyObject l g slot)) j =
        some ((atPrefix l X g index).kvAcquires slot) := by
  obtain ⟨⟨pc, kind⟩, he, hk⟩ := h
  dsimp only at hk
  subst kind
  have ordinal (j : Nat) : (atPrefix l X g j).kvAcquires slot =
      Flow.okPolls (readyObject l g slot) ((X.tr g).take j) :=
    kvAcquireCount l g _ slot
  rw [ordinal]
  exact Loader.readyGenerationOfLaneReuse hp hX slot he
    (fun j _ q acquire scope hGet => by
      change q % 2 = Flow.okPolls (readyObject l g slot) ((X.tr g).take j) % 2
      rw [← ordinal]
      exact hAlt j q acquire scope ⟨_, hGet, rfl⟩)
    (fun issue hi hd hu => hReuse issue hi hd (by rw [ordinal]; exact hu))

end
end PTX.Kernels.TmlFa4Fwd.Thread.Mma
