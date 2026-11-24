-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.SharedLifetime
public import Lemmas.Kernel.Safety.Classes

@[expose] public section

/-! # Shared-memory lifetime from the own-CTA frame

A proof skeleton, generic over the kernel, for ERR-SHARED-LIFETIME (`SharedLifetimeUnsafe`) in a
kernel whose CTAs use only their own shared memory. The check has two arms:

* a use of another CTA's shared memory not preceded by an instruction of the owner: empty when
  every use is of the issuer's own CTA (`hown`, the kernel's frame: the shapes' footprints and
  objects in shared memory are of the thread's CTA, `RoleTable.intent_at`,
  `RoleTable.mbar_frame`);
* a use not finished before an exit of the owner CTA, once the CTA has exited: a thread
  instruction that uses shared memory is no exit, so it is before its own thread's exit in program
  order (`SharedFinished.of_thread`, done here for every thread use: an access, an mbarrier
  operation, a commit); an asynchronous use is finished by its completion chain, which is the
  kernel's (`hasync`: `SharedFinished.of_observer_exit`, `of_stage`, `of_caused` of
  `Lemmas/Kernel/ExitChain.lean`). -/

namespace PTX

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- **A thread instruction that uses shared memory is no exit.** -/
theorem sharedUse_thread_event {e : EvId} {c : Nat} (h : SharedUse L X (.thread e) c) :
    ∃ ev, X.get e = some ev ∧ ∀ pc, ev ≠ ⟨pc, .exit⟩ := by
  rcases h with ⟨-, ⟨a, w, hi, -⟩ | ⟨addr, act, ho⟩⟩ | ⟨i, s, he, ⟨pc, hc⟩, -⟩ | ⟨_, _, _, _, _, _,
      he, -⟩ | ⟨_, _, _, he, -⟩ | ⟨_, _, he, -⟩
  · rcases hi with ⟨bs, ⟨pc, he⟩, -⟩ | ⟨bs, ⟨pc, he⟩, -⟩ | ⟨old, new, pc, he⟩
    all_goals exact ⟨_, he, fun _ h => by cases h⟩
  · exact objectAction_thread ho
  · cases he
    exact ⟨_, hc, fun _ h => by cases h⟩
  · cases he
  · cases he
  · cases he

/-- **ERR-SHARED-LIFETIME for own-CTA shared memory**: every use is of the issuer's CTA, and every
asynchronous use is finished once its CTA has exited; thread uses are finished by program
order. -/
theorem noSharedLifetime_of_own (hX : Consistent L K A mem0 X)
    (hown : ∀ e c, SharedUse L X e c → c = e.issuer.1 / L.block)
    (hasync : ∀ i p c, SharedUse L X (.async i p) c → CtaExited L X c →
      SharedFinished L K A X (.async i p) c) :
    ¬ SharedLifetimeUnsafe L K A X := by
  rintro ⟨e, c, hu, (⟨hne, -⟩ | ⟨hx, hnf⟩)⟩
  · exact hne (hown e c hu)
  · rcases e with i | ⟨i, p⟩
    · obtain ⟨ev, he, hne⟩ := sharedUse_thread_event hu
      have hc := hown _ c hu
      exact hnf (SharedFinished.of_thread (fun g hg => hX.outside g hg) he hne hc.symm hx)
    · exact hnf (hasync i p c hu hx)

end

end PTX
