-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.Sites
public import Kernels.FlashKdaFwd.Proof.Ref.Startup.Tracked

@[expose] public section

/-!
# Tracking: the machine follows every thread; where a thread's machine can stop

**Words.** The machine of thread `g` *follows* the thread up to position `k` when
`Frame.stateAt (code L) X g k = some (some s)` (`At (code L) X g k s`: a *followed state*). It
has *given up* when the value is `some none` (the machine declines to describe the thread
further) and the thread is *dead* when the value is `none` (the machine's successor along an
event was `none`: the event leads to a faulted state whose next event is undefined behaviour,
or the event was the thread's `ret`).

* `later : Startup.Later P L X` — what the startup phase asked of the later phases
  (`Ref/Startup/Shfl.lean`): a followed state of a thread that has left the startup phase is at
  no site of the startup phase. From `stage_any` and the instruction ranges of `Sites.lean`:
  a state at a startup site is at an instruction up to 384, so it is in the startup stage,
  and a thread in the startup stage has not left it (`Startup.Inv.not_left`).
* `tracked : Frame.Tracked (code L) X` — **no machine gives up**, for every consistent
  execution under the precondition (`Startup.tracked` with `later`). `shflWarp` is the
  startup's complete statement about shuffles, for the record.
* `followed_event`: an event that is not undefined behaviour fires from a followed state
  (`Frame.event_state` with `tracked`); `event_stage`: that state is in a stage, and the
  guard `NoUb` holds at it. This is the entry point for a contract field about an event.
* `dead_cases`: **where a thread can die.** If the machine's successor along an event of a
  launched thread, from a followed state, is `none` and the event is not the thread's `ret`,
  then the state is in the Conversion, the CarryLoad, the Compute or the Store phase. In the
  startup phase, the Producer phase and the epilogue every successor is a state
  (`Startup.inv_next`, `Producer.producer_followed`, `Epilogue.step_at`). In the four phases
  named, a dead successor is excluded by a *data condition* that the value layer proves (the
  bytes a load returned rebuild to a value, a value converts; `Conversion.conversion_ok`,
  `CarryLoad.carry_ok`, the Compute phase's and `Store.next_at`'s conditions).
* `Alive L X`: no event of a launched thread other than its `ret` leads from a followed state
  to a dead one. `followed`: **under `Alive`, every position of a launched thread up to the
  end of its trace has a followed state**, unless the thread has exited before it. This is
  the form of "no event leads to a dead or given-up state" that can be proved in the reference
  layer: without `Alive` it is false for an execution in which a load returns bytes that do
  not rebuild (the value layer excludes such executions, the reference layer cannot).
  `alive_of`: `Alive` from the four phases' share, in the shape of `dead_cases`.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- A thread that has left the startup phase at or before a position has left it at or before
the end of its trace: positions beyond the trace have the state and the ledger of the last
one. -/
theorem left_min {k : Nat} (h : Startup.Left P L X g k) :
    Startup.Left P L X g (min k (X.tr g).length) := by
  obtain ⟨j, hj, s0, hσ0, ho⟩ := h
  rcases Nat.le_total j (X.tr g).length with hjl | hjl
  · exact ⟨j, Nat.le_min.mpr ⟨hj, hjl⟩, s0, hσ0, ho⟩
  · refine ⟨(X.tr g).length, Nat.le_min.mpr ⟨by omega, le_rfl⟩, s0, ?_, ho.1, ?_⟩
    · rw [← Frame.stateAt_of_le hjl]
      exact hσ0
    · have h2 := ho.2
      rwa [List.take_of_length_le hjl, ← List.take_length (l := X.tr g)] at h2

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
include hpre hX

/-- **A followed state of a thread that has left the startup phase is at no site of the
startup phase**: what the startup phase asked of the later phases. -/
theorem later : Startup.Later P L X := by
  intro g k s hg hleft hσ pos hsite
  have hst := stage_any hpre hX hg hσ
  have hpc : s.site.pc ≤ 384 := by
    rw [hsite]
    exact startup_pos_pc pos
  exact (hst.of_pc_startup (by omega)).inv.not_left (left_min hleft)

/-- **Every launched thread is followed by its machine**: no machine gives up, in any
consistent execution under the precondition. -/
theorem tracked : Frame.Tracked (code L) X :=
  Startup.tracked hpre hX (later hpre hX)

/-- Every shuffle of a launched thread returned a value whose word is the thread's warp
index. -/
theorem shflWarp : ∀ g < L.threads, Startup.ShflWarp X g :=
  Startup.shflWarp hpre hX (later hpre hX)

/-- **An event that is not undefined behaviour fires from a followed state.** -/
theorem followed_event {k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩) : ∃ s, At (code L) X g k s :=
  Frame.event_state (sounds hpre) hX (tracked hpre hX) he hub

/-- **An event that is not undefined behaviour fires from a followed state, which is in a
stage**, and no undefined-behaviour event precedes it (so the guards of the Store phase's and
the epilogue's invariant hold). The event's thread is launched (`Frame.lt_of_get hX he`). -/
theorem event_stage {k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hne : ∀ f, e.kind ≠ .ub f) :
    ∃ s, At (code L) X g k s ∧ Stage P L X g k s ∧ NoUb X g k := by
  obtain ⟨s, hσ⟩ := followed_event hpre hX he fun pc f h => hne f (by rw [h])
  obtain ⟨hst, hub⟩ := stage_event hpre hX (Frame.lt_of_get hX he) he hσ
  exact ⟨s, hσ, hst, hub⟩

/-- **Where a thread can die**: if the machine's successor along an event of a launched
thread, from a followed state, is dead, and the event is not the thread's `ret`, then the
state is in the Conversion, the CarryLoad, the Compute or the Store phase (where a data
condition of the value layer excludes it). -/
theorem dead_cases (hg : g < L.threads) {k : Nat} {s : D} {e : Event}
    (he : X.get (g, k) = some e) (hσ : At (code L) X g k s)
    (hn : Thread.next L g s e = none) (hx : ∀ pc, e ≠ ⟨pc, .exit⟩) :
    (∃ j0, Conversion.Inv P X g j0 k s) ∨ (∃ j0, CarryLoad.Inv P X g j0 k s) ∨
      (tid g < 128 ∧ ∃ j0, Compute.Inv P L X g j0 k s) ∨
      (warp g = 5 ∧ Store.Inv P X g k s) := by
  obtain ⟨hst, hub⟩ := stage_event hpre hX hg he hσ
  cases hst with
  | startup hI =>
    obtain ⟨s', hσ', -⟩ := Startup.inv_next hpre hX hg he hσ hI
    rw [Frame.stateAt_succ he, hσ] at hσ'
    have hn' : Thread.next L g s e = some (some s') := hσ'
    rw [hn] at hn'
    cases hn'
  | conversion _ _ hI => exact .inl ⟨_, hI⟩
  | carryLoad _ _ hI => exact .inr (.inl ⟨_, hI⟩)
  | compute hr _ _ _ hI => exact .inr (.inr (.inl ⟨hr, _, hI⟩))
  | producer hr _ _ _ hI =>
    obtain ⟨s', hn'⟩ := Producer.producer_followed hpre hX hg hr he hσ hI
    rw [hn] at hn'
    cases hn'
  | store hr _ _ _ hI _ => exact .inr (.inr (.inr ⟨hr, hI hub⟩))
  | epilogue _ _ _ hI =>
    exfalso
    obtain ⟨pos, hr, -⟩ := hI hub
    obtain ⟨site, w, p, x⟩ := s
    obtain rfl : site = pos.site := hr.site
    obtain ⟨t, ins, o, hat, -, hc, hf⟩ := Frame.fired_site (sounds hpre) hX he hσ
    obtain ⟨hev, hnx⟩ := Epilogue.step_at hpre hg pos hr hat hc hf
    by_cases hne : pos = .exit
    · subst hne
      have hev' : e = ⟨3835, .exit⟩ := hev
      exact hx 3835 hev'
    · obtain ⟨d', hd, -⟩ := hnx hne
      rw [hn] at hd
      cases hd

end

/-- **No thread dies**: no event of a launched thread other than its `ret` leads from a
followed state to a dead state. The reference layer proves this for the startup phase, the
Producer phase and the epilogue (`dead_cases`); for the other four phases it is the value
layer's data conditions. -/
def Alive (L : Launch) (X : Execution) : Prop :=
  ∀ g k s e, g < L.threads → X.get (g, k) = some e → At (code L) X g k s →
    (∀ pc, e ≠ ⟨pc, .exit⟩) → Thread.next L g s e ≠ none

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
include hpre hX

/-- **`Alive` from the four phases with a data condition**: it is enough that the successor
along an event is not dead at the states of the Conversion, the CarryLoad, the Compute and the
Store phase. -/
theorem alive_of
    (h : ∀ g k s e, g < L.threads → X.get (g, k) = some e → At (code L) X g k s →
      ((∃ j0, Conversion.Inv P X g j0 k s) ∨ (∃ j0, CarryLoad.Inv P X g j0 k s) ∨
        (tid g < 128 ∧ ∃ j0, Compute.Inv P L X g j0 k s) ∨
        (warp g = 5 ∧ Store.Inv P X g k s)) → Thread.next L g s e ≠ none) :
    Alive L X :=
  fun g k s e hg he hσ hx hn => h g k s e hg he hσ (dead_cases hpre hX hg he hσ hn hx) hn

/-- **Every position of a launched thread has a followed state**, up to the end of its
trace, when no thread dies (`Alive`) and the thread has not exited before the position. -/
theorem followed (ha : Alive L X) (hg : g < L.threads) {k : Nat}
    (hk : k ≤ (X.tr g).length) (hx : ∀ i pc, i < k → X.get (g, i) ≠ some ⟨pc, .exit⟩) :
    ∃ s, At (code L) X g k s := by
  induction k with
  | zero => exact ⟨_, at_zero⟩
  | succ k ih =>
    obtain ⟨s, hs⟩ := ih (by omega) fun i pc hi => hx i pc (by omega)
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hne : ∀ pc, e ≠ ⟨pc, .exit⟩ := fun pc h => hx k pc (Nat.lt_succ_self k) (h ▸ he)
    have hsucc : Frame.stateAt (code L) X g (k + 1) = Thread.next L g s e := by
      rw [Frame.stateAt_succ he, hs]
      rfl
    cases hnext : Thread.next L g s e with
    | none => exact absurd hnext (ha g k s e hg he hs hne)
    | some σ =>
      cases σ with
      | none =>
        rw [hnext] at hsucc
        exact absurd hsucc (tracked hpre hX g (k + 1) hg)
      | some s' =>
        rw [hnext] at hsucc
        exact ⟨s', hsucc⟩

end

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
