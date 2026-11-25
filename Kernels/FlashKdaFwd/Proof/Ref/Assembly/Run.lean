-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Chain
public import Kernels.FlashKdaFwd.Proof.Ref.Startup.Progress
public import Kernels.FlashKdaFwd.Proof.Ref.Conversion.Trace
public import Kernels.FlashKdaFwd.Proof.Ref.CarryLoad.Links
public import Kernels.FlashKdaFwd.Proof.Ref.Producer.Exports
public import Kernels.FlashKdaFwd.Proof.Ref.Compute.Trace
public import Kernels.FlashKdaFwd.Proof.Ref.Store.Trace
public import Kernels.FlashKdaFwd.Proof.Ref.Epilogue.Trace
public import Kernels.FlashKdaFwd.Proof.Ref.Epilogue.Links

@[expose] public section

/-!
# The chain: the phases of a thread's run, joined

The reference layer describes the run of a thread phase by phase: the startup (instructions 0
to 386), the conversion loop (387 to 621), the carry loads (622 to 1401), one of the three tile
loops by the thread's role (the compute threads' 2106 to 2944, the load warp's 1403 to 2105,
the store warp's 2945 to 3112; all three start at the `bar.sync 0` of instruction 1402 and end
before the one of instruction 3113), and the epilogue (3113 to 3835). This file joins the seven
theorems into one, in the vocabulary of `Ref/Chain.lean`.

**Words.** A *followed state* of thread `g` at position `k` is the state `s` of the thread's
machine before the thread's `k`-th event (`At (code L) X g k s`); position `(X.tr g).length` is
the state after the thread's last event. A *phase* (`Ref.Phase`) is an entry condition
`In k s`, an invariant `Inv k0 k s` (`k0` is the *entry index*: the position at which the entry
condition held) and an exit condition `Out k0 k s`. The *role* of a thread is decided by its
index `tid g` in its thread block: a *compute thread* has `tid g < 128`, the *load warp* is
`warp g = 4` and the *store warp* is `warp g = 5`. A *ledger* is a phase's count of the thread's
earlier events by class. *Undefined behaviour* is an event of kind `.ub`; it is a thread's last
event.

## The generic part

* `NoUb X g k`: none of the first `k` events of thread `g` is undefined behaviour. It holds at
  every position before an event (`noUb_of_lt`), so it is a condition on the state after the
  thread's last event only: that last event is not undefined behaviour.
* `Phase.Runs` is `Phase.Traces` of `Ref/Chain.lean` without the hypothesis that an event
  follows the state (`k ≤ (X.tr g).length` in place of `k < …`): it also speaks of the state
  after the thread's last event, which is the state the progress argument looks at.
* `Runs.of_step` turns a phase's step lemma ("from a followed state with the invariant, the
  successor state has the invariant or is the exit") into `Runs`. Some phases prove their step
  only for an event that is not undefined behaviour (an undefined-behaviour event at one of
  their sites is in no class of the ledger, so the ledger of the successor position is wrong):
  `Runs.of_step_noUb` gives `Runs` for the *guarded* phase `Φ.guard W X`, whose invariant is
  `W k0 k s ∧ (NoUb X g k → Φ.Inv k0 k s)` for a *weak invariant* `W` that every successor of
  a state of the invariant has, whatever the event.
* `Runs.first`, `Runs.seq`, `Runs.run` are the three lemmas of `Ref/Chain.lean` for `Runs`.
* `Phase.after Φ H X` is the phase `Φ` entered with a *history* `H` (a fact about the entry
  position and state that the earlier phases proved): its entry condition is `H`, and its exit
  condition keeps `H` at the entry index. This is how the exit of a phase carries what the
  phases before it proved, which the link lemmas at the site `bar_5` need.

## The phases

| phase | `Phase` | `Runs` | from |
|---|---|---|---|
| startup | `startupPhase` | `startup_runs` | `Startup.startup_invE_le` |
| conversion | `Conversion.phase` | `conversion_runs` | `Conversion.inv_step` |
| carry loads | `CarryLoad.phase` | `carryLoad_runs` | `CarryLoad.inv_next` |
| compute loop | `Compute.phase` | `compute_runs` | `Compute.good` |
| load loop | `producerPhase` | `producer_runs` | `Producer.inv_step` |
| store loop | `storePhase` | `store_runs` | `Store.inv_step`, `Store.step_at` |
| epilogue | `epiloguePhase` | `epilogue_runs` | `Epilogue.epilogue_weak`, `inv_step` |

The Store phase and the epilogue are the two phases with a guarded invariant. Their weak
invariants, which hold at every followed state: `StoreWeak` (the state is at a position of the
Store phase with the position's registers, or it is the phase's exit state) and
`Epilogue.InvW` (position, registers, ordinal, number of `bar.sync 0`).

## The history records

`StartupDone`, `ConversionDone`, `CarryLoadDone`, `TileDone` (`… P L X g j s`): the thread
left the named phase at position `j` in the followed state `s`, with the phase's exit
condition there, the invariant of the phase at every position from its entry up to `j`, and
the record of the phase before at the entry. Each is the entry condition of the next phase in
the chain, so a state in a phase comes with everything the earlier phases proved (counts of
events that the current phase does not make are known at these exits).

## The links

"The exit of a phase gives the entry of the next at the same followed state": startup to
conversion and conversion to carry loads are the definitions (`Conversion.In` is
`Startup.Out`, `CarryLoad.In` is `Conversion.Out`); carry loads to the three tile loops are
`compute_in`, `producer_entered`, `store_in` below, which are the lemmas of the same names of
`Ref/CarryLoad/Links.lean` applied to the history `CarryLoadDone` (they need the first exit of
the startup: the counts per mbarrier are known there); the three tile loops to the epilogue
are `Epilogue.in_of_compute`, `in_of_producer`, `in_of_store` (`Ref/Epilogue/Links.lean`).

## The chain

`chain P L X g T` for a tile-loop phase `T`: startup, conversion, carry loads, `T`, epilogue,
each entered at the FIRST exit of the one before it (`Phase.first`) with the history record of
that exit (`Phase.after`); `chain_runs` is its theorem. `computeChain`, `loadChain`,
`storeChain` are the three instances and `compute_chain`, `load_chain`, `store_chain` their
theorems. `Stage.lean` reads them as one case principle.

## Hypotheses

Everything here is proved from the precondition `Pre P L mem0`, consistency of the execution
and `g < L.threads` (the machine's soundness is `Thread.sound`); no phase's premise is left.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref
open PTX

/-! ### A phase's theorem at every followed state -/

section Generic
variable {K : Kernel} {A : List Assumption} {L : Launch} {C : (g : Nat) → Flow.Code K A L g}
  {X : Execution} {g : Nat}

/-- **None of the first `k` events of thread `g` is undefined behaviour.** -/
def NoUb (X : Execution) (g k : Nat) : Prop :=
  ∀ i < k, ∀ pc f, X.get (g, i) ≠ some ⟨pc, .ub f⟩

theorem NoUb.mono {j k : Nat} (h : NoUb X g k) (hjk : j ≤ k) : NoUb X g j :=
  fun i hi => h i (by omega)

/-- An undefined-behaviour event is a thread's last: none precedes a position that an event
follows. -/
theorem noUb_of_lt {mem0 : Mem0} (hX : Consistent L K A mem0 X) {k : Nat}
    (hk : k < (X.tr g).length) : NoUb X g k := by
  intro i hi pc f he
  obtain ⟨e', he'⟩ : ∃ e', (X.tr g)[k]? = some e' := ⟨_, List.getElem?_eq_getElem hk⟩
  have := ub_last hX he he'
  omega

/-- An execution without undefined behaviour has none before any position. -/
theorem noUb_of_not_hasUb (h : ¬ HasUb X) (k : Nat) : NoUb X g k :=
  fun i _ pc f he => h ⟨(g, i), pc, f, he⟩

/-- **The theorem of a phase at every followed state**, the one after the thread's last event
included: from the entry condition at a followed state at `k0`, every later followed state
satisfies the invariant, or the exit condition held at a followed state between the entry and
it. -/
def Phase.Runs (Φ : Phase C g) (X : Execution) : Prop :=
  ∀ k0 s0 k s, At C X g k0 s0 → Φ.In k0 s0 → k0 ≤ k → k ≤ (X.tr g).length → At C X g k s →
    Φ.Inv k0 k s ∨ ∃ j s1, k0 ≤ j ∧ j ≤ k ∧ At C X g j s1 ∧ Φ.Out k0 j s1

/-- The form of `Ref/Chain.lean` (states before an event) is a special case. -/
theorem Phase.Runs.traces {Φ : Phase C g} (h : Φ.Runs X) : Φ.Traces X :=
  fun k0 s0 k s h0 hin hk0 hk hs => h k0 s0 k s h0 hin hk0 (Nat.le_of_lt hk) hs

/-- **A phase whose invariant is asked only when no undefined-behaviour event precedes the
position**, with a *weak invariant* `W` that holds at every position. Before an event the guard
holds (`noUb_of_lt`); at the state after the thread's last event it says that this event is not
undefined behaviour. -/
def Phase.guard (Φ : Phase C g) (W : Nat → Nat → (C g).D → Prop) (X : Execution) :
    Phase C g where
  In := Φ.In
  Inv k0 k s := W k0 k s ∧ (NoUb X g k → Φ.Inv k0 k s)
  Out := Φ.Out

/-- **From a step lemma for defined events to the theorem of the guarded phase.** If the
entry condition gives the invariant at the entry, from a followed state with the invariant the
successor state along an event that is not undefined behaviour has the invariant or the exit
condition, and along any event it has the weak invariant, then the guarded phase runs. (`hlt`:
no undefined-behaviour event precedes an event; `noUb_of_lt`.) -/
theorem Phase.Runs.of_step_noUb {Φ : Phase C g} {W : Nat → Nat → (C g).D → Prop}
    (hlt : ∀ k, k < (X.tr g).length → NoUb X g k)
    (hentry : ∀ k0 s0, At C X g k0 s0 → Φ.In k0 s0 → Φ.Inv k0 k0 s0)
    (hW : ∀ k0 k s, Φ.Inv k0 k s → W k0 k s)
    (hstep : ∀ k0 k e s s', k0 ≤ k → X.get (g, k) = some e → At C X g k s → Φ.Inv k0 k s →
      (∀ pc f, e ≠ ⟨pc, .ub f⟩) → (C g).next s e = some (some s') →
      Φ.Inv k0 (k + 1) s' ∨ Φ.Out k0 (k + 1) s')
    (hweak : ∀ k0 k e s s', k0 ≤ k → X.get (g, k) = some e → At C X g k s → Φ.Inv k0 k s →
      (C g).next s e = some (some s') → W k0 (k + 1) s') :
    (Φ.guard W X).Runs X := by
  intro k0 s0 k s h0 hin hk0 hk hs
  induction k, hk0 using Nat.le_induction generalizing s with
  | base =>
    obtain rfl : s0 = s := Option.some.inj (Option.some.inj (h0.symm.trans hs))
    exact .inl ⟨hW _ _ _ (hentry k0 s0 h0 hin), fun _ => hentry k0 s0 h0 hin⟩
  | succ k hk0 ih =>
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨s1, hs1⟩ := followed_of_le hs (Nat.le_succ k)
    rcases ih s1 (by omega) hs1 with hI | ⟨j, s2, h1, h2, h3, h4⟩
    · have hI1 := hI.2 (hlt k (by omega))
      have hn : (C g).next s1 e = some (some s) := by
        have h := hs
        rw [At, Frame.stateAt_succ he, hs1] at h
        exact h
      by_cases hub : NoUb X g (k + 1)
      · have hne : ∀ pc f, e ≠ ⟨pc, .ub f⟩ :=
          fun pc f h => hub k (Nat.lt_succ_self k) pc f (h ▸ he)
        rcases hstep k0 k e s1 s hk0 he hs1 hI1 hne hn with h | h
        · exact .inl ⟨hW _ _ _ h, fun _ => h⟩
        · exact .inr ⟨k + 1, s, by omega, le_rfl, hs, h⟩
      · exact .inl ⟨hweak k0 k e s1 s hk0 he hs1 hI1 hn, fun h => absurd h hub⟩
    · exact .inr ⟨j, s2, h1, by omega, h3, h4⟩

/-- **From a step lemma for every event to the theorem of a phase.** -/
theorem Phase.Runs.of_step {Φ : Phase C g}
    (hentry : ∀ k0 s0, At C X g k0 s0 → Φ.In k0 s0 → Φ.Inv k0 k0 s0)
    (hstep : ∀ k0 k e s s', k0 ≤ k → X.get (g, k) = some e → At C X g k s → Φ.Inv k0 k s →
      (C g).next s e = some (some s') → Φ.Inv k0 (k + 1) s' ∨ Φ.Out k0 (k + 1) s') :
    Φ.Runs X := by
  intro k0 s0 k s h0 hin hk0 hk hs
  induction k, hk0 using Nat.le_induction generalizing s with
  | base =>
    obtain rfl : s0 = s := Option.some.inj (Option.some.inj (h0.symm.trans hs))
    exact .inl (hentry k0 s0 h0 hin)
  | succ k hk0 ih =>
    obtain ⟨e, he⟩ : ∃ e, (X.tr g)[k]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨s1, hs1⟩ := followed_of_le hs (Nat.le_succ k)
    rcases ih s1 (by omega) hs1 with hI | ⟨j, s2, h1, h2, h3, h4⟩
    · have hn : (C g).next s1 e = some (some s) := by
        have h := hs
        rw [At, Frame.stateAt_succ he, hs1] at h
        exact h
      rcases hstep k0 k e s1 s hk0 he hs1 hI hn with h | h
      · exact .inl h
      · exact .inr ⟨k + 1, s, by omega, le_rfl, hs, h⟩
    · exact .inr ⟨j, s2, h1, by omega, h3, h4⟩

open Classical in
/-- A phase leaves through a first exit (`Phase.Traces.first` for `Runs`). -/
theorem Phase.Runs.first {Φ : Phase C g} (h : Φ.Runs X) : (Φ.first X).Runs X := by
  intro k0 s0 k s h0 hin hk0 hk hs
  rcases h k0 s0 k s h0 hin hk0 hk hs with hi | hex
  · exact .inl hi
  · have hex' : ∃ j, k0 ≤ j ∧ j ≤ k ∧ ∃ s1, At C X g j s1 ∧ Φ.Out k0 j s1 := by
      obtain ⟨j, s1, h1, h2, h3, h4⟩ := hex
      exact ⟨j, h1, h2, s1, h3, h4⟩
    obtain ⟨h1, h2, s1, h3, h4⟩ := Nat.find_spec hex'
    refine .inr ⟨Nat.find hex', s1, h1, h2, h3, h4, fun i si hi1 hi2 hsi => ?_⟩
    rcases h k0 s0 i si h0 hin hi1 (by omega) hsi with hi | ⟨j', s', h1', h2', h3', h4'⟩
    · exact hi
    · exact absurd (Nat.find_min' hex' ⟨h1', by omega, s', h3', h4'⟩) (by omega)

/-- Joining two phases (`Phase.Traces.seq` for `Runs`). -/
theorem Phase.Runs.seq {Φ Ψ : Phase C g} (hΦ : Φ.Runs X) (hΨ : Ψ.Runs X)
    (hlink : ∀ k0 j s1, At C X g j s1 → Φ.Out k0 j s1 → Ψ.In j s1) : (Φ.seq Ψ X).Runs X := by
  intro k0 s0 k s h0 hin hk0 hk hs
  rcases hΦ k0 s0 k s h0 hin hk0 hk hs with hi | ⟨j, s1, h1, h2, h3, h4⟩
  · exact .inl (.inl hi)
  · have hin2 := hlink k0 j s1 h3 h4
    rcases hΨ j s1 k s h3 hin2 h2 hk hs with hi | ⟨j2, s2, h5, h6, h7, h8⟩
    · exact .inl (.inr ⟨j, s1, h1, h2, h3, h4, hin2, hi⟩)
    · exact .inr ⟨j2, s2, by omega, h6, h7, j, s1, h1, h5, h3, h4, hin2, h8⟩

/-- The whole run (`Phase.Traces.run` for `Runs`): a chain whose entry condition holds of the
initial state gives, at every followed state, the invariant of the chain with entry index 0 or
an exit of the chain at an earlier position. -/
theorem Phase.Runs.run {Φ : Phase C g} (h : Φ.Runs X) (hin : Φ.In 0 (C g).init) {k : Nat}
    {s : (C g).D} (hk : k ≤ (X.tr g).length) (hs : At C X g k s) :
    Φ.Inv 0 k s ∨ ∃ j s1, j ≤ k ∧ At C X g j s1 ∧ Φ.Out 0 j s1 := by
  rcases h 0 _ k s at_zero hin (Nat.zero_le _) hk hs with hi | ⟨j, s1, -, h2, h3, h4⟩
  · exact .inl hi
  · exact .inr ⟨j, s1, h2, h3, h4⟩

/-- **A phase entered with a history**: the entry condition is the history `H` (a fact about
the entry position and state), and the exit condition keeps it at the entry index, together
with the order of the two positions and that the exit position is in the trace. -/
def Phase.after (Φ : Phase C g) (H : Nat → (C g).D → Prop) (X : Execution) : Phase C g where
  In := H
  Inv := Φ.Inv
  Out k0 j s := (∃ s0, At C X g k0 s0 ∧ H k0 s0) ∧ k0 ≤ j ∧ j ≤ (X.tr g).length ∧ Φ.Out k0 j s

/-- A phase that runs also runs when entered with a history that gives its entry condition. -/
theorem Phase.Runs.after {Φ : Phase C g} {H : Nat → (C g).D → Prop} (h : Φ.Runs X)
    (hH : ∀ k s, At C X g k s → H k s → Φ.In k s) : (Φ.after H X).Runs X := by
  intro k0 s0 k s h0 hin hk0 hk hs
  rcases h k0 s0 k s h0 (hH k0 s0 h0 hin) hk0 hk hs with hi | ⟨j, s1, h1, h2, h3, h4⟩
  · exact .inl hi
  · exact .inr ⟨j, s1, h1, h2, h3, ⟨s0, h0, hin⟩, h1, by omega, h4⟩

end Generic

namespace Assembly
open PTX.Proof PTX.Flow
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-! ### The history records -/

/-- **The thread left the startup phase at position `j` in the followed state `s`**: the exit
condition holds there (`Startup.OutE`: the exit state at the proxy fence of instruction 387,
the exit ledger, the count of shuffles and elections), and the invariant held at every
position before. -/
structure StartupDone (P : Params) (L : Launch) (X : Execution) (g j : Nat) (s : D) : Prop where
  /-- The state at the exit is followed. -/
  state : At (code L) X g j s
  /-- The exit condition, with the count of warp collectives. -/
  out : Startup.OutE P X g j s
  /-- Every earlier followed state is in the phase. -/
  before : ∀ i si, i < j → At (code L) X g i si → Startup.InvE P X g i si

/-- The entry condition of the Conversion phase at the startup's exit. -/
theorem StartupDone.conversion_in {j : Nat} {s : D} (h : StartupDone P L X g j s) :
    Conversion.In P X g j s := h.out.1

/-- The startup's exit in the form its counting lemmas take (`Startup/Counts.lean`). -/
theorem StartupDone.firstOut {j : Nat} {s : D} (h : StartupDone P L X g j s) :
    Startup.FirstOut P L X g j :=
  ⟨s, h.state, h.out.1, fun i hi si hσ => (h.before i si hi hσ).inv⟩

/-- **The thread left the Conversion phase at position `j` in the followed state `s`**: it
entered at the startup's exit, `Conversion.len g` events earlier, the invariant held at every
position in between, and the exit condition holds at `j` (the state after the transition of
the `bar.sync 0` at instruction 621, with five `bar.sync 0` in the ledger). -/
structure ConversionDone (P : Params) (L : Launch) (X : Execution) (g j : Nat) (s : D) :
    Prop where
  /-- The entry: the startup's exit, and the invariant from there to the exit. -/
  entry : ∃ j0 s0, StartupDone P L X g j0 s0 ∧ j = j0 + Conversion.len g ∧
    ∀ i si, j0 ≤ i → i < j → At (code L) X g i si → Conversion.Inv P X g j0 i si
  /-- The state at the exit is followed. -/
  state : At (code L) X g j s
  /-- The exit condition. -/
  out : Conversion.Out P X g j s

/-- The entry condition of the CarryLoad phase at the Conversion's exit. -/
theorem ConversionDone.carryLoad_in {j : Nat} {s : D} (h : ConversionDone P L X g j s) :
    CarryLoad.In P X g j s := h.out

/-- **The thread left the CarryLoad phase at position `j` in the followed state `s`**: it
entered at the Conversion's exit, `CarryLoad.len g` events earlier, the invariant held at
every position in between, and the exit condition holds at `j` (the state at `bar_5`,
instruction 1402, before its event; the event before is the proxy fence of 1401). -/
structure CarryLoadDone (P : Params) (L : Launch) (X : Execution) (g j : Nat) (s : D) :
    Prop where
  /-- The entry: the Conversion's exit, and the invariant from there to the exit. -/
  entry : ∃ j0 s0, ConversionDone P L X g j0 s0 ∧ j = j0 + CarryLoad.len g ∧
    ∀ i si, j0 ≤ i → i < j → At (code L) X g i si → CarryLoad.Inv P X g j0 i si
  /-- The state at the exit is followed. -/
  state : At (code L) X g j s
  /-- The exit condition. -/
  out : CarryLoad.Out P X g j s

/-- **The thread left the tile loop of its role at position `j` in the followed state `s`**
(the state at `bar_7`, instruction 3113, before its event): it entered at the CarryLoad's exit
`j0`, and by its role the entry condition of its tile loop held there, the exit condition holds
at `j`, and the loop's invariant held at every position in between. `into` is the entry
condition of the epilogue. -/
structure TileDone (P : Params) (L : Launch) (X : Execution) (g j : Nat) (s : D) : Prop where
  /-- The entry and the passage through the tile loop, by role. -/
  entry : ∃ j0 s0, CarryLoadDone P L X g j0 s0 ∧ j0 ≤ j ∧
    ((tid g < 128 ∧ Compute.In P L X g j0 s0 ∧ Compute.Out P L X g j0 j s ∧
        ∀ i si, j0 ≤ i → i < j → At (code L) X g i si → Compute.Inv P L X g j0 i si) ∨
     (warp g = 4 ∧ Producer.Entered P L X g j0 ∧ Producer.Out P L X g j s ∧
        ∀ i si, j0 ≤ i → i < j → At (code L) X g i si → Producer.Inv P L X g i si) ∨
     (warp g = 5 ∧ Store.In P X g j0 s0 ∧ Store.Out P X g j s ∧
        ∀ i si, j0 ≤ i → i < j → At (code L) X g i si → Store.Inv P X g i si))
  /-- The state at the exit is followed. -/
  state : At (code L) X g j s
  /-- The entry condition of the epilogue. -/
  into : Epilogue.In P X g j s

/-! ### The seven phases -/

/-- **The startup phase** in the form of `Ref/Chain.lean`: it is entered at position 0 only (the
initial state, which the exit condition records); its invariant and exit condition are the
extended ones of `Startup/Trace.lean` (`InvE`, `OutE`: with the count of the thread's shuffles
and elections). -/
def startupPhase (P : Params) (L : Launch) (X : Execution) (g : Nat) : Phase (code L) g where
  In k _ := k = 0
  Inv _ k s := Startup.InvE P X g k s
  Out k0 k s := k0 = 0 ∧ Startup.OutE P X g k s

/-- **The Producer phase** (the tile loop of the load warp) in the form of `Ref/Chain.lean`.
The entry condition is `Producer.Entered` (the entry state, the entry ledger and one
successful poll of the state mbarrier); the invariant keeps it at the entry index, because the
phase's exports take it. -/
def producerPhase (P : Params) (L : Launch) (X : Execution) (g : Nat) : Phase (code L) g where
  In k _ := Producer.Entered P L X g k
  Inv k0 k s := Producer.Entered P L X g k0 ∧ Producer.Inv P L X g k s
  Out _ k s := Producer.Out P L X g k s

/-- **The weak invariant of the Store phase**: the state is at a position of the phase with
the position's register facts, or it is the phase's exit state (at `bar_7`). It says nothing
about the ledger. -/
def StoreWeak (P : Params) (g : Nat) (s : D) : Prop :=
  (∃ pos, Store.RefAt P g pos s) ∨ Store.Exit P g s

/-- **The Store phase** (the tile loop of the store warp) in the form of `Ref/Chain.lean`, at
every followed state: the weak invariant `StoreWeak` always, and the invariant `Store.Inv`
when no undefined-behaviour event precedes the position. -/
def storePhase (P : Params) (L : Launch) (X : Execution) (g : Nat) : Phase (code L) g :=
  (Store.phase P L X g).guard (fun _ _ s => StoreWeak P g s) X

/-- **The epilogue** in the form of `Ref/Chain.lean`, at every followed state: the weak
invariant `Epilogue.InvW` always, and the full invariant `Epilogue.Inv` when no
undefined-behaviour event precedes the position. It has no exit: the phase ends with the
thread's `ret`. -/
def epiloguePhase (P : Params) (L : Launch) (X : Execution) (g : Nat) : Phase (code L) g where
  In := Epilogue.In P X g
  Inv k0 k s := Epilogue.InvW P X g k0 k s ∧ (NoUb X g k → Epilogue.Inv P L X g k0 k s)
  Out _ _ _ := False

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads)
include hpre hX hg

/-- **The startup phase runs**: `Startup.startup_invE_le`. -/
theorem startup_runs : (startupPhase P L X g).Runs X := by
  intro k0 s0 k s _ hin hk0 hk hs
  have h00 : k0 = 0 := hin
  rcases Startup.startup_invE_le hpre hX hg hk hs with h | ⟨j, hj, s1, h1, h2⟩
  · exact .inl h
  · exact .inr ⟨j, s1, by omega, hj, h1, h00, h2⟩

/-- **The Conversion phase runs**: its entry is the fence position, and `Conversion.inv_step`
is its step. -/
theorem conversion_runs : (Conversion.phase P L X g).Runs X := by
  refine Phase.Runs.of_step (fun k0 s0 _ hin => ?_) fun k0 k e s s' _ he hσ hI hn => ?_
  · exact ⟨.fence, Conversion.entry_at hin.1, hin.2, rfl, trivial⟩
  · obtain ⟨t, ins, o, hat, -, hc, hf⟩ := Frame.fired_site (sounds hpre) hX he hσ
    exact Conversion.inv_step hpre hg he hI hat hc hf hn

/-- **The CarryLoad phase runs**: `CarryLoad.inv_next` is its step. -/
theorem carryLoad_runs : (CarryLoad.phase P L X g).Runs X := by
  refine Phase.Runs.of_step (fun k0 s0 _ hin => ?_) fun k0 k e s s' _ he hσ hI hn => ?_
  · obtain ⟨pos0, hr0, hd0⟩ := CarryLoad.entry_at hin.1
    exact ⟨pos0, hr0, hin.2, by omega⟩
  · exact CarryLoad.inv_next hpre hX hg he hσ hI hn

/-- **The Compute phase runs**: `Compute.good` is its step. -/
theorem compute_runs : (Compute.phase P L X g).Runs X := by
  refine Phase.Runs.of_step (fun k0 s0 _ hin => Compute.inv_entry hin)
    fun k0 k e s s' _ he hσ hI hn => ?_
  obtain ⟨pos, hR, hled, hjk, hcnt⟩ := hI
  obtain ⟨t, ins, o, hat, -, hc, hf⟩ := Frame.fired_site (sounds hpre) hX he hσ
  rcases Compute.good hpre hg hR hat hc hf hn with ⟨pos', hR', hl, hi⟩ | ⟨hx, hl, hi⟩
  · exact .inl ⟨pos', hR', by rw [Compute.ledOf_succ he, hled, hl], by omega,
      by rw [Compute.counted_succ hjk he, hcnt, hi]⟩
  · exact .inr ⟨hx, by rw [Compute.ledOf_succ he, hled, hl], by omega,
      by rw [Compute.counted_succ hjk he, hcnt, hi]⟩

/-- **The Producer phase runs**, for a thread of the load warp: `Producer.inv_step` is its
step. -/
theorem producer_runs (hw : warp g = 4) : (producerPhase P L X g).Runs X := by
  refine Phase.Runs.of_step (fun k0 s0 h0 hen => ?_) fun k0 k e s s' _ he hσ hI hn => ?_
  · obtain ⟨s1, h1, hE⟩ := (id hen : Producer.Entered P L X g k0).state
    obtain rfl : s1 = s0 := Option.some.inj (Option.some.inj (h1.symm.trans h0))
    exact ⟨hen, .entry,
      ⟨hE.site, hE.tid, hE.p85, hE.p86, hE.p87, hE.p88, hE.scan, hE.elected⟩,
      (id hen : Producer.Entered P L X g k0).led⟩
  · rcases Producer.inv_step hpre hX hg hw he hσ hI.2 hn with h | h
    · exact .inl ⟨hI.1, h⟩
    · exact .inr h

/-- **The Store phase runs**: `Store.inv_step` is its step, for an event that is not undefined
behaviour; `Store.step_at` gives the weak invariant of the successor for every event. -/
theorem store_runs : (storePhase P L X g).Runs X := by
  refine Phase.Runs.of_step_noUb (fun k hk => noUb_of_lt hX hk) (fun k0 s0 _ hin => hin.inv)
    (fun _ _ s hI => ?_) (fun k0 k e s s' _ he hσ hI hub hn => ?_)
    fun k0 k e s s' _ he hσ hI hn => ?_
  · obtain ⟨pos, hr, -⟩ := hI
    exact .inl ⟨pos, hr⟩
  · exact Store.inv_step hpre hX hg he hσ hI hub hn
  · obtain ⟨pos, hr, -⟩ := hI
    obtain ⟨site, w, p, x⟩ := s
    obtain rfl : site = pos.site := hr.site
    rcases Store.step_at hpre hg pos hr hn with ⟨pos', h1, -⟩ | ⟨-, h1, -⟩
    · exact .inl ⟨pos', h1⟩
    · exact .inr h1

/-- **The epilogue runs**: the weak invariant at every followed state
(`Epilogue.epilogue_weak`), and the full one where no undefined-behaviour event precedes
(`Epilogue.inv_step`). -/
theorem epilogue_runs : (epiloguePhase P L X g).Runs X := by
  have hfull : ((Epilogue.phase P L X g).guard (fun _ _ _ => True) X).Runs X :=
    Phase.Runs.of_step_noUb (fun k hk => noUb_of_lt hX hk) (fun k0 s0 _ hin => hin.inv)
      (fun _ _ _ _ => trivial)
      (fun k0 k e s s' _ he hσ hI hub hn =>
        .inl (Epilogue.inv_step hpre hX hg he hσ hI hub hn))
      fun _ _ _ _ _ _ _ _ _ _ => trivial
  intro k0 s0 k s h0 hin hk0 hk hs
  refine .inl ⟨Epilogue.epilogue_weak hpre hX hg h0 hin hk0 hk hs, ?_⟩
  rcases hfull k0 s0 k s h0 hin hk0 hk hs with h | ⟨_, _, _, _, _, h⟩
  · exact h.2
  · exact h.elim

end

/-! ### The links at the site `bar_5`: the CarryLoad's exit is the entry of a tile loop -/

/-- The history at the CarryLoad's exit in the form the links of `Ref/CarryLoad/Links.lean`
take: the first exit of the startup at `j0`, the Conversion's exit at `k1`, and the exit
condition of the CarryLoad phase entered at `k1`. -/
theorem CarryLoadDone.entered {j : Nat} {s : D} (h : CarryLoadDone P L X g j s) :
    ∃ j0 k1, CarryLoad.Entered P L X g j0 k1 ∧ (CarryLoad.phase P L X g).Out k1 j s := by
  obtain ⟨k1, s1, hc, hlen, -⟩ := h.entry
  obtain ⟨j0, s0, hs, hlen1, -⟩ := hc.entry
  exact ⟨j0, k1, ⟨hs.firstOut, hlen1, s1, hc.state, hc.out⟩, hlen, h.out⟩

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads)
include hpre hX hg

/-- The exit of the CarryLoad phase is the entry of the Compute phase, for a compute
thread. -/
theorem compute_in (hr : tid g < 128) {j : Nat} {s : D} (h : CarryLoadDone P L X g j s) :
    Compute.In P L X g j s := by
  obtain ⟨j0, k1, hen, hout⟩ := h.entered
  exact CarryLoad.compute_in hpre hX hg hen hr h.state hout

/-- The exit of the CarryLoad phase is the entry of the Producer phase, for a thread of the
load warp. -/
theorem producer_entered (hr : warp g = 4) {j : Nat} {s : D}
    (h : CarryLoadDone P L X g j s) : Producer.Entered P L X g j := by
  obtain ⟨j0, k1, hen, hout⟩ := h.entered
  exact CarryLoad.producer_entered hpre hX hg hen hr h.state hout

/-- The exit of the CarryLoad phase is the entry of the Store phase, for a thread of the
store warp. -/
theorem store_in (hr : warp g = 5) {j : Nat} {s : D} (h : CarryLoadDone P L X g j s) :
    Store.In P X g j s := by
  obtain ⟨j0, k1, hen, hout⟩ := h.entered
  exact CarryLoad.store_in hpre hX hg hen hr h.state hout

end

/-! ### The chain -/

/-- **The chain of the run of thread `g`** whose tile-loop phase is `T`: startup, conversion,
carry loads, `T`, epilogue, each entered at the first exit of the one before, with the history
record of that exit as its entry condition. -/
def chain (P : Params) (L : Launch) (X : Execution) (g : Nat) (T : Phase (code L) g) :
    Phase (code L) g :=
  ((startupPhase P L X g).first X).seq
    ((((Conversion.phase P L X g).after (StartupDone P L X g) X).first X).seq
      ((((CarryLoad.phase P L X g).after (ConversionDone P L X g) X).first X).seq
        (((T.after (CarryLoadDone P L X g) X).first X).seq
          ((epiloguePhase P L X g).after (TileDone P L X g) X) X) X) X) X

/-- **The chain runs**, for a tile-loop phase `T` that runs, whose entry condition the history
at the CarryLoad's exit gives (`hin`) and whose first exit gives the history record `TileDone`
(`hout`: the role's part of it). -/
theorem chain_runs (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hg : g < L.threads) {T : Phase (code L) g} (hT : T.Runs X)
    (hin : ∀ j s, CarryLoadDone P L X g j s → T.In j s)
    (hout : ∀ k0 s0 j s, CarryLoadDone P L X g k0 s0 → k0 ≤ j → j ≤ (X.tr g).length →
      At (code L) X g j s → T.Out k0 j s →
      (∀ i si, k0 ≤ i → i < j → At (code L) X g i si → T.Inv k0 i si) →
      TileDone P L X g j s) :
    (chain P L X g T).Runs X := by
  refine (startup_runs hpre hX hg).first.seq
    (((conversion_runs hpre hX hg).after fun _ _ _ h => h.conversion_in).first.seq
      (((carryLoad_runs hpre hX hg).after fun _ _ _ h => h.carryLoad_in).first.seq
        (((hT.after fun j s _ h => hin j s h).first.seq
            ((epilogue_runs hpre hX hg).after fun _ _ _ h => h.into) ?_) ) ?_) ?_) ?_
  · rintro k0 j s hs ⟨⟨⟨s0, -, hH⟩, hk0, hj, ho⟩, hb⟩
    exact hout k0 s0 j s hH hk0 hj hs ho hb
  · rintro k0 j s hs ⟨⟨⟨s0, -, hH⟩, -, -, hlen, ho⟩, hb⟩
    exact ⟨⟨k0, s0, hH, hlen, hb⟩, hs, ho⟩
  · rintro k0 j s hs ⟨⟨⟨s0, -, hH⟩, -, -, hlen, ho⟩, hb⟩
    exact ⟨⟨k0, s0, hH, hlen, hb⟩, hs, ho⟩
  · rintro k0 j s hs ⟨⟨rfl, ho⟩, hb⟩
    exact ⟨hs, ho, fun i si hi hσ => hb i si (Nat.zero_le _) hi hσ⟩

/-- The chain of a compute thread. -/
abbrev computeChain (P : Params) (L : Launch) (X : Execution) (g : Nat) : Phase (code L) g :=
  chain P L X g (Compute.phase P L X g)

/-- The chain of a thread of the load warp. -/
abbrev loadChain (P : Params) (L : Launch) (X : Execution) (g : Nat) : Phase (code L) g :=
  chain P L X g (producerPhase P L X g)

/-- The chain of a thread of the store warp. -/
abbrev storeChain (P : Params) (L : Launch) (X : Execution) (g : Nat) : Phase (code L) g :=
  chain P L X g (storePhase P L X g)

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads)
include hpre hX hg

/-- **The chain of a compute thread runs.** -/
theorem compute_chain (hr : tid g < 128) : (computeChain P L X g).Runs X :=
  chain_runs hpre hX hg (compute_runs hpre hX hg) (fun _ _ h => compute_in hpre hX hg hr h)
    fun k0 s0 _ _ hH hk0 _ hs ho hb =>
      ⟨⟨k0, s0, hH, hk0, .inl ⟨hr, compute_in hpre hX hg hr hH, ho, hb⟩⟩, hs,
        Epilogue.in_of_compute ho⟩

/-- **The chain of a thread of the load warp runs.** -/
theorem load_chain (hr : warp g = 4) : (loadChain P L X g).Runs X :=
  chain_runs hpre hX hg (producer_runs hpre hX hg hr)
    (fun _ _ h => producer_entered hpre hX hg hr h)
    fun k0 s0 _ _ hH hk0 _ hs ho hb =>
      ⟨⟨k0, s0, hH, hk0, .inr (.inl ⟨hr, producer_entered hpre hX hg hr hH, ho,
        fun i si h1 h2 h3 => (hb i si h1 h2 h3).2⟩)⟩, hs, Epilogue.in_of_producer hr ho⟩

/-- **The chain of a thread of the store warp runs.** -/
theorem store_chain (hr : warp g = 5) : (storeChain P L X g).Runs X :=
  chain_runs hpre hX hg (store_runs hpre hX hg) (fun _ _ h => store_in hpre hX hg hr h)
    fun k0 s0 _ _ hH hk0 hj hs ho hb =>
      ⟨⟨k0, s0, hH, hk0, .inr (.inr ⟨hr, store_in hpre hX hg hr hH, ho,
        fun i si h1 h2 h3 => (hb i si h1 h2 h3).2 (noUb_of_lt hX (by omega))⟩)⟩, hs,
        Epilogue.in_of_store ho⟩

end

end

end Assembly

end PTX.Kernels.FlashKdaFwd.Proof.Ref
