-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.Run

@[expose] public section

/-!
# The case principle: which phase a followed state of a thread is in

`Stage P L X g k s` says which of the seven phases the followed state `s` of thread `g` at
position `k` is in (the state before the thread's `k`-th event; `k = (X.tr g).length` is the
state after its last event), with what that phase's exported theorems take as hypotheses.
`stage` proves it for every followed state of a launched thread of a consistent execution:

    theorem stage (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
        (hg : g < L.threads) (hk : k ≤ (X.tr g).length) (hσ : At (code L) X g k s) :
        Stage P L X g k s

No other hypothesis remains. A contract field about a thread's event or state is proved by
`cases stage …` with one export of each phase.

**The constructors.** Each carries

* `past`: the history record of the phase before (`Run.lean`: `StartupDone`, `ConversionDone`,
  `CarryLoadDone`, `TileDone`) at the entry index `j0` and the entry state `s0` of the phase
  the state is in. `past.state : At (code L) X g j0 s0` is the followed entry state;
  `past.out` is the exit condition of the phase before (its exit ledger: the counts at the
  entry of the classes the current phase does not count); `past.entry` goes one phase further
  back. The entry condition of the current phase is `past.conversion_in`, `past.carryLoad_in`,
  the field `hin` / `hen` of the three tile loops, `past.into` for the epilogue;
* `hj : j0 ≤ k`;
* the role fact `hr` in the three tile loops (`tid g < 128`, `warp g = 4`, `warp g = 5`);
* `hI`: the invariant of the phase at `k`, `s`.

**The last state.** The invariants of the startup, the Conversion, the CarryLoad, the Compute
and the Producer phase hold at every followed state. The Store phase and the epilogue prove
their step only for an event that is not undefined behaviour, so their invariant is guarded by
`NoUb X g k` ("none of the first `k` events of the thread is undefined behaviour"). Before an
event the guard holds (`noUb_of_lt hX hk`; `stage_event` returns it with the stage); at the
state after the thread's last event it asks that this event is not undefined behaviour. Both
also have a weak invariant unguarded (`hW`): `StoreWeak` (the state is at a position of the
Store phase with its registers, or is the phase's exit state; no ledger) and `Epilogue.InvW`
(position, registers, ordinal, number of `bar.sync 0`). After the thread's `ret` there is no
followed state, so there is no constructor for "exited".

`stage_any` is the statement for an arbitrary position (positions beyond the trace have the
state of position `(X.tr g).length`); `stage_event` is the statement at an event, with the
guard.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- **The phase of a followed state**: the state `s` of thread `g` before its event `k` is in
one of the seven phases of the thread's run, with the history of the run up to the phase's
entry (`past`, at the entry index `j0` and entry state `s0`) and the phase's invariant. -/
inductive Stage (P : Params) (L : Launch) (X : Execution) (g k : Nat) (s : D) : Prop where
  /-- The startup phase (instructions 0 to 386; no entry: it starts at the initial state). -/
  | startup (hI : Startup.InvE P X g k s)
  /-- The Conversion phase (387 to 621), entered at the startup's exit. -/
  | conversion {j0 : Nat} {s0 : D} (past : StartupDone P L X g j0 s0) (hj : j0 ≤ k)
      (hI : Conversion.Inv P X g j0 k s)
  /-- The CarryLoad phase (622 to 1401), entered at the Conversion's exit. -/
  | carryLoad {j0 : Nat} {s0 : D} (past : ConversionDone P L X g j0 s0) (hj : j0 ≤ k)
      (hI : CarryLoad.Inv P X g j0 k s)
  /-- The Compute phase (1402, 2106 to 2944) of a compute thread, entered at the CarryLoad's
  exit. -/
  | compute {j0 : Nat} {s0 : D} (hr : tid g < 128) (past : CarryLoadDone P L X g j0 s0)
      (hj : j0 ≤ k) (hin : Compute.In P L X g j0 s0) (hI : Compute.Inv P L X g j0 k s)
  /-- The Producer phase (1402 to 2105) of a thread of the load warp, entered at the
  CarryLoad's exit. -/
  | producer {j0 : Nat} {s0 : D} (hr : warp g = 4) (past : CarryLoadDone P L X g j0 s0)
      (hj : j0 ≤ k) (hen : Producer.Entered P L X g j0) (hI : Producer.Inv P L X g k s)
  /-- The Store phase (1402, 2945 to 3112) of a thread of the store warp, entered at the
  CarryLoad's exit. Its invariant is guarded and its weak invariant is not: see the header. -/
  | store {j0 : Nat} {s0 : D} (hr : warp g = 5) (past : CarryLoadDone P L X g j0 s0)
      (hj : j0 ≤ k) (hin : Store.In P X g j0 s0) (hI : NoUb X g k → Store.Inv P X g k s)
      (hW : StoreWeak P g s)
  /-- The epilogue (3113 to 3835), entered at the exit of the thread's tile loop. The weak
  invariant holds at every followed state, the full one is guarded: see the header. -/
  | epilogue {j0 : Nat} {s0 : D} (past : TileDone P L X g j0 s0) (hj : j0 ≤ k)
      (hW : Epilogue.InvW P X g j0 k s) (hI : NoUb X g k → Epilogue.Inv P L X g j0 k s)

/-! ### Reading the chain -/

/-- The chain has no exit: its last phase, the epilogue, has none. -/
theorem chain_no_exit {T : Phase (code L) g} {j : Nat} {s : D}
    (h : (chain P L X g T).Out 0 j s) : False := by
  obtain ⟨_, _, -, -, -, -, -, _, _, -, -, -, -, -, _, _, -, -, -, -, -, _, _, -, -, -, -, -,
    -, -, -, hF⟩ := h
  exact hF

/-- **The invariant of the chain, case by case**: the invariant of the startup; or the
startup's history record and the invariant of the Conversion; or the Conversion's record and
the invariant of the CarryLoad; or the CarryLoad's record and the invariant of the tile loop
`T`; or the tile loop's record and the invariant of the epilogue. -/
theorem chain_cases {T : Phase (code L) g} {k : Nat} {s : D}
    (h : (chain P L X g T).Inv 0 k s) :
    Startup.InvE P X g k s ∨
    (∃ j0 s0, StartupDone P L X g j0 s0 ∧ j0 ≤ k ∧ Conversion.Inv P X g j0 k s) ∨
    (∃ j0 s0, ConversionDone P L X g j0 s0 ∧ j0 ≤ k ∧ CarryLoad.Inv P X g j0 k s) ∨
    (∃ j0 s0, CarryLoadDone P L X g j0 s0 ∧ j0 ≤ k ∧ T.Inv j0 k s) ∨
    (∃ j0 s0, TileDone P L X g j0 s0 ∧ j0 ≤ k ∧ Epilogue.InvW P X g j0 k s ∧
      (NoUb X g k → Epilogue.Inv P L X g j0 k s)) := by
  rcases h with h | ⟨j1, s1, -, hj1, -, -, hd1, h⟩
  · exact .inl h
  rcases h with h | ⟨j2, s2, -, hj2, -, -, hd2, h⟩
  · exact .inr (.inl ⟨j1, s1, hd1, hj1, h⟩)
  rcases h with h | ⟨j3, s3, -, hj3, -, -, hd3, h⟩
  · exact .inr (.inr (.inl ⟨j2, s2, hd2, hj2, h⟩))
  rcases h with h | ⟨j4, s4, -, hj4, -, -, hd4, h⟩
  · exact .inr (.inr (.inr (.inl ⟨j3, s3, hd3, hj3, h⟩)))
  · exact .inr (.inr (.inr (.inr ⟨j4, s4, hd4, hj4, h.1, h.2⟩)))

/-- The three roles: a thread is a compute thread, or of the load warp, or of the store
warp. -/
theorem role_cases (g : Nat) : tid g < 128 ∨ warp g = 4 ∨ warp g = 5 := by
  have := tid_lt g
  unfold tid at this
  unfold tid warp
  omega

/-! ### The case principle -/

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads)
include hpre hX hg

/-- **Every followed state of a launched thread is in a phase**, the state after the thread's
last event included. -/
theorem stage {k : Nat} {s : D} (hk : k ≤ (X.tr g).length) (hσ : At (code L) X g k s) :
    Stage P L X g k s := by
  rcases role_cases g with hr | hr | hr
  · rcases (compute_chain hpre hX hg hr).run rfl hk hσ with h | ⟨j, s1, -, -, h⟩
    · rcases chain_cases h with h | ⟨j0, s0, hd, hj, h⟩ | ⟨j0, s0, hd, hj, h⟩ |
        ⟨j0, s0, hd, hj, h⟩ | ⟨j0, s0, hd, hj, h1, h2⟩
      · exact .startup h
      · exact .conversion hd hj h
      · exact .carryLoad hd hj h
      · exact .compute hr hd hj (compute_in hpre hX hg hr hd) h
      · exact .epilogue hd hj h1 h2
    · exact (chain_no_exit h).elim
  · rcases (load_chain hpre hX hg hr).run rfl hk hσ with h | ⟨j, s1, -, -, h⟩
    · rcases chain_cases h with h | ⟨j0, s0, hd, hj, h⟩ | ⟨j0, s0, hd, hj, h⟩ |
        ⟨j0, s0, hd, hj, h⟩ | ⟨j0, s0, hd, hj, h1, h2⟩
      · exact .startup h
      · exact .conversion hd hj h
      · exact .carryLoad hd hj h
      · exact .producer hr hd hj h.1 h.2
      · exact .epilogue hd hj h1 h2
    · exact (chain_no_exit h).elim
  · rcases (store_chain hpre hX hg hr).run rfl hk hσ with h | ⟨j, s1, -, -, h⟩
    · rcases chain_cases h with h | ⟨j0, s0, hd, hj, h⟩ | ⟨j0, s0, hd, hj, h⟩ |
        ⟨j0, s0, hd, hj, h⟩ | ⟨j0, s0, hd, hj, h1, h2⟩
      · exact .startup h
      · exact .conversion hd hj h
      · exact .carryLoad hd hj h
      · exact .store hr hd hj (store_in hpre hX hg hr hd) h.2 h.1
      · exact .epilogue hd hj h1 h2
    · exact (chain_no_exit h).elim

/-- **The phase of the state before an event**, with the guard of the Store phase's and the
epilogue's invariant: no undefined-behaviour event precedes an event. -/
theorem stage_event {k : Nat} {s : D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : At (code L) X g k s) : Stage P L X g k s ∧ NoUb X g k :=
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  ⟨stage hpre hX hg (Nat.le_of_lt hk) hσ, noUb_of_lt hX hk⟩

/-- **The phase of a followed state at any position**: a position beyond the thread's trace
has the state after the thread's last event. -/
theorem stage_any {k : Nat} {s : D} (hσ : At (code L) X g k s) :
    Stage P L X g (min k (X.tr g).length) s := by
  rcases Nat.le_total k (X.tr g).length with hk | hk
  · rw [Nat.min_eq_left hk]
    exact stage hpre hX hg hk hσ
  · rw [Nat.min_eq_right hk]
    have hσ' : At (code L) X g (X.tr g).length s := by
      rw [At, ← Frame.stateAt_of_le hk]
      exact hσ
    exact stage hpre hX hg le_rfl hσ'

end

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
