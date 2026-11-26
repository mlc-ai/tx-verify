-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.Tracked
public import Kernels.FlashKdaFwd.Proof.Ref.Startup.Contract
public import Kernels.FlashKdaFwd.Proof.Ref.Epilogue.Contract
public import Kernels.FlashKdaFwd.Proof.Ref.Kinds
public import Kernels.FlashKdaFwd.Proof.Protocol.Export
public import Lemmas.Flow.NthEv
public import Lemmas.Step.ExitLast

@[expose] public section

/-!
# Assembly, group A: the sixteen fields of `BarFacts`, `InitFacts` and `LifeFacts`

The protocol layer (`Proof/Protocol/`) proves its theorems about the kernel's barriers and
memory barriers from contracts about the events of single threads. This file proves three of
those contracts for every consistent execution under the precondition: `Protocol.BarFacts`
(`Bars.lean`, 8 fields), `Protocol.InitFacts` (`Init.lean`, 4 fields) and `Protocol.LifeFacts`
(`Life.lean`, 4 fields). `FactsA.lean` states the three final theorems.

**Words.** An *event* of thread `g` is `X.get (g, k)`, its `k`-th event. A *followed state* at
`k` is the state `s` of the thread's machine before that event (`At (code L) X g k s`);
`s.site.pc` is the index of the instruction the state is at. A *stage* is one of the seven
phases of a thread's run (startup, conversion, carry loads, the tile loop of the thread's role
— compute thread, load warp, store warp — and the epilogue; `Stage.lean`). `bar.sync 0` is
the barrier of the whole thread block and `bar.sync 8, 128` the *named barrier* of the 128
compute threads; `bar0Before X (g, k)` counts the thread's `bar.sync 0` before event `k`. An
*mbarrier* is one of the eleven memory-barrier objects of a block (`Protocol.Bar`); an event
*names* an mbarrier when it arrives on it, polls it, initializes it or issues a tensor load that
completes on it (`Frame.MbarOf`). *Undefined behaviour* is an event of kind `.ub`.

**Method.** An event that is not undefined behaviour is fired from a followed state, which is
in a stage and at the event's instruction (`event_site`, from the chain's `event_stage`). The
kind of the event decides the kind of site it was fired at (`Ref/Kinds`), hence a set of
instructions; the instruction decides the stage (`Sites.lean: Stage.of_pc_*`) and the number
of earlier `bar.sync 0` (`Stage.bar0`). So most cases need no fact of a phase at all:

* a barrier event is at one of the nine `bar.sync 0` instructions, where its event is
  `bar.sync 0` (`Ref.bar0_event`) and its ordinal is the number of those instructions below it,
  or at instruction 2913, which is in the Compute phase (`bar_event`);
* an initialization is fired in the startup phase (`init_startup`); an event that names an
  mbarrier in the startup phase or in a tile loop (`mbarOf_pc`); a tensor load in the startup
  phase or the load leader's loop; a tensor store in the store leader's loop or the epilogue;
  the `ret` in the epilogue.

A field about counts over a thread's whole trace is proved from the event that would be one
too many (`bar0_le`, `bar8_le`, `full_issues_thread`): that event is fired from a followed
state whatever happens after it, so no statement about the thread's last state is needed.

**What the phases give.** Startup: `Startup/Contract.lean` (`init_ev_startup`,
`init_once_startup`, `init_done_startup`, `use_ev_startup`, `state_polled_startup`) and
`issue_startup`. Producer: `producer_good` and `issue_shape` (the closed form of each event
and the ledger of loads). Epilogue: `store_wait`. Compute: the exit ledger (`compute_out`)
and the two fields of `ComputeOwes`. Store: the two fields of `StoreOwes`. The two `Owes`
structures are proved in `FactsAOwes.lean` from the export files of the two phases.

**The fields.**

| contract field | lemma | from |
|---|---|---|
| `BarFacts.shape`, `bar0_pc`, `bar8_pc` | `bar_shape`, `bar0_pc`, `bar8_pc` | `bar_event` |
| `BarFacts.bar0_le`, `bar8_le` | `bar0_le`, `bar8_le` | the event one too many |
| `BarFacts.bar0_exit` | `bar0_exit` | `Stage.bar0` at the `ret`, the `ret` is last |
| `BarFacts.bar8_exit` | `bar8_exit` | `bar8_le`, the Compute phase's exit ledger |
| `BarFacts.sched` | `bar_sched` | `isBar_split`, `bar_event`, the exit ledger |
| `InitFacts.init_ev`, `init_once`, `init_done` | same names | the startup's exports |
| `InitFacts.use_ev` | `use_ev` | `mbarOf_pc`, then startup, Producer, the two `Owes` |
| `LifeFacts.store_wait` | `store_wait` | `StoreOwes.store_wait`, `Epilogue.store_wait` |
| `LifeFacts.state_polled` | `state_polled` | `Startup.state_polled_startup` |
| `LifeFacts.full_issues` | `full_issues_thread` | `Startup.issue_startup`, `issue_shape` |
| `LifeFacts.full_polled` | `full_polled_thread` | the Compute phase's exit ledger |

`barFacts_of`, `initFacts_of`, `lifeFacts_of` at the end are the three structures. Everything
here is in the namespace `Assembly.FactsA`.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly.FactsA
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Protocol

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-! ### What the Compute phase and the Store phase still owe -/

/-- **What group A needs from the Compute phase** (instructions 2106 to 2944), each field for
an event `k` of a thread `g` at a followed state `s` with the phase's invariant. -/
structure ComputeOwes (P : Params) (L : Launch) (X : Execution) : Prop where
  /-- A barrier event at the instruction of the named barrier (2913) is `bar.sync 8, 128`, and
  the thread has made fewer named barriers before it than its sequence has tiles. -/
  bar8 : ∀ {g j0 k pc id : Nat} {cnt : Option Nat} {mode : BarMode} {s : D},
    At (code L) X g k s → Compute.Inv P L X g j0 k s →
    X.get (g, k) = some ⟨pc, .bar id cnt mode⟩ → s.site.pc = 2913 →
      id = 8 ∧ cnt = some 128 ∧ mode = .sync ∧
        ((X.tr g).take k).countP (Execution.isBarId 8) < Compute.tilesOf P g
  /-- An event that names an mbarrier names one of the eleven mbarriers of the thread's
  block. -/
  mbar : ∀ {g j0 k : Nat} {e : Event} {m : Loc} {s : D},
    At (code L) X g k s → Compute.Inv P L X g j0 k s → X.get (g, k) = some e →
    Frame.MbarOf e m → ∃ b : Bar, m = b.loc L (g / L.block)

/-- **What group A needs from the Store phase** (instructions 2945 to 3112), each field for an
event `k` of a thread `g` at a followed state `s` with the phase's invariant. -/
structure StoreOwes (P : Params) (L : Launch) (X : Execution) : Prop where
  /-- An event that names an mbarrier names one of the eleven mbarriers of the thread's
  block. -/
  mbar : ∀ {g k : Nat} {e : Event} {m : Loc} {s : D},
    At (code L) X g k s → Store.Inv P X g k s → X.get (g, k) = some e →
    Frame.MbarOf e m → ∃ b : Bar, m = b.loc L (g / L.block)
  /-- Between a tensor store of the phase and a later followed state with the phase's exit
  condition, the thread executes a `.read` bulk-group wait that covers the store. -/
  store_wait : ∀ {g k0 k j pc al : Nat} {sp : TensorStore.Spec} {s0 s sj : D},
    At (code L) X g k0 s0 → Store.In P X g k0 s0 → k0 ≤ k →
    X.get (g, k) = some ⟨pc, .tensorStore al sp⟩ →
    At (code L) X g k s → Store.Inv P X g k s →
    At (code L) X g j sj → Store.Out P X g j sj →
      ∃ w, k < w ∧ w < j ∧ BulkWaitsFor X .read (g, k) (g, w)

/-! ### Small facts about lists, instructions and roles -/

/-- A class of events that is the disjoint union of two classes on a list is counted by the
sum of their counts. -/
theorem countP_split {l : List Event} {p q r : Event → Bool}
    (h : ∀ x ∈ l, (if p x then 1 else 0) = (if q x then 1 else 0) + (if r x then 1 else 0)) :
    l.countP p = l.countP q + l.countP r := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have h1 := h a (List.mem_cons_self ..)
    have h2 := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp only [List.countP_cons]
    omega

/-- The `bar.sync 0` instruction with `n` of the nine below it is the `n`-th. -/
theorem bar0Pcs_idx : ∀ pc ∈ bar0Pcs, bar0Pcs[(bar0Pcs.filter (· < pc)).length]? = some pc := by
  decide

/-- An event of the class "`bar.sync` of barrier `id`" is such a barrier event. -/
theorem isBarId_form {id : Nat} {e : Event} (h : Execution.isBarId id e = true) :
    ∃ pc cnt m, e = ⟨pc, .bar id cnt m⟩ := NamedBar.isBarId_form h

/-- A barrier publishes after at most two `bar.sync 0` of its initializing thread. -/
theorem gen_le (b : Bar) : b.gen ≤ 2 := by cases b <;> simp [Bar.gen]

/-- The tile count of the block of a thread, in the protocol layer's and in the reference
layer's notation. -/
theorem ctaTiles_eq (hpre : Pre P L mem0) (g : Nat) :
    ctaTiles P (g / L.block) = Compute.tilesOf P g := by
  rw [hpre.block]
  rfl

/-- The initializations are at instructions of the startup. -/
theorem mbarInit_pc : ∀ j, (Site.mbarInit j).pc ≤ 384 := by decide

/-- The polls are at instructions of the startup or of a tile loop. -/
theorem mbarWait_pc : ∀ j,
    (Site.mbarWait j).pc ≤ 384 ∨ (1402 < (Site.mbarWait j).pc ∧ (Site.mbarWait j).pc ≤ 3112) := by
  decide

/-- The arrivals are at instructions of the startup or of a tile loop. -/
theorem mbarArrive_pc : ∀ j, (Site.mbarArrive j).pc ≤ 384 ∨
    (1402 < (Site.mbarArrive j).pc ∧ (Site.mbarArrive j).pc ≤ 3112) := by
  decide

/-- The tensor loads are at instructions of the startup or of the load leader's loop. -/
theorem tensorLoad_pc : ∀ j : Fin 258, j.val < firstStoreCopy → (Site.tensorCopy j).pc ≤ 384 ∨
    (1402 < (Site.tensorCopy j).pc ∧ (Site.tensorCopy j).pc ≤ 2105) := by
  decide +kernel

/-- The tensor stores are at instructions of the store leader's loop or of the epilogue. -/
theorem tensorStore_pc : ∀ j : Fin 258, firstStoreCopy ≤ j.val →
    2944 < (Site.tensorCopy j).pc := by
  decide +kernel

/-! ### An event, its state and its phase -/

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
include hpre hX

/-- **The state before an event that is not undefined behaviour**: it is followed, in a stage,
no undefined-behaviour event precedes it, and it is at the event's instruction. -/
theorem event_site {k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hne : ∀ f, e.kind ≠ .ub f) :
    ∃ s, At (code L) X g k s ∧ Stage P L X g k s ∧ NoUb X g k ∧ s.site.pc = e.pc := by
  obtain ⟨s, hs, hst, hub⟩ := event_stage hpre hX he hne
  exact ⟨s, hs, hst, hub, (Frame.event_pc (sounds hpre) hX he hs).symm⟩

/-! ### The barriers (`Protocol.BarFacts`) -/

/-- **Every barrier event**: `bar.sync 0` at the instruction of its ordinal among the nine, or
the named barrier `bar.sync 8, 128` of a compute thread at instruction 2913, after six
`bar.sync 0` and fewer named barriers than the block has tiles. -/
theorem bar_event (hC : ComputeOwes P L X) {k pc id : Nat} {cnt : Option Nat} {mode : BarMode}
    (he : X.get (g, k) = some ⟨pc, .bar id cnt mode⟩) :
    mode = .sync ∧
      ((id = 0 ∧ cnt = none ∧ bar0Pcs[bar0Before X (g, k)]? = some pc) ∨
        (id = 8 ∧ cnt = some 128 ∧ pc = 2913 ∧ tid g < 128 ∧ bar0Before X (g, k) = 6 ∧
          ((X.tr g).take k).countP (Execution.isBarId 8) < ctaTiles P (g / L.block))) := by
  obtain ⟨s, hs, hst, hub, hpc⟩ := event_site hpre hX he (fun f h => by cases h)
  have hpc' : s.site.pc = pc := hpc
  have hb0 := hst.bar0 hub
  obtain ⟨-, -, h0 | h8⟩ := bar_site_pc (sounds hpre) hX he hs rfl
  · have hev := bar0_event (sounds hpre) hX he hs h0
    injection hev with h1 h2
    injection h2 with h3 h4 h5
    refine ⟨h5, .inl ⟨h3, h4, ?_⟩⟩
    rw [bar0Before_eq, hb0, hpc']
    exact bar0Pcs_idx pc (hpc' ▸ h0)
  · obtain ⟨hr, j0, s0, -, -, -, hI⟩ := hst.of_pc_compute (by omega) (by omega)
    obtain ⟨h1, h2, h3, h4⟩ := hC.bar8 hs hI he h8
    have hb : bar0Before X (g, k) = 6 := by
      rw [bar0Before_eq, hb0, h8]
      rfl
    exact ⟨h3, .inr ⟨h1, h2, by omega, hr, hb, by rw [ctaTiles_eq hpre]; exact h4⟩⟩

/-- `BarFacts.shape`. -/
theorem bar_shape (hC : ComputeOwes P L X) {k pc id : Nat} {cnt : Option Nat} {mode : BarMode}
    (he : X.get (g, k) = some ⟨pc, .bar id cnt mode⟩) :
    mode = .sync ∧ ((id = 0 ∧ cnt = none) ∨ (id = 8 ∧ cnt = some 128 ∧ g % L.block < 128)) := by
  obtain ⟨hm, ⟨h1, h2, -⟩ | ⟨h1, h2, -, h3, -⟩⟩ := bar_event hpre hX hC he
  · exact ⟨hm, .inl ⟨h1, h2⟩⟩
  · exact ⟨hm, .inr ⟨h1, h2, by rw [block_mod hpre]; exact h3⟩⟩

/-- `BarFacts.bar0_pc`. -/
theorem bar0_pc (hC : ComputeOwes P L X) {k pc : Nat} {cnt : Option Nat} {mode : BarMode}
    (he : X.get (g, k) = some ⟨pc, .bar 0 cnt mode⟩) :
    bar0Pcs[bar0Before X (g, k)]? = some pc := by
  obtain ⟨-, ⟨-, -, h⟩ | ⟨h, -⟩⟩ := bar_event hpre hX hC he
  · exact h
  · cases h

/-- `BarFacts.bar8_pc`. -/
theorem bar8_pc (hC : ComputeOwes P L X) {k pc : Nat} {cnt : Option Nat} {mode : BarMode}
    (he : X.get (g, k) = some ⟨pc, .bar 8 cnt mode⟩) : pc = 2913 := by
  obtain ⟨-, ⟨h, -⟩ | ⟨-, -, h, -⟩⟩ := bar_event hpre hX hC he
  · cases h
  · exact h

/-- `BarFacts.bar0_le`: a tenth `bar.sync 0` would be at the tenth of nine instructions. -/
theorem bar0_le (hC : ComputeOwes P L X) : (X.tr g).countP (Execution.isBarId 0) ≤ 9 := by
  by_contra h
  have h' : 9 + 1 ≤ ((X.tr g).take (X.tr g).length).countP (Execution.isBarId 0) := by
    rw [List.take_length]
    omega
  obtain ⟨j, e, -, he, hp, hc⟩ := exists_nthEv h'
  obtain ⟨pc, cnt, mode, rfl⟩ := isBarId_form hp
  have h9 := bar0_pc hpre hX hC he
  rw [show bar0Before X (g, j) = 9 from hc] at h9
  simp [bar0Pcs] at h9

/-- `BarFacts.bar0_exit`: the `ret` is after the ninth `bar.sync 0`, and it is the thread's
last event. -/
theorem bar0_exit {j pc : Nat} (he : X.get (g, j) = some ⟨pc, .exit⟩) :
    (X.tr g).countP (Execution.isBarId 0) = 9 := by
  obtain ⟨s, hs, hst, hub, -⟩ := event_site hpre hX he (fun f h => by cases h)
  obtain ⟨-, hpc⟩ := exit_site_pc (sounds hpre) hX he hs rfl
  have hb := hst.bar0 hub
  rw [hpc] at hb
  have hlen := Execution.exit_last hX (Frame.lt_of_get hX he) he
  have h1 := Frame.countP_take_succ_ite (Execution.isBarId 0) he
  rw [hlen, List.take_length, hb] at h1
  exact h1

/-- `BarFacts.bar8_le`: one more named barrier than the block has tiles would be made after
as many named barriers as the block has tiles. -/
theorem bar8_le (hC : ComputeOwes P L X) :
    (X.tr g).countP (Execution.isBarId 8) ≤ ctaTiles P (g / L.block) := by
  by_contra h
  have h' : ctaTiles P (g / L.block) + 1 ≤
      ((X.tr g).take (X.tr g).length).countP (Execution.isBarId 8) := by
    rw [List.take_length]
    omega
  obtain ⟨j, e, -, he, hp, hc⟩ := exists_nthEv h'
  obtain ⟨pc, cnt, mode, rfl⟩ := isBarId_form hp
  obtain ⟨-, ⟨h0, -⟩ | ⟨-, -, -, -, -, hlt⟩⟩ := bar_event hpre hX hC he
  · cases h0
  · omega

omit hpre hX in
/-- The ledger at the exit of the Compute phase: one named barrier per tile, and one
successful poll of `loadFull st` per use of load stage `st`. -/
theorem compute_out {j0 k : Nat} {s : D} (ho : Compute.Out P L X g j0 k s) :
    ((X.tr g).take k).countP (Execution.isBarId 8) = Compute.tilesOf P g ∧
      ∀ st : Fin 3, okPolls ((Bar.loadFull st).loc L (g / L.block)) ((X.tr g).take k) =
        uses 3 (Compute.tilesOf P g) st.val := by
  obtain ⟨-, hl, -⟩ := ho
  refine ⟨congrArg Compute.Led.bar8 hl, fun st => ?_⟩
  fin_cases st
  · exact congrArg Compute.Led.pf0 hl
  · exact congrArg Compute.Led.pf1 hl
  · exact congrArg Compute.Led.pf2 hl

omit hpre hX in
/-- A compute thread in the epilogue left the Compute phase at the epilogue's entry. -/
theorem tileDone_compute {j0 : Nat} {s0 : D} (h : TileDone P L X g j0 s0) (hc : tid g < 128) :
    ∃ j1, Compute.Out P L X g j1 j0 s0 := by
  obtain ⟨j1, s1, -, -, ⟨-, -, ho, -⟩ | ⟨hw, -⟩ | ⟨hw, -⟩⟩ := h.entry
  · exact ⟨j1, ho⟩
  · have := (warp_eq4_iff g).mp hw
    omega
  · have := (warp_eq5_iff g).mp hw
    omega

/-- `BarFacts.bar8_exit`: at most one named barrier per tile, and at the entry of the
epilogue the compute thread had made one per tile. -/
theorem bar8_exit (hC : ComputeOwes P L X) {j pc : Nat} (hc : g % L.block < 128)
    (he : X.get (g, j) = some ⟨pc, .exit⟩) :
    (X.tr g).countP (Execution.isBarId 8) = ctaTiles P (g / L.block) := by
  refine le_antisymm (bar8_le hpre hX hC) ?_
  obtain ⟨s, hs, hst, hub, -⟩ := event_site hpre hX he (fun f h => by cases h)
  obtain ⟨-, hpc⟩ := exit_site_pc (sounds hpre) hX he hs rfl
  obtain ⟨j0, s0, past, -, -, -⟩ := hst.of_pc_epilogue (by omega) (.inl hub)
  obtain ⟨j1, ho⟩ := tileDone_compute past (by rw [← block_mod hpre]; exact hc)
  rw [ctaTiles_eq hpre, ← (compute_out ho).1]
  exact (List.take_sublist _ _).countP_le

/-- **The barrier events of a thread are those on barrier 0 and those on barrier 8.** -/
theorem isBar_split (hC : ComputeOwes P L X) (k : Nat) :
    ((X.tr g).take k).countP Execution.isBar =
      bar0Before X (g, k) + ((X.tr g).take k).countP (Execution.isBarId 8) := by
  rw [bar0Before_eq]
  refine countP_split fun x hx => ?_
  obtain ⟨i, hi⟩ := List.getElem?_of_mem (List.mem_of_mem_take hx)
  obtain ⟨pc, kd⟩ := x
  cases kd <;> try rfl
  rename_i id cnt mode
  have hi' : X.get (g, i) = some ⟨pc, .bar id cnt mode⟩ := hi
  obtain ⟨-, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩ := bar_event hpre hX hC hi' <;> rfl

omit hpre hX in
/-- A `bar.sync 0` instruction with at least six of the nine below it is one of the
epilogue. -/
theorem bar0Pcs_late {n pc : Nat} (h : bar0Pcs[n]? = some pc) (h6 : 6 ≤ n) : 3113 ≤ pc := by
  have hn : n < 9 := (List.getElem?_eq_some_iff.mp h).1
  interval_cases n <;> simp [bar0Pcs] at h <;> omega

/-- `BarFacts.sched`. The barrier events before a barrier event are `bar.sync 0` and named
barriers. A named barrier is made after six `bar.sync 0`, so before one of the first six
`bar.sync 0` there is none; a later `bar.sync 0` is in the epilogue, where a compute thread has
made all its named barriers; and a named barrier comes after six `bar.sync 0` and fewer named
barriers than the block has tiles. -/
theorem bar_sched (hC : ComputeOwes P L X) {k pc id : Nat} {cnt : Option Nat} {mode : BarMode}
    (he : X.get (g, k) = some ⟨pc, .bar id cnt mode⟩) :
    (id, cnt, mode) = barSched (decide (g % L.block < 128)) (ctaTiles P (g / L.block))
      (((X.tr g).take k).countP Execution.isBar) := by
  rw [isBar_split hpre hX hC k]
  obtain ⟨hm, ⟨h1, h2, h3⟩ | ⟨h1, h2, -, h3, h4, h5⟩⟩ := bar_event hpre hX hC he
  · subst hm h1 h2
    unfold barSched
    split
    case isFalse => rfl
    rename_i hcond
    exfalso
    obtain ⟨hc, h6, hT⟩ := hcond
    have hc' : tid g < 128 := by
      rw [← block_mod hpre]
      exact of_decide_eq_true hc
    by_cases h5 : bar0Before X (g, k) ≤ 5
    · have h8 : ((X.tr g).take k).countP (Execution.isBarId 8) = 0 := by
        by_contra hne
        obtain ⟨i, e, hik, hei, hp, -⟩ := exists_nthEv (n := 0)
          (show 0 + 1 ≤ ((X.tr g).take k).countP (Execution.isBarId 8) by omega)
        obtain ⟨pc', cnt', mode', rfl⟩ := isBarId_form hp
        obtain ⟨-, ⟨h0, -⟩ | ⟨-, -, -, -, hb, -⟩⟩ := bar_event hpre hX hC hei
        · cases h0
        · have := Flow.countP_take_mono (Execution.isBarId 0) (X.tr g) (Nat.le_of_lt hik)
          rw [bar0Before_eq] at hb h5
          omega
      omega
    · obtain ⟨s, hs, hst, hub, hpc⟩ := event_site hpre hX he (fun f h => by cases h)
      have hpc' : s.site.pc = pc := hpc
      have hlate := bar0Pcs_late h3 (by omega)
      obtain ⟨j0, s0, past, hj, -, -⟩ := hst.of_pc_epilogue (by omega) (.inl hub)
      obtain ⟨j1, ho⟩ := tileDone_compute past hc'
      have h8 := (compute_out ho).1
      have := Flow.countP_take_mono (Execution.isBarId 8) (X.tr g) hj
      rw [ctaTiles_eq hpre] at hT
      omega
  · subst hm h1 h2
    unfold barSched
    split
    case isTrue => rfl
    rename_i hcond
    exact absurd ⟨decide_eq_true (by rw [block_mod hpre]; exact h3), by omega, by omega⟩ hcond

/-! ### Initialization and use of the mbarriers (`Protocol.InitFacts`) -/

/-- An initialization is fired at a state of the startup phase. -/
theorem init_startup {k pc n : Nat} {m : Loc} (he : X.get (g, k) = some ⟨pc, .mbInit m n⟩) :
    ∃ s, At (code L) X g k s ∧ Startup.InvE P X g k s := by
  obtain ⟨s, hs, hst, -, -⟩ := event_site hpre hX he (fun f h => by cases h)
  obtain ⟨j, hj⟩ := mbInit_site (sounds hpre) hX he hs rfl
  exact ⟨s, hs, hst.of_pc_startup (by rw [hj]; have := mbarInit_pc j; omega)⟩

/-- `InitFacts.init_ev`. -/
theorem init_ev {k pc n : Nat} {m : Loc} (he : X.get (g, k) = some ⟨pc, .mbInit m n⟩) :
    ∃ b : Bar, m = b.loc L (g / L.block) ∧ n = b.count ∧ g = b.owner L (g / L.block) ∧
      bar0Before X (g, k) = b.gen := by
  obtain ⟨s, hs, hI⟩ := init_startup hpre hX he
  exact (Startup.init_ev_startup hpre hX (Frame.lt_of_get hX he) he hs).resolve_right
    hI.inv.not_left

/-- `InitFacts.init_once`. -/
theorem init_once {k k' pc pc' n n' : Nat} {m : Loc}
    (he : X.get (g, k) = some ⟨pc, .mbInit m n⟩)
    (he' : X.get (g, k') = some ⟨pc', .mbInit m n'⟩) : k = k' := by
  obtain ⟨s, hs, hI⟩ := init_startup hpre hX he
  obtain ⟨s', hs', hI'⟩ := init_startup hpre hX he'
  rcases Startup.init_once_startup hpre hX (Frame.lt_of_get hX he) he he' hs hs' with h | h | h
  · exact h
  · exact absurd h hI.inv.not_left
  · exact absurd h hI'.inv.not_left

/-- `InitFacts.init_done`: a `bar.sync 0` with at most two earlier ones is fired in the
startup phase. -/
theorem init_done {c k pc : Nat} {cnt : Option Nat} {mode : BarMode} (b : Bar)
    (he : X.get (b.owner L c, k) = some ⟨pc, .bar 0 cnt mode⟩)
    (hb : bar0Before X (b.owner L c, k) = b.gen) :
    ∃ j pcj, j < k ∧ X.get (b.owner L c, j) = some ⟨pcj, .mbInit (b.loc L c) b.count⟩ := by
  obtain ⟨s, hs, hst, hub, -⟩ := event_site hpre hX he (fun f h => by cases h)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hst.bar0_bounds hub
  have hg2 := gen_le b
  have hb' := hb
  rw [bar0Before_eq] at hb'
  have hlt : s.site.pc < 387 := by
    rcases hst.pc_cases with h | h | h | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | h <;> omega
  have hI := hst.of_pc_startup hlt
  exact (Startup.init_done_startup hpre hX (Frame.lt_of_get hX he) b rfl he hb hs).resolve_right
    hI.inv.not_left

/-- **An event that names an mbarrier is fired at an instruction of the startup or of a tile
loop**: such an event is an arrival, a poll, an initialization or the issue of a tensor
load. -/
theorem mbarOf_pc {k : Nat} {e : Event} {m : Loc} {s : D} (he : X.get (g, k) = some e)
    (hs : At (code L) X g k s) (hm : Frame.MbarOf e m) :
    s.site.pc ≤ 384 ∨ (1402 < s.site.pc ∧ s.site.pc ≤ 3112) := by
  have hf := site_fires (sounds hpre) hX he hs
  obtain ⟨pc, kd⟩ := e
  cases kd with
  | arrive m' tx c rel sc =>
    obtain ⟨j, hj⟩ := arrive_site (sounds hpre) hX he hs rfl
    rw [hj]
    exact mbarArrive_pc j
  | wait m' q ok acq sc =>
    obtain ⟨j, hj⟩ := wait_site (sounds hpre) hX he hs rfl
    rw [hj]
    exact mbarWait_pc j
  | mbInit m' n =>
    obtain ⟨j, hj⟩ := mbInit_site (sounds hpre) hX he hs rfl
    rw [hj]
    exact .inl (mbarInit_pc j)
  | tensorIssue al sp =>
    obtain ⟨j, hj, hlt⟩ := tensorIssue_site (sounds hpre) hX he hs rfl
    rw [hj]
    rcases tensorLoad_pc j hlt with h | ⟨h1, h2⟩
    · exact .inl h
    · exact .inr ⟨h1, by omega⟩
  | _ =>
    first
      | exact hm.elim
      | (exfalso; revert hf; generalize s.site.kind = κ; cases κ <;> simp [firedAt])

/-- An event of the Producer phase that names an mbarrier names one of the thread's block. -/
theorem producer_mbar (hg : g < L.threads) (hw : warp g = 4) {k : Nat} {e : Event} {m : Loc}
    {s : D} (he : X.get (g, k) = some e) (hs : At (code L) X g k s)
    (hI : Producer.Inv P L X g k s) (hm : Frame.MbarOf e m) :
    ∃ b : Bar, m = b.loc L (g / L.block) := by
  obtain ⟨pos, w, p, x, -, hr, hl, hev, -⟩ := Producer.producer_good hpre hX hg hw he hs hI
  obtain ⟨pc, kd⟩ := e
  cases pos with
  | entry => cases hev; exact hm.elim
  | poll c u =>
    obtain ⟨ok, h⟩ := id hev
    cases h
    exact ⟨.loadEmpty (Producer.stage (Producer.tile c u)), hm⟩
  | arrive c u =>
    cases id hev
    exact ⟨.loadFull (Producer.stage (Producer.tile c u)), hm⟩
  | load c u i =>
    cases id hev
    refine ⟨.loadFull (Producer.stage (Producer.tile c u)), ?_⟩
    rw [← show (Producer.tileLoad P L g (Producer.tile c u) i.val).mbar = m from hm,
      Producer.tileLoad, loadSpec_mbar, Producer.fullLoc_eq hpre]
  | tail j =>
    obtain ⟨ok, h⟩ := id hev
    cases h
    exact ⟨.loadEmpty (Producer.stage (Producer.tilesOf P g + j.val)), hm⟩

/-- `InitFacts.use_ev`. In the startup phase it is the phase's export; an event of a tile loop
that names an mbarrier names one of the thread's block and comes after six `bar.sync 0`, more
than any mbarrier needs to be published. -/
theorem use_ev (hC : ComputeOwes P L X) (hS : StoreOwes P L X) {k : Nat} {e : Event} {m : Loc}
    (he : X.get (g, k) = some e) (hm : Frame.MbarOf e m) (hni : ∀ n, e.kind ≠ .mbInit m n) :
    ∃ b : Bar, m = b.loc L (g / L.block) ∧
      (b.gen + 1 ≤ bar0Before X (g, k) ∨
        g = b.owner L (g / L.block) ∧
          ∃ j pcj, j < k ∧ X.get (g, j) = some ⟨pcj, .mbInit m b.count⟩) := by
  have hg := Frame.lt_of_get hX he
  have hne : ∀ f, e.kind ≠ .ub f := by
    intro f hk
    obtain ⟨pc, kd⟩ := e
    cases hk
    exact hm.elim
  obtain ⟨s, hs, hst, hub, -⟩ := event_site hpre hX he hne
  rcases mbarOf_pc hpre hX he hs hm with hlo | ⟨h1, h2⟩
  · have hI := hst.of_pc_startup (by omega)
    exact (Startup.use_ev_startup hpre hX hg he hs hm hni).resolve_right hI.inv.not_left
  · have hb6 : bar0Before X (g, k) = 6 := by
      rw [bar0Before_eq]
      exact (hst.bar0_bounds hub).2.2.2.2.1 h1 (by omega)
    suffices h : ∃ b : Bar, m = b.loc L (g / L.block) by
      obtain ⟨b, hb⟩ := h
      exact ⟨b, hb, .inl (by have := gen_le b; omega)⟩
    by_cases hp : s.site.pc ≤ 2105
    · obtain ⟨hw, j0, s0, -, -, -, hI⟩ := hst.of_pc_producer h1 hp
      exact producer_mbar hpre hX hg hw he hs hI hm
    · by_cases hc : s.site.pc ≤ 2944
      · obtain ⟨hr, j0, s0, -, -, -, hI⟩ := hst.of_pc_compute (by omega) hc
        exact hC.mbar hs hI he hm
      · obtain ⟨hw, j0, s0, -, -, -, hI, -⟩ := hst.of_pc_store (by omega) h2
        exact hS.mbar hs (hI hub) he hm

/-! ### Lifetimes (`Protocol.LifeFacts`) -/

/-- `LifeFacts.store_wait`. A tensor store is one of the store leader's loop or one of the
epilogue. In the epilogue the group wait of instruction 3833 follows it; in the loop the group
wait of its tile follows it before the loop's exit, which is before the thread's `ret`. -/
theorem store_wait (hS : StoreOwes P L X) {k j pc al pcx : Nat} {sp : TensorStore.Spec}
    (he : X.get (g, k) = some ⟨pc, .tensorStore al sp⟩)
    (hx : X.get (g, j) = some ⟨pcx, .exit⟩) :
    ∃ w, k < w ∧ w < j ∧ BulkWaitsFor X .read (g, k) (g, w) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨s, hs, hst, hub, -⟩ := event_site hpre hX he (fun f h => by cases h)
  obtain ⟨i, hi, h226⟩ := tensorStore_site (sounds hpre) hX he hs rfl
  have hlo : 2944 < s.site.pc := by
    rw [hi]
    exact tensorStore_pc i h226
  by_cases hp : s.site.pc ≤ 3112
  · obtain ⟨hw, j1, s1, past1, hj1, hin, hI, -⟩ := hst.of_pc_store hlo hp
    obtain ⟨sx, hsx, hstx, hubx, -⟩ := event_site hpre hX hx (fun f h => by cases h)
    obtain ⟨-, hpcx⟩ := exit_site_pc (sounds hpre) hX hx hsx rfl
    obtain ⟨j0, s0, past, hj0, -, -⟩ := hstx.of_pc_epilogue (by omega) (.inl hubx)
    have h5 := (warp_eq5_iff g).mp hw
    obtain ⟨j2, s2, -, -, ⟨hc, -⟩ | ⟨hw4, -⟩ | ⟨-, -, hout, -⟩⟩ := past.entry
    · omega
    · have := (warp_eq4_iff g).mp hw4
      omega
    · obtain ⟨w, h1, h2, h3⟩ := hS.store_wait past1.state hin hj1 he hs (hI hub) past.state hout
      exact ⟨w, h1, by omega, h3⟩
  · obtain ⟨j0, s0, past, hj0, -, -⟩ := hst.of_pc_epilogue (by omega) (.inl hub)
    exact Epilogue.store_wait hpre hX hg ⟨s0, past.state, past.into⟩ hj0 he hx

/-- `LifeFacts.state_polled`: the startup's export, at the followed state of the `ret`. -/
theorem state_polled {j pcx : Nat} (he : X.get (g, j) = some ⟨pcx, .exit⟩) :
    1 ≤ okPolls (Bar.state.loc L (g / L.block)) ((X.tr g).take j) := by
  obtain ⟨s, hs, -⟩ := event_site hpre hX he (fun f h => by cases h)
  exact Startup.state_polled_startup hpre hX (Frame.lt_of_get hX he) he hs

/-- **A thread issues at most 70 loads on `loadFull st` of its block for each use of load
stage `st`** (`LifeFacts.full_issues` for every thread). One load more would be issued after
`70 * uses` loads on that mbarrier; a load of the startup completes on the state mbarrier, and
a load of the Producer phase on `loadFull` of the stage of a tile `tt` below the tile count,
after `70 * (tt / 3) + i` loads on it, which is less than `70 * uses`. -/
theorem full_issues_thread (st : Fin 3) :
    (X.tr g).countP (issuesTo ((Bar.loadFull st).loc L (g / L.block))) ≤
      70 * uses 3 (ctaTiles P (g / L.block)) st := by
  by_contra h
  have h' : 70 * uses 3 (ctaTiles P (g / L.block)) st + 1 ≤
      ((X.tr g).take (X.tr g).length).countP
        (issuesTo ((Bar.loadFull st).loc L (g / L.block))) := by
    rw [List.take_length]
    omega
  obtain ⟨i, e, -, he, hp, hcnt⟩ := exists_nthEv h'
  obtain ⟨pc, kd⟩ := e
  cases kd <;> try cases hp
  rename_i al sp
  have hmb : sp.mbar = (Bar.loadFull st).loc L (g / L.block) := of_decide_eq_true hp
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, hs, hst, hub, -⟩ := event_site hpre hX he (fun f h => by cases h)
  obtain ⟨j, hj, hlt⟩ := tensorIssue_site (sounds hpre) hX he hs rfl
  rcases tensorLoad_pc j hlt with hlo | ⟨h1, h2⟩
  · have hI := hst.of_pc_startup (by rw [hj]; omega)
    obtain ⟨q, -, -, rfl, -⟩ :=
      (Startup.issue_startup hpre hX hg he hs).resolve_right hI.inv.not_left
    have hlt3 := st.isLt
    simp only [Startup.stateSpec, loadSpec_mbar, Bar.loc, Bar.off, Loc.mk.injEq,
      hpre.sharedBase, true_and] at hmb
    omega
  · obtain ⟨hw, j0, s0, -, -, -, hI⟩ :=
      hst.of_pc_producer (by rw [hj]; exact h1) (by rw [hj]; exact h2)
    obtain ⟨pos, w, p, x, -, hr, hl, hev, -⟩ := Producer.producer_good hpre hX hg hw he hs hI
    obtain ⟨tt, ii, htt, hii, -, -, rfl, -, hcount, -⟩ := Producer.issue_shape hr hl hev
    have hm2 : (Producer.tileLoad P L g tt ii).mbar =
        (Bar.loadFull (Producer.stage tt)).loc L (g / L.block) := by
      rw [Producer.tileLoad, loadSpec_mbar, Producer.fullLoc_eq hpre]
    obtain ⟨hbar, -⟩ := Bar.loc_inj (hm2.symm.trans hmb)
    injection hbar with hstage
    subst hstage
    have hcount' : ((X.tr g).take i).countP
        (issuesTo ((Bar.loadFull (Producer.stage tt)).loc L (g / L.block))) =
          70 * (tt / 3) + ii := hcount
    have hu := div_lt_uses (n := 3) (by decide)
      (show tt < ctaTiles P (g / L.block) by rw [ctaTiles_eq hpre]; exact htt)
    have hval : (Producer.stage tt).val = tt % 3 := rfl
    rw [hcnt, hval] at hcount'
    have := Nat.mul_le_mul_left 70 (Nat.succ_le_of_lt hu)
    omega

/-- **A compute thread that exits has polled `loadFull st` of its block successfully once for
each use of load stage `st`** (`LifeFacts.full_polled` for a thread): the ledger of the Compute
phase's exit, which is before the `ret`. -/
theorem full_polled_thread {j pcx : Nat} (st : Fin 3) (hc : tid g < 128)
    (he : X.get (g, j) = some ⟨pcx, .exit⟩) :
    uses 3 (ctaTiles P (g / L.block)) st ≤
      okPolls ((Bar.loadFull st).loc L (g / L.block)) ((X.tr g).take j) := by
  obtain ⟨d, hs, hst, hub, -⟩ := event_site hpre hX he (fun f h => by cases h)
  obtain ⟨-, hpc⟩ := exit_site_pc (sounds hpre) hX he hs rfl
  obtain ⟨j0, s0, past, hj, -, -⟩ := hst.of_pc_epilogue (by omega) (.inl hub)
  obtain ⟨j1, ho⟩ := tileDone_compute past hc
  rw [ctaTiles_eq hpre, ← (compute_out ho).2 st]
  exact Flow.countP_take_mono _ _ hj

/-! ### The three contracts, from what is owed -/

/-- **`Protocol.BarFacts`**, given the Compute phase's share. -/
theorem barFacts_of (hC : ComputeOwes P L X) : BarFacts L X (ctaTiles P) where
  shape := fun _ he => bar_shape hpre hX hC he
  bar0_le := fun _ => bar0_le hpre hX hC
  bar0_exit := fun _ he => bar0_exit hpre hX he
  bar0_pc := fun _ he => bar0_pc hpre hX hC he
  bar8_pc := fun _ he => bar8_pc hpre hX hC he
  bar8_le := fun _ _ => bar8_le hpre hX hC
  bar8_exit := fun _ hc he => bar8_exit hpre hX hC hc he
  sched := fun _ he => bar_sched hpre hX hC he

/-- **`Protocol.InitFacts`**, given the shares of the Compute phase and the Store phase. -/
theorem initFacts_of (hC : ComputeOwes P L X) (hS : StoreOwes P L X) : InitFacts L X where
  init_ev := fun _ he => init_ev hpre hX he
  init_once := fun he he' => init_once hpre hX he he'
  init_done := fun b _ he hb => init_done hpre hX b he hb
  use_ev := fun _ he hm hni => use_ev hpre hX hC hS he hm hni

/-- **`Protocol.LifeFacts`**, given the Store phase's share. -/
theorem lifeFacts_of (hS : StoreOwes P L X) : LifeFacts L X (ctaTiles P) where
  store_wait := fun he hx => store_wait hpre hX hS he hx
  state_polled := fun _ he => state_polled hpre hX he
  full_issues := fun {c} st _ => by
    have h := full_issues_thread hpre hX (g := loadLeader L c) st
    rwa [show loadLeader L c / L.block = c from thr_div hpre.block (by decide)] at h
  full_polled := fun {c j pcx} st a _ he => by
    have ha := a.isLt
    have ht : tid (computeThread L c a) < 128 := by
      rw [← block_mod hpre, computeThread, thr_mod hpre.block (by omega)]
      exact ha
    have h := full_polled_thread hpre hX st ht he
    rwa [computeThread_div hpre.block a] at h

end

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly.FactsA
