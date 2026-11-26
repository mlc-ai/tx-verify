-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Kinds.Count

@[expose] public section

/-! # The class of an event is determined by the kind of the site it was fired at

The phases of the reference layer (`Proof/Ref/<Phase>/`) are written independently, each with
its own ledger: the classes of events it counts along a thread's trace. Joining two phases
needs facts about classes that a phase never counted ("the startup phase makes no matrix
event", "the epilogue makes no arrival"), and the layers above need to know at which site an
event of a given kind was fired. Both come from one fact, proved here once for the whole
program, and from nothing a phase has to prove:

    theorem site_fires (hC : ∀ g < L.threads, (code L g).Sound)
        (hX : Consistent L kernel Assumptions.all mem0 X) (he : X.get (g, k) = some e)
        (hσ : Frame.stateAt (code L) X g k = some (some d)) :
        firedAt e.kind d.site.kind = true

**Words.** A *site* is an instruction that fires an event; the thread machine (`Proof/Thread`)
names it `Site.bar j`, `Site.tensorCopy j`, … (`j` is the ordinal among the sites of its kind,
in program order). The *kind* of a site (`Site.kind : Site → SiteKind`) is that constructor
name. A state `d` of the machine is at the site `d.site`; `Frame.stateAt (code L) X g k` is the
state before the `k`-th event of thread `g`, and it is *followed* when it is `some (some d)`.
The *kind* of an event is the constructor of `e.kind` (`.bar`, `.wait`, `.rd`, …,
`Core/Data/Types.lean`). `firedAt k κ` is the table "an event of kind `k` can be fired at a
site of kind `κ`". A *class* of events is a Boolean predicate `c : Event → Bool` that a
contract counts as `((X.tr g).take k).countP c`, the events of the class among the first `k`
events of thread `g`. An *mbarrier* is a memory barrier object (`mbarrier.*` instructions); a
*poll* is an `mbarrier.try_wait`; *undefined behaviour* is an event of kind `.ub`, which any
site can fire and which is a thread's last event.

**The table `firedAt`** (`Kinds/Fires.lean`):

| kind of event | kinds of sites that fire it |
|---|---|
| `.bar` (a `bar.sync`) | `bar` |
| `.wait` (a poll) | `mbarWait` |
| `.arrive` | `mbarArrive` |
| `.mbInit` | `mbarInit` |
| `.fenceMbarInit` | `fenceMbarInit` |
| `.tensorIssue` (a tensor load) | `tensorCopy` (ordinal below `firstStoreCopy` = 226) |
| `.tensorStore` | `tensorCopy` (ordinal from 226 on) |
| `.matrix` | `matrixLoadMx`, `warpMma`, `matrixMove`, `matrixStore` |
| `.shfl`, `.elect`, `.exit` | `shfl`, `elect`, `exit` |
| `.fenceProxy`, `.bulkCommit`, `.bulkWait` | `fenceProxy`, `bulkCommit`, `bulkWait` |
| `.rd` (a memory read) | `load`, `loadEl1`, `loadEl2`, `loadEl3`, `matrixLoad` |
| `.wr` (a memory write) | `store`, `matrixStoreWr` |
| `.ub` | every kind (a `trap` site fires nothing else) |
| any other kind | none: the program fires no such event at a followed state |

An `ldmatrix` fires two events, the read of its row (site `matrixLoad j`) and then the matrix
event (site `matrixLoadMx j row`); a `stmatrix` the matrix event (`matrixStore j`) and then the
write (`matrixStoreWr j row`).

**Files.**

* `Kinds/Fires.lean` (generic, 3 s): `SiteKind`, `firedAt`, `opKind` (the kind of an
  instruction at a sub-step), `fires_opKind` (an event fired by an instruction of kind `κ` is
  of a kind that `κ` can fire; from the library's classification of event templates,
  `Lemmas/Flow/Fire.lean`, and for the warp matrix instructions from their definition).
* `Kinds/Table.lean` (11 s): `Site.kind`, and `site_kind : kindAt s.sub s.pc = some s.kind`
  — the instruction at the program counter of every site is of the site's kind. One evaluated
  scan of the 3,836 instructions (`scan`), not a lookup per site.
* `Kinds/Event.lean` (2 s): `site_fires` and one lemma per kind of event.
* `Kinds/Count.lean` (4 s): the count transport.
* `Kinds/Examples.lean`: the worked examples below, against the startup phase.

## How to use it

Hypotheses everywhere: `hC : ∀ g < L.threads, (code L g).Sound` (under the precondition:
`sounds hpre`) and `hX : Consistent L kernel Assumptions.all mem0 X`. Tracking
(`Frame.Tracked`) is never assumed; where a state is needed it is a hypothesis
`hσ : Frame.stateAt (code L) X g k = some (some d)`.

**1. From an event to its site** (`Kinds/Event.lean`). With `he : X.get (g, k) = some e` and
`hσ`, and `hk` the kind of the event (`rfl` when the event is written out):

    bar_site hC hX he hσ hk          : ∃ j, d.site = .bar j
    bar_site_pc hC hX he hσ hk       : (∃ j, d.site = .bar j) ∧ d.site.sub = 0 ∧
                                         (d.site.pc ∈ Protocol.bar0Pcs ∨ d.site.pc = 2913)
    exit_site_pc hC hX he hσ hk      : d.site = .exit 0 ∧ d.site.pc = 3835
    bar0_event hC hX he hσ hpc       : e = ⟨d.site.pc, .bar 0 none .sync⟩
                                         (hpc : d.site.pc ∈ Protocol.bar0Pcs; the other way round)
    wait_site, arrive_site, mbInit_site, fenceMbarInit_site, shfl_site, elect_site,
    fenceProxy_site, bulkCommit_site, bulkWait_site                 (same shape)
    tensorIssue_site hC hX he hσ hk  : ∃ j : Fin 258, d.site = .tensorCopy j ∧ j.val < 226
    tensorStore_site hC hX he hσ hk  : ∃ j : Fin 258, d.site = .tensorCopy j ∧ 226 ≤ j.val
    matrix_site, rd_site, wr_site    : a disjunction over the kinds of the table
    matrix_site_ind hC hX he hσ hk (P := P) h1 h2 h3 h4 : P d.site

The `_ind` forms prove any property of the site from its four (five, two) cases; for a
classification of sites defined elsewhere this is one line, for example
`matrix_site_ind hC hX he hσ hk (P := fun s => siteCls s = .matrix) (fun _ _ => rfl)
(fun _ => rfl) (fun _ => rfl) (fun _ => rfl)`. `shfl_sites hpre hX` is the statement
`ShflSites L X` of the startup phase.

**2. A count that a phase did not put in its ledger** (`Kinds/Count.lean`). The count of a
class is the same at trace positions `j ≤ k` when no state in between is at a site that can
fire the class:

    count_isMatrix hC hX (hjk : j ≤ k) (hn : Frame.stateAt (code L) X g n = some (some dn))
        (hkn : k ≤ n + 1)
        (h : ∀ i d, j ≤ i → i < k → Frame.stateAt (code L) X g i = some (some d) →
          d.site.kind ∉ matrixKinds ∨ ∀ e, X.get (g, i) = some e → isMatrix e = false) :
        ((X.tr g).take k).countP isMatrix = ((X.tr g).take j).countP isMatrix

`hn` is a followed state at or after the stretch (usually `n = k`: the state at which the next
phase starts); it makes every earlier state followed (`followed_of_le`). The same for
`count_isBar`, `count_isBarId id`, `count_bar0Before`, `count_okPoll m`, `count_arrivesOn m`,
`count_issuesTo m`, `count_isShfl`, `count_isTensorStore`, `count_isCommit`, `count_isExit`;
for any class,
`count_transport_of_state hC hX hK …` with `hK : FiredOnly c K` (the tactic `fired_only [c]`
proves it for a class defined by a `match e.kind with`), `count_zero_of_state` from the start
of the trace, and `count_transport` when the states in between are given one by one.

A phase proves the premise `h` from its invariant in two steps (worked in
`Kinds/Examples.lean`, for the startup phase and matrix events):

    theorem pos_not_matrix (pos : Pos) : pos.site.kind ∉ matrixKinds := by
      cases pos <;> simp [Pos.site, Site.kind, matrixKinds]

    theorem startup_no_matrix … (hσ : Frame.stateAt (code L) X g k = some (some s))
        (hin : ∀ i < k, ∀ si, Frame.stateAt (code L) X g i = some (some si) → Inv P X g i si) :
        ((X.tr g).take k).countP isMatrix = 0 :=
      count_zero_of_state hC hX firedOnly_isMatrix hσ (Nat.le_succ k) fun i d hik hd => by
        obtain ⟨pos, hr, -⟩ := hin i hik d hd
        left
        rw [hr.site]
        exact pos_not_matrix pos

and the premise `hin` ("the states before `k` are in the phase") is what `first_exit` gives
from the phase's theorem at its first exit position: `first_exit (fun _ _ => <phase>_inv …) hk
hσ : I k s ∨ ∃ j ≤ k, ∃ s0, stateAt … j = some (some s0) ∧ E j s0 ∧ ∀ i < j, ∀ si, … → I i si`.

**3. Finer than the kind: counts per object.** An arrival, a poll or a tensor load names an
mbarrier, and a phase's closed-form event shape says which. Give the premise `h` in its second
form at those sites: the event fired there is not of the class. `okPoll_other`,
`arrivesOn_other`, `issuesTo_other` turn "the event is on mbarrier `m₁`" and `m₁ ≠ m₂` into
"it is not of the class of `m₂`"; `not_class_of_kind` settles the other sites. Example ("the
startup phase makes no successful poll of `Bar.loadEmpty st`", its one poll being on the state
barrier):

    count_zero_of_state (sounds hpre) hX (firedOnly_okPoll _) hσ (Nat.le_succ k)
      fun i d hik hd => .inr fun e he => by
        obtain ⟨pos, hr, hshape⟩ := hev i hik d e hd he   -- the phase's event shape
        by_cases hp : pos = .wait
        · subst hp
          obtain ⟨ok, rfl⟩ := hshape
          refine okPoll_other rfl fun h => ?_             -- two different offsets
          simp only [Bar.loc, Bar.off, hpre.sharedBase, Loc.mk.injEq, true_and] at h
          omega
        · refine not_class_of_kind (sounds hpre) hX (firedOnly_okPoll _) he hd ?_
          rw [hr.site]
          cases pos <;> simp [Pos.site, Site.kind] at hp ⊢

Free of any phase, from the code alone: a tensor copy on the load side fires no tensor store
and one on the store side no load issue (`isTensorStore_load`, `issuesTo_store`, by the ordinal
of the site); the event of each of the nine `bar.sync 0` is the arrival at barrier 0
(`bar0_event`), so `isBarId_bar0 hC hX he hσ hpc id : Execution.isBarId id e = (0 == id)` decides
the class "arrival at barrier `id`" there (the tenth barrier, at instruction 2913, has register
operands and is the business of its phase).

**For the assembly.** The count of a class at the end of a thread's trace is the sum over the
phases that count it; for every other phase use the transport between the phase's entry and
exit positions. With tracking and no undefined behaviour every position has a followed state
(`Frame.state_of_noUb`), so `count_transport` applies to any stretch. -/
