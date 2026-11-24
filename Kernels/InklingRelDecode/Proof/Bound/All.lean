-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Bound.Generic
public import Kernels.InklingRelDecode.Proof.Bound.Base
public import Kernels.InklingRelDecode.Proof.Bound.DStart
public import Kernels.InklingRelDecode.Proof.Bound.ProA
public import Kernels.InklingRelDecode.Proof.Bound.Sm
public import Kernels.InklingRelDecode.Proof.Bound.Epi
public import Kernels.InklingRelDecode.Proof.Bound.Worker
public import Kernels.InklingRelDecode.Proof.Bound.Loader
public import Kernels.InklingRelDecode.Proof.Bound.Mma
public import Kernels.InklingRelDecode.Proof.Bound.WComp
public import Kernels.InklingRelDecode.Proof.Bound.DComp
public import Kernels.InklingRelDecode.Proof.Bound.Goal

@[expose] public section

/-!
# The bound layer of the Inkling kernel

`Bound.bound_goal`: consistent executions of the kernel have bounded size (`BoundGoal`), under the
premises listed below. The proof is by ranks on the machines' abstract states
(`Lemmas/Kernel/Bound.lean`'s idea, with one extension, `Generic.lean`).

## Design

* Every measure is defined on the machines' abstract states (`Site`, loop counters `i`, `n`,
  `num_iters`), never on a pc or a register. A rank counts the counted events (every event except
  a failed `try_wait`) that the state still allows on its longest path; every step of a machine
  lowers it by the step's count (`rank_step` of each file). A failed poll stays at its state and
  is not counted, so the machines may spin.
* `Epi.lean`, `ProA.lean`, `DStart.lean`: straight lines of sites. The prologue's rank is the number
  of sites declared after its own (`Site.ctorIdx`; every successor is a later site).
* `Loader.lean`, `Mma.lean`, `Sm.lean`: loops. The rank is `c (n - i)` plus the sites left in the
  iteration, `c` above the number of sites of an iteration (`22`, `30`, `91`); the invariants of the
  machines give `i < n` where the rank has to fall and `n` below a constant (`2 ^ 31`, `2 ^ 32`)
  where the rank has to be bounded. `Sm.rank` is defined over all 157 sites
  (`Sm.pos`), whether or not a site has a step lemma.
* `Worker.lean`, `WComp.lean`: the workers' dispatch loop is the one cycle of the machines. A
  rank cannot fall around a cycle, so the load of the role byte may raise it by `WComp.budget`
  (the rank of a role's first state), and a thread's counted events are at most its initial rank
  plus two plus `budget` for each such load (`Generic.lean`: `count_le_resets`, which names the
  reset by the program counter of the state the event fires from).
* `DComp.lean`: the default-partition thread, the four regions in order, each ranked above the
  next. The softmax region's first state is bounded by the invariant of the successor state that a
  sound machine's step provides (`Generic.lean` uses `Code.StepAt`'s `Good` for it).
* `Goal.lean`: `threadCode` (the default partition's or the worker's machine by `g % block`), the
  per-thread rank (`ranked`), the soundness of the machines (`threadCode_sound`), the absence of
  `cp.async.bulk` (`no_copy`, by `decide +kernel` on the code) and `bound_goal`.

## What `bound_goal` takes

* `hpre : Pre Q L mem0`.
* `hso`: `DComp.SmObligations` for the default-partition threads: `DComp.sound` is conditional on
  it. The rank itself is not.
* `htr`: `Frame.Tracked (threadCode L Q)` for every consistent execution (no machine reaches
  `some none`): the protocol layer's facts the machines list (`DCompMachine.lean`,
  `WCompMachine.lean`); the interface layer's `tracked`.
* `hR : DispatchBound L mem0 R`: **the role table protocol.** A worker thread's events at the
  load of its role byte (`Worker.Site.ldRole`) number at most `R` (the table is written twice,
  `0x01000202` then `0x03030303`, each before a `barrier.sync 1` the workers wait at: `R = 2`).
  Not proved here; recorded in the development notes ("thread-layer gaps").

The bound `N` is `Correct.terminates_of_count`'s, for the per-thread bound
`initTop + 2 + WComp.budget * R`.

## What is missing

* The three premises above come from other layers. `htr` and `DispatchBound` are protocol facts;
  `hso` is the thread layer's open obligation.
* `bound_goal` takes `threadCode`, which this directory defines from `DComp.code` and
  `WComp.code`; the interface layer's own family of machines is the same if it is this `if`.
* The bounds are machine-level (`2 ^ 31`, `2 ^ 32`), not the tighter ones `Pre` gives
  (`num_iters ≤ 2 ^ 24`): a bound needs none. Tighter bounds would need `Pre` at the machines'
  entry states, which the rank steps do not use.
-/
