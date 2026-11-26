-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Schedule.Defs

@[expose] public section

/-!
# The contract of the reference layer for progress and termination

`RefProgress L X I` is everything the progress instance and the termination bound need to know
about the threads of one consistent execution `X` beyond the machine's own step theorems. The
reference layer (`Proof/Ref/<Phase>`) owes it, phase by phase, for the numbers `I : Nums` it
chooses (`I.tile`, `I.tiles`, `I.left`). Every field but one is about ONE thread `g`: its
machine state `d` before its `k`-th event (`Frame.stateAt (Thread.code L) X g k = some (some
d)`, a "followed state") and counts over its first `k` events. In the reference layer's terms
each such field is a line of a phase's ledger or of its position facts.

Conventions the fields fix:

* the tile index `I.tile g d` is 0 up to the last `bar.sync 0` of the startup (instruction
  1402), the count `I.tiles g` from the first `bar.sync 0` of the epilogue (3113) on, and in
  between the index of the tile the thread works on; for a compute thread it advances at the
  jump back to the loop head, so the instructions 2914 to 2944 still belong to the tile whose
  named barrier (2913) was just made;
* the counts are those of `Defs.lean`: `bar0Of`, `bar8Of`, `collOf`, `matBefore`.

The fields, by use:

* `tracked`: the machines follow the execution (passed through to the premises).
* `tile_le`, `tile_start`, `tile_end`, `tile_matrix`: the tile index.
* `bar0`, `bar8`, `coll`, `matrix`: the ledgers of barrier arrivals, warp collectives and
  matrix events.
* `arrLoadEmpty`, `arrStoreFull`, `arrLoadFull`, `arrStoreEmpty`: lower bounds on a thread's
  mbarrier arrivals (and the load leader's issued loads) by its tile index: what it has done in
  the tiles before the current one. They turn the count-level blockers of `Proof/Protocol`
  ("the leader has made at most `n` arrivals") into "the blocker is at an earlier tile".
* `poll`: at a poll state, the polled mbarrier, who polls it, the parity of the poll, and an
  upper bound on the poller's successful polls by its tile index.
* `barStep`, `exitAt`: the state after a barrier event (a later instruction, a tile index
  that is not smaller); where the exit is.
* `collShape`, `collKind`, `matrixShape`, `matrixPrev`, `deadReleased`: the library's facts
  about whole-warp events that are not counts (`Sched.WarpCollRel.shape`, `CollLead.kind`,
  `Sched.MatrixFacts.shape`, its `last`, and `Sched.WarpCollRel.dead`), word for word. The
  library's remaining fact of this kind, `Sched.WarpCollRel.released` (two lanes at the same
  collective are released together: at `shfl.sync` 87 their last events are arrivals of one
  generation of `bar.sync 0`), is no field: it needs the safety goal, which this contract does
  not have, and is derived where the safety goal is at hand (`collReleased_of`, `Lag.lean`,
  from the fields `tracked`, `bar0`, `coll`, `collAt` and the protocol layer's barrier facts).
* `left_dec`: every step lowers the counted events left by the event's count.
* `region`, `collAt`, `pollStage`, `arrState` (added last, by the assembly of the progress
  instance, which found the fields above too weak for four of its arguments):
  * `region`: which warps are at the instructions of the three tile loops. The time table
    orders the load leader's, the compute warps' and the store leader's code of one tile by
    instruction index; that is an order of the THREADS only if a compute thread is never at
    an instruction of the store leader's loop, and so on.
  * `collAt`: a collective state is at a collective position of the thread's own warp (warp 0
    alone is at the elections 61 and 93, the load warp alone at 32). Without it the count
    `collOf` does not order a lane at such a position against the other lanes of its warp.
  * `pollStage`: a poll of a "full" barrier (the compute threads' poll of `loadFull`, the
    store leader's of `storeFull`) is inside a tile and polls that tile's stage. `poll` bounds
    the successful polls by the uses of the polled stage in the earlier tiles; only when the
    current tile uses that stage does "the producer has delivered no more than that" put the
    producer at this tile or an earlier one.
  * `arrState`: once past its third `bar.sync 0` the load leader has arrived on the state
    barrier and issued the 16 loads of the initial state: a thread whose poll of the state
    barrier fails then waits for an unfinished load, or for a load leader that is earlier.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Progress

open PTX PTX.Sched PTX.Flow PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Protocol

noncomputable section

/-- **What the reference layer exports for progress and termination**, for one execution. -/
structure RefProgress (L : Launch) (mem0 : Mem0) (X : Execution) (I : Nums) : Prop where
  /-- The machines follow the execution. -/
  tracked : Frame.Tracked (Thread.code L) X
  -- The tile index.
  /-- The tile index is at most the tile count. -/
  tile_le : ∀ {g k : Nat} {d : Thread.D}, g < L.threads →
    Frame.stateAt (Thread.code L) X g k = some (some d) → I.tile g d ≤ I.tiles g
  /-- It is 0 in the startup. -/
  tile_start : ∀ {g k : Nat} {d : Thread.D}, g < L.threads →
    Frame.stateAt (Thread.code L) X g k = some (some d) → d.site.pc ≤ 1402 → I.tile g d = 0
  /-- It is the tile count in the epilogue. -/
  tile_end : ∀ {g k : Nat} {d : Thread.D}, g < L.threads →
    Frame.stateAt (Thread.code L) X g k = some (some d) → 3113 ≤ d.site.pc →
    I.tile g d = I.tiles g
  /-- A thread at a matrix event is a compute thread inside a tile. -/
  tile_matrix : ∀ {g k : Nat} {d : Thread.D}, g < L.threads →
    Frame.stateAt (Thread.code L) X g k = some (some d) → siteCls d.site = .matrix →
    g % L.block < 128 ∧ I.tile g d < I.tiles g
  -- The ledgers: counts of the thread's earlier events.
  /-- Its `bar.sync 0`. -/
  bar0 : ∀ {g k : Nat} {d : Thread.D}, g < L.threads →
    Frame.stateAt (Thread.code L) X g k = some (some d) →
    ((X.tr g).take k).countP (Execution.isBarId 0) = bar0Of d.site.pc
  /-- The named barriers of a compute thread. -/
  bar8 : ∀ {g k : Nat} {d : Thread.D}, g < L.threads →
    Frame.stateAt (Thread.code L) X g k = some (some d) → g % L.block < 128 →
    ((X.tr g).take k).countP (Execution.isBarId 8) = bar8Of d.site.pc (I.tile g d)
  /-- Its shuffles and elections. -/
  coll : ∀ {g k : Nat} {d : Thread.D}, g < L.threads →
    Frame.stateAt (Thread.code L) X g k = some (some d) →
    ((X.tr g).take k).countP isWarpColl = collOf (g % L.block / 32) d.site.pc
  /-- The matrix events of a compute thread: 182 per finished tile, and those of the current
  one. -/
  matrix : ∀ {g k : Nat} {d : Thread.D}, g < L.threads →
    Frame.stateAt (Thread.code L) X g k = some (some d) → g % L.block < 128 →
    ((X.tr g).take k).countP isMatrix = 182 * I.tile g d + matBefore d.site
  /-- A compute thread has arrived on the "empty" barrier of a load stage once per earlier tile
  of that stage. -/
  arrLoadEmpty : ∀ {g k : Nat} {d : Thread.D}, g < L.threads →
    Frame.stateAt (Thread.code L) X g k = some (some d) → g % L.block < 128 → ∀ s : Fin 3,
    uses 3 (I.tile g d) s.val ≤
      arrivals ((Bar.loadEmpty s).loc L (g / L.block)) ((X.tr g).take k)
  /-- A compute thread has arrived on the "full" barrier of a store stage once per earlier tile
  of that stage. -/
  arrStoreFull : ∀ {g k : Nat} {d : Thread.D}, g < L.threads →
    Frame.stateAt (Thread.code L) X g k = some (some d) → g % L.block < 128 → ∀ o : Fin 2,
    uses 2 (I.tile g d) o.val ≤
      arrivals ((Bar.storeFull o).loc L (g / L.block)) ((X.tr g).take k)
  /-- The load leader has made its arrival and issued its 70 loads for every earlier tile of a
  load stage. -/
  arrLoadFull : ∀ {g k : Nat} {d : Thread.D}, g < L.threads →
    Frame.stateAt (Thread.code L) X g k = some (some d) → g = loadLeader L (g / L.block) →
    ∀ s : Fin 3,
    uses 3 (I.tile g d) s.val ≤
        arrivals ((Bar.loadFull s).loc L (g / L.block)) ((X.tr g).take k) ∧
      70 * uses 3 (I.tile g d) s.val ≤
        ((X.tr g).take k).countP (issuesTo ((Bar.loadFull s).loc L (g / L.block)))
  /-- The store leader has arrived on the "empty" barrier of a store stage once per earlier
  tile of that stage. -/
  arrStoreEmpty : ∀ {g k : Nat} {d : Thread.D}, g < L.threads →
    Frame.stateAt (Thread.code L) X g k = some (some d) → g = storeLeader L (g / L.block) →
    ∀ o : Fin 2,
    uses 2 (I.tile g d) o.val ≤
      arrivals ((Bar.storeEmpty o).loc L (g / L.block)) ((X.tr g).take k)
  -- Single events.
  /-- A barrier event is made at sub-step 0 and leads to a later instruction, at a tile index
  that is not smaller. (The tile index may grow across a barrier: a lane of the load or the
  store warp that is not its leader goes from the `bar.sync 0` at 1402, tile index 0, directly
  to the one at 3113, where the tile index is the tile count.) -/
  barStep : ∀ {g k pc id : Nat} {cnt : Option Nat} {m : BarMode} {d d' : Thread.D},
    g < L.threads → Frame.stateAt (Thread.code L) X g k = some (some d) →
    X.get (g, k) = some ⟨pc, .bar id cnt m⟩ →
    Frame.stateAt (Thread.code L) X g (k + 1) = some (some d') →
    d.site.sub = 0 ∧ d.site.pc < d'.site.pc ∧ I.tile g d ≤ I.tile g d'
  /-- The exit is at the last instruction. -/
  exitAt : ∀ {g k pc : Nat} {d : Thread.D}, g < L.threads →
    Frame.stateAt (Thread.code L) X g k = some (some d) → X.get (g, k) = some ⟨pc, .exit⟩ →
    d.site.pc = 3835
  /-- **A poll state**: it polls one mbarrier `b` of the thread's block; the thread is a poller
  of `b`; it has made at most `roundOf b` successful polls of it; in the startup `b` is the
  state barrier; and every wait event the state fires is on `b`, with the parity of the
  thread's successful polls of `b` plus the barrier's offset. -/
  poll : ∀ {g k : Nat} {d : Thread.D}, g < L.threads →
    Frame.stateAt (Thread.code L) X g k = some (some d) → siteCls d.site = .poll →
    ∃ b : Bar, pollerOf L (g / L.block) b g ∧
      okPolls (b.loc L (g / L.block)) ((X.tr g).take k) ≤ roundOf b (I.tile g d) ∧
      (d.site.pc ≤ 1402 → b = .state) ∧
      ∀ {t : TState} {ins : Instr} {e : Event} {o : Option TState},
        (Thread.code L g).AtD d t → kernel.code[d.site.pc]? = some ins →
        Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) e o →
        ∀ l q ok acq sc, e.kind = .wait l q ok acq sc →
          l = b.loc L (g / L.block) ∧
            q % 2 = (okPolls l ((X.tr g).take k) + b.delta) % 2
  -- Whole-warp events: the library's facts that are not counts.
  /-- `Sched.WarpCollRel.shape`. -/
  collShape : ∃ F : Nat × Nat → Nat → Nat × CollShape,
    (∀ c n, (F c n).2.Full) ∧
    (∀ {g k : Nat} {e : Event} {d : Thread.D}, g < L.threads →
      Frame.stateAt (Thread.code L) X g k = some (some d) → X.get (g, k) = some e →
      isWarpColl e = true →
      kindShape e.kind = some (F (wkey L g) (((X.tr g).take k).countP isWarpColl)).2) ∧
    (∀ {g : Nat} {d : Thread.D} {t : TState} {m : Tmpl}, g < L.threads →
      Frame.stateAt (Thread.code L) X g (X.tr g).length = some (some d) →
      siteCls d.site = .coll → (Thread.code L g).AtD d t → (Thread.code L g).inv d →
      out kernel Assumptions.all L g t = .ev m → (∃ f, m = .ub f) ∨
        (t.pc = (F (wkey L g) ((X.tr g).countP isWarpColl)).1 ∧
          tmplShape m = some (F (wkey L g) ((X.tr g).countP isWarpColl)).2))
  /-- `CollLead.kind`: the template at a collective state is a shuffle or an election. -/
  collKind : ∀ {g : Nat} {d : Thread.D} {t : TState} {m : Tmpl} {s : CollShape},
    g < L.threads → Frame.stateAt (Thread.code L) X g (X.tr g).length = some (some d) →
    siteCls d.site = .coll → (Thread.code L g).AtD d t → (Thread.code L g).inv d →
    out kernel Assumptions.all L g t = .ev m → tmplShape m = some s → s.tag ≤ 1
  /-- `Sched.WarpCollRel.dead`: a pending thread whose machine has stopped is released (the
  machine stops only after an event that never blocks). -/
  deadReleased : ∀ {g : Nat}, Frame.Pending L X g →
    Frame.stateAt (Thread.code L) X g (X.tr g).length = none → Step.Released L X g
  /-- `Sched.MatrixFacts.shape`, with the matrix instructions of the code as the table. -/
  matrixShape : ∀ {g : Nat} {d : Thread.D} {t : TState} {m : Tmpl}, g < L.threads →
    Frame.stateAt (Thread.code L) X g (X.tr g).length = some (some d) →
    siteCls d.site = .matrix → (Thread.code L g).AtD d t →
    out kernel Assumptions.all L g t = .ev m → (∃ f, m = .ub f) ∨
      ∃ pc op own k, Proof.Top.matrixSites[(X.tr g).countP isMatrix % 182]? = some (pc, op) ∧
        t.pc = pc ∧ m = .matrix op own k
  /-- The event before a matrix event never blocks. -/
  matrixPrev : ∀ {g : Nat} {d : Thread.D}, g < L.threads →
    Frame.stateAt (Thread.code L) X g (X.tr g).length = some (some d) →
    siteCls d.site = .matrix → ∀ q, X.get (g, (X.tr g).length - 1) = some q →
    Unblocking q.kind
  -- Termination.
  /-- Every step of a followed thread lowers the counted events left by the event's count. -/
  left_dec : ∀ {g k : Nat} {d d' : Thread.D} {e : Event}, g < L.threads →
    (X.tr g)[k]? = some e → Frame.stateAt (Thread.code L) X g k = some (some d) →
    Thread.next L g d e = some (some d') →
    I.left g d' + (if e.counts then 1 else 0) ≤ I.left g d
  -- Added last (see the header): where the roles are, and two facts about polls.
  /-- **Who is inside which tile loop**: a thread at an instruction of the load leader's loop
  (1403 to 2105) is of the load warp, at one of the compute loop (2106 to 2944) a compute
  thread, at one of the store leader's loop (2945 to 3112) of the store warp. -/
  region : ∀ {g k : Nat} {d : Thread.D}, g < L.threads →
    Frame.stateAt (Thread.code L) X g k = some (some d) →
    (1402 < d.site.pc → d.site.pc ≤ 2105 → 128 ≤ g % L.block ∧ g % L.block < 160) ∧
    (2105 < d.site.pc → d.site.pc ≤ 2944 → g % L.block < 128) ∧
    (2944 < d.site.pc → d.site.pc ≤ 3112 → 160 ≤ g % L.block)
  /-- **A collective state is at a collective position of the thread's warp** (`collPcs`). -/
  collAt : ∀ {g k : Nat} {d : Thread.D}, g < L.threads →
    Frame.stateAt (Thread.code L) X g k = some (some d) → siteCls d.site = .coll →
    d.site.pc ∈ collPcs (g % L.block / 32)
  /-- **A poll of a "full" barrier is inside a tile and polls the tile's stage**: a wait event
  that a poll state fires on `loadFull s` (a compute thread's) has `s` = the tile index modulo
  3, one on `storeFull s` (the store leader's) has `s` = the tile index modulo 2, and in both
  cases the tile index is below the tile count. -/
  pollStage : ∀ {g k : Nat} {d : Thread.D}, g < L.threads →
    Frame.stateAt (Thread.code L) X g k = some (some d) → siteCls d.site = .poll →
    ∀ {t : TState} {ins : Instr} {e : Event} {o : Option TState},
      (Thread.code L g).AtD d t → kernel.code[d.site.pc]? = some ins →
      Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) e o →
      ∀ q ok acq sc,
        (∀ s : Fin 3, e.kind = .wait ((Bar.loadFull s).loc L (g / L.block)) q ok acq sc →
          s.val = I.tile g d % 3 ∧ I.tile g d < I.tiles g) ∧
        (∀ s : Fin 2, e.kind = .wait ((Bar.storeFull s).loc L (g / L.block)) q ok acq sc →
          s.val = I.tile g d % 2 ∧ I.tile g d < I.tiles g)
  /-- **The load leader past its third `bar.sync 0`** (instruction 379) has arrived on the state
  barrier and issued the 16 loads of the initial state. -/
  arrState : ∀ {g k : Nat} {d : Thread.D}, g < L.threads →
    Frame.stateAt (Thread.code L) X g k = some (some d) → g = loadLeader L (g / L.block) →
    379 < d.site.pc →
    1 ≤ arrivals (Bar.state.loc L (g / L.block)) ((X.tr g).take k) ∧
      16 ≤ ((X.tr g).take k).countP (issuesTo (Bar.state.loc L (g / L.block)))

end

end PTX.Kernels.FlashKdaFwd.Proof.Progress
