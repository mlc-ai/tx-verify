-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Lib
public import Lemmas.Flow.Polls

@[expose] public section

/-! # Store phase: the ledger and the entry condition

The store phase is the loop of the store warp (thread indices 160 to 191 of a block) over the
tiles of its sequence, instructions 2945 to 3112. Its entry is the state at the site `bar_5`
(instruction 1402, a `bar.sync 0` that every thread executes), before that barrier's event: the
transition of `bar_5` leads a thread of the store warp into the phase or, when it is not the
elected lane or its sequence is empty, directly to the phase's exit.

This file states what the phase needs from the phases before it:

* `Keep P g d`: the registers the phase inherits, in closed form (`W n` is the 64-bit word of
  the number `n`): the thread index, the length and the number of tiles of the thread's
  sequence, the cluster rank, the election flag of instruction 312 and the first token of the
  sequence. The phase writes none of them, so they also hold at its exit;
* `Entry P g d`: `Keep` at the site `bar_5`;
* `Led`, `ledOf`: the **ledger** of the phase, counts of the thread's earlier events by the
  classes the protocol and safety contracts count: `bar.sync 0`, successful polls of the state
  mbarrier of the block (`stateBar`), successful polls of each of the two "store full"
  mbarriers (`fullBar`), arrivals on each of the two "store empty" mbarriers (`emptyBar`),
  tensor stores, bulk-group commits, bulk-group waits, and writes of global memory;
* `ledEntry`: the ledger at the entry: five `bar.sync 0` (instructions 85, 110, 379, 620 and
  621), one successful poll of the state mbarrier (instruction 384, the exit of the startup
  phase) and no event of the other classes;
* `In`: the two together, before the thread's event `k`. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Store
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section

/-- The state mbarrier of the thread's block (the layout's `Bar.state`): every thread polls it
once, successfully, at the end of the startup phase. -/
def stateBar (P : Params) (g : Nat) : Loc := ⟨.shared, cta g, P.sharedBase + 98384⟩

/-- The "store full" mbarrier of output stage `o` of the thread's block (the layout's
`Bar.storeFull o`): the store leader polls it before it stores the stage. -/
def fullBar (P : Params) (g o : Nat) : Loc := ⟨.shared, cta g, P.sharedBase + 98352 + 8 * o⟩

/-- The "store empty" mbarrier of output stage `o` of the thread's block (the layout's
`Bar.storeEmpty o`): the store leader arrives on it after the stage is stored. -/
def emptyBar (P : Params) (g o : Nat) : Loc := ⟨.shared, cta g, P.sharedBase + 98368 + 8 * o⟩

/-- Whether an event is the issue of a tensor store, a bulk-group commit, a bulk-group wait, a
write of global memory. -/
def isTStore (e : Event) : Bool := match e.kind with | .tensorStore .. => true | _ => false
def isCommit (e : Event) : Bool := match e.kind with | .bulkCommit => true | _ => false
def isBWait (e : Event) : Bool := match e.kind with | .bulkWait .. => true | _ => false
def isGWrite (e : Event) : Bool :=
  match e.kind with
  | .wr a _ => decide (a.loc.space = .global)
  | _ => false

/-- Counts of the classes of events the store phase accounts for. -/
structure Led where
  /-- `bar.sync 0` events. -/
  bars : Nat
  /-- Successful polls of the state mbarrier. -/
  pollS : Nat
  /-- Successful polls of the "store full" mbarrier of stage 0, of stage 1. -/
  pollF0 : Nat
  pollF1 : Nat
  /-- Arrivals on the "store empty" mbarrier of stage 0, of stage 1. -/
  arrE0 : Nat
  arrE1 : Nat
  /-- Tensor store issues. -/
  tstores : Nat
  /-- Bulk-group commits. -/
  commits : Nat
  /-- Bulk-group waits. -/
  waits : Nat
  /-- Writes of global memory. -/
  gstores : Nat
  deriving DecidableEq

/-- The ledger of a list of events of thread `g`. -/
def ledOf (P : Params) (g : Nat) (es : List Event) : Led :=
  ⟨es.countP (Execution.isBarId 0), okPolls (stateBar P g) es, okPolls (fullBar P g 0) es,
    okPolls (fullBar P g 1) es, arrivals (emptyBar P g 0) es, arrivals (emptyBar P g 1) es,
    es.countP isTStore, es.countP isCommit, es.countP isBWait, es.countP isGWrite⟩

/-- **The registers the store phase inherits and keeps**, for a thread of the store warp:
`%r1` (the thread index), `%r8` and `%r9` (the length of the thread's sequence and its number
of tiles), `%r46` (`%cluster_ctarank`), `%r180` (the flag of the election at instruction 312: 1
in lane 0) and `%rd2` (the first token of the sequence, entry `seq` of the offsets array, a
64-bit word). -/
structure Keep (P : Params) (g : Nat) (d : D) : Prop where
  store : warp g = 5
  tid : d.w 307 = W (tid g)
  len : d.w 314 = W (P.length (seqOf P g))
  tiles : d.w 315 = W (tiles (P.length (seqOf P g)))
  rank : d.w 352 = W 0
  elected : d.w 486 = W (if lane g = 0 then 1 else 0)
  first : d.w 2248 = W (firstToken P.length (seqOf P g))

/-- **The state at the entry of the store phase**: the site `bar_5` (instruction 1402), before
its event, for a thread of the store warp. -/
structure Entry (P : Params) (g : Nat) (d : D) : Prop where
  site : d.site = .bar 5
  keep : Keep P g d

/-- The ledger at the entry: five `bar.sync 0`, one successful poll of the state mbarrier,
nothing else of the phase's classes (a thread of the store warp polls and arrives on no
mbarrier of the store pipeline, issues no tensor store and writes no global byte before the
phase). -/
def ledEntry : Led := ⟨5, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩

variable (P : Params) (X : Execution) (g : Nat)

/-- **The entry condition of the store phase** before the thread's event `k`. -/
def In (k : Nat) (d : D) : Prop :=
  Entry P g d ∧ ledOf P g ((X.tr g).take k) = ledEntry

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Store
