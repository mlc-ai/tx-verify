-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Lib
public import Kernels.FlashKdaFwd.Proof.Protocol.Layout
public import Lemmas.Flow.Polls
public import Lemmas.Matrix.Instance

@[expose] public section

/-! # The Compute phase of the reference layer: entry, exit and ledger (statements)

The Compute phase is the stretch of the program from instruction 2106 to 2944: the tile loop of
the 128 *compute threads* of a thread block (thread index below 128; warps 0 to 3). For each tile
of the block's sequence a compute thread polls two mbarriers, executes 182 warp matrix
instructions with 18 scalar loads between them, arrives on the named barrier `bar.sync 8, 128`,
executes a proxy fence and arrives on two mbarriers. Its boundary with the other phases:

* **entry**: the state at the site `bar_5` (instruction 1402, a `bar.sync 0` that every thread
  executes), *before* the barrier's event (`Entry`, `ledEntry`, `In`). The phases before it
  (startup, conversion, carry load) prove it. The registers are the control registers that are
  live at `bar_5` for a compute thread and that
  the phase reads: the thread index (`%r1`), three role flags (`%p83`, `%p84`, `%p85`, all false
  for a compute thread), the results of the scan of the offsets array (`%r8`: the number of
  tokens of the block's sequence, `%r9`: its number of tiles, `%rd2`: its first token), and the
  flag of the election at instruction 312 (`%r180`, which the phase only carries to its exit).
  The 128 carry registers and every other data register are opaque values of the thread machine:
  the reference layer says nothing about them.
* **exit**: the state at the site `bar_7` (instruction 3113, the first `bar.sync 0` of the
  epilogue), before its event (`Exit`, `ledExit`). A compute thread whose sequence has no token
  goes there directly from `bar_5`.

**The ledger** (`Led`) counts the events a thread has made, by the classes that the contracts of
the protocol, value and progress layers count for a compute thread: `bar.sync 0`, the named
barrier (barrier 8), successful polls of the state mbarrier, successful polls of each of the two
"empty" mbarriers of the output stages (`Bar.storeEmpty o`) and of each of the three "full"
mbarriers of the input stages (`Bar.loadFull s`), arrivals on each of the two "full" mbarriers
of the output stages (`Bar.storeFull o`) and on each of the three "empty" mbarriers of the input
stages (`Bar.loadEmpty s`), and warp matrix events. `ledOf L c es` is the ledger of the events
`es` of a thread of block `c`.

`ledAt a b n c d m` is the ledger of a compute thread in the tile loop that has polled
successfully the "empty" output mbarrier for `a` tiles and the "full" input mbarrier for `b`
tiles, made `n` named barriers, arrived on the "full" output mbarrier for `c` tiles and on the
"empty" input mbarrier for `d` tiles, and made `m` matrix events. Tile `t` uses output stage
`t % 2` and input stage `t % 3`, so the count of a stage's mbarrier is the number of the tiles
counted that use the stage (`Protocol.uses`). Every ledger of the phase after the entry is of
this form.

Abbreviations: `T = tilesOf P g` is the number of tiles of the sequence of the thread's block;
`W n` is the 64-bit word of the number `n`. A register is named by its id in the generated
thread machine (`%rN` is `306 + N`, `%rdN` is `2246 + N`, `%pN` is `N`); the comments give its
name in the PTX. An *mbarrier* is one of the eleven 8-byte synchronization objects of a block
(`Protocol.Bar`). -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Compute
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Protocol (Bar uses)

noncomputable section

/-- The number of tiles of the sequence that the block of thread `g` works on. -/
abbrev tilesOf (P : Params) (g : Nat) : Nat := tiles (P.length (seqOf P g))

/-! ### The entry -/

/-- **The entry condition of the Compute phase**, for a compute thread: the state is at `bar_5`
(instruction 1402) and holds the thread index (`%r1`), the three role flags that the phase
reads (`%p83`, `%p84`, `%p85`: false in a compute thread), the number of tokens (`%r8`) and of
tiles (`%r9`) of the block's sequence, its first token (`%rd2`, a 64-bit word) and the flag of
the election at instruction 312 (`%r180`: 1 in lane 0 of a warp). -/
structure Entry (P : Params) (g : Nat) (d : D) : Prop where
  site : d.site = .bar 5
  compute : tid g < 128
  tid : d.w 307 = W (tid g)
  p83 : d.p 83 = false
  p84 : d.p 84 = false
  p85 : d.p 85 = false
  len : d.w 314 = W (P.length (seqOf P g))
  tiles : d.w 315 = W (tilesOf P g)
  first : d.w 2248 = W (firstToken P.length (seqOf P g))
  elected : d.w 486 = W (if lane g = 0 then 1 else 0)

/-! ### The exit -/

/-- **The exit condition of the Compute phase**, for a compute thread: the state is at `bar_7`
(instruction 3113) and holds the election flag (`%r180`), the thread index (`%r1736`, read
again at instruction 3111) and the flag "the thread index is above 127" (`%p77`, false): the
control registers live at `bar_7` for a compute thread. -/
structure Exit (P : Params) (g : Nat) (d : D) : Prop where
  site : d.site = .bar 7
  compute : tid g < 128
  elected : d.w 486 = W (if lane g = 0 then 1 else 0)
  tid : d.w 2042 = W (tid g)
  p77 : d.p 77 = false

/-! ### The ledger -/

/-- Counts of the classes of events the Compute phase accounts for. -/
structure Led where
  /-- `bar.sync 0` events. -/
  bar0 : Nat
  /-- Arrivals on the named barrier (barrier 8). -/
  bar8 : Nat
  /-- Successful polls of the state mbarrier. -/
  pollS : Nat
  /-- Successful polls of the "empty" mbarrier of output stage 0, 1. -/
  pe0 : Nat
  pe1 : Nat
  /-- Successful polls of the "full" mbarrier of input stage 0, 1, 2. -/
  pf0 : Nat
  pf1 : Nat
  pf2 : Nat
  /-- Arrivals on the "full" mbarrier of output stage 0, 1. -/
  af0 : Nat
  af1 : Nat
  /-- Arrivals on the "empty" mbarrier of input stage 0, 1, 2. -/
  ae0 : Nat
  ae1 : Nat
  ae2 : Nat
  /-- Warp matrix events. -/
  mats : Nat
  deriving DecidableEq

instance : Add Led := ⟨fun a b =>
  ⟨a.bar0 + b.bar0, a.bar8 + b.bar8, a.pollS + b.pollS, a.pe0 + b.pe0, a.pe1 + b.pe1,
    a.pf0 + b.pf0, a.pf1 + b.pf1, a.pf2 + b.pf2, a.af0 + b.af0, a.af1 + b.af1,
    a.ae0 + b.ae0, a.ae1 + b.ae1, a.ae2 + b.ae2, a.mats + b.mats⟩⟩

theorem Led.add_def (a b : Led) : a + b =
    ⟨a.bar0 + b.bar0, a.bar8 + b.bar8, a.pollS + b.pollS, a.pe0 + b.pe0, a.pe1 + b.pe1,
      a.pf0 + b.pf0, a.pf1 + b.pf1, a.pf2 + b.pf2, a.af0 + b.af0, a.af1 + b.af1,
      a.ae0 + b.ae0, a.ae1 + b.ae1, a.ae2 + b.ae2, a.mats + b.mats⟩ := rfl

/-- The ledger of the events `es` of a thread of block `c`. -/
def ledOf (L : Launch) (c : Nat) (es : List Event) : Led :=
  ⟨es.countP (Execution.isBarId 0), es.countP (Execution.isBarId 8),
    okPolls (Bar.state.loc L c) es,
    okPolls ((Bar.storeEmpty 0).loc L c) es, okPolls ((Bar.storeEmpty 1).loc L c) es,
    okPolls ((Bar.loadFull 0).loc L c) es, okPolls ((Bar.loadFull 1).loc L c) es,
    okPolls ((Bar.loadFull 2).loc L c) es,
    arrivals ((Bar.storeFull 0).loc L c) es, arrivals ((Bar.storeFull 1).loc L c) es,
    arrivals ((Bar.loadEmpty 0).loc L c) es, arrivals ((Bar.loadEmpty 1).loc L c) es,
    arrivals ((Bar.loadEmpty 2).loc L c) es, es.countP isMatrix⟩

/-- The ledger of one event of a thread of block `c`. -/
def ledEv (L : Launch) (c : Nat) (e : Event) : Led :=
  ⟨if Execution.isBarId 0 e then 1 else 0, if Execution.isBarId 8 e then 1 else 0,
    if okPoll (Bar.state.loc L c) e then 1 else 0,
    if okPoll ((Bar.storeEmpty 0).loc L c) e then 1 else 0,
    if okPoll ((Bar.storeEmpty 1).loc L c) e then 1 else 0,
    if okPoll ((Bar.loadFull 0).loc L c) e then 1 else 0,
    if okPoll ((Bar.loadFull 1).loc L c) e then 1 else 0,
    if okPoll ((Bar.loadFull 2).loc L c) e then 1 else 0,
    if arrivesOn ((Bar.storeFull 0).loc L c) e then 1 else 0,
    if arrivesOn ((Bar.storeFull 1).loc L c) e then 1 else 0,
    if arrivesOn ((Bar.loadEmpty 0).loc L c) e then 1 else 0,
    if arrivesOn ((Bar.loadEmpty 1).loc L c) e then 1 else 0,
    if arrivesOn ((Bar.loadEmpty 2).loc L c) e then 1 else 0,
    if isMatrix e then 1 else 0⟩

/-- **The ledger at the entry**: five `bar.sync 0` (instructions 85, 110, 379, 620 and 621),
one successful poll of the state mbarrier (instruction 384) and no event of the other classes:
before the tile loop a compute thread polls and arrives on no mbarrier of the two pipelines and
executes no named barrier and no matrix instruction. -/
def ledEntry : Led := ⟨5, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- **The ledger of a compute thread in the tile loop** that has polled the "empty" output
mbarrier for `a` tiles and the "full" input mbarrier for `b` tiles, made `n` named barriers,
arrived on the "full" output mbarrier for `c` tiles and on the "empty" input mbarrier for `d`
tiles, and made `m` matrix events: six `bar.sync 0`, the poll of the state mbarrier, and per
stage the tiles counted that use it. -/
def ledAt (a b n c d m : Nat) : Led :=
  ⟨6, n, 1, uses 2 a 0, uses 2 a 1, uses 3 b 0, uses 3 b 1, uses 3 b 2,
    uses 2 c 0, uses 2 c 1, uses 3 d 0, uses 3 d 1, uses 3 d 2, m⟩

/-- **The ledger at the exit**: the thread has run its `T` tiles, each with its two polls, its
named barrier, its two arrivals and its 182 matrix events (with `T = 0`: only the sixth
`bar.sync 0`). -/
def ledExit (P : Params) (g : Nat) : Led :=
  ledAt (tilesOf P g) (tilesOf P g) (tilesOf P g) (tilesOf P g) (tilesOf P g)
    (182 * tilesOf P g)

variable (P : Params) (L : Launch) (X : Execution) (g : Nat)

/-- **The entry condition of the Compute phase** before the thread's event `k`: the state at
`bar_5` with the entry's registers, and the entry's ledger for the first `k` events. -/
def In (k : Nat) (d : D) : Prop :=
  Entry P g d ∧ ledOf L (g / L.block) ((X.tr g).take k) = ledEntry

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Compute
