-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Compute.Tables

@[expose] public section

/-! # The reference invariant of the Compute phase (instructions 2106 to 2944): statement

The phase is the tile loop of a compute thread (thread index below 128 in its block). For tile
`t` of the `T` tiles of the block's sequence the thread

* polls the "empty" mbarrier of output stage `t % 2` (instruction 2144) and the "full" mbarrier
  of input stage `t % 3` (2186) until each poll succeeds;
* executes 182 warp matrix instructions (44 `ldmatrix`, 104 `mma.sync`, 16 `movmatrix`,
  18 `stmatrix`) with 18 scalar loads between them: 262 events, because an `ldmatrix` is the read
  of the lane's row followed by the matrix event, and an `stmatrix` the matrix event followed by
  the write of the lane's row;
* arrives on the named barrier `bar.sync 8, 128` (2913), executes `fence.proxy.async` (2914),
  arrives on the "full" mbarrier of output stage `t % 2` (2920) and on the "empty" mbarrier of
  input stage `t % 3` (2928).

**Positions.** A position (`Pos`) is the phase's entry (the site `bar_5`) or a pair of a tile
`t` and an index `n < 268` in the straight line of the tile's 268 events: 0 and 1 are the two
polls, 2 to 263 the events of the matrix instructions and scalar loads in program order, 264 the
named barrier, 265 the fence, 266 and 267 the two arrivals. `skOf n` is the kind of the site of
position `n` (table `skTab`). A failed poll leaves the position unchanged. The five breakpoint
sites of the phase are no positions: no state of the invariant is at one of them.

**Register facts** (`Tile`). The code of a tile assigns each of its control registers once, so
the facts of a position are a prefix of one table: `regKeys` lists the registers in program
order, `regVal P g t r` is the closed form of register `r` in tile `t` (table `regTab`), and at
position `n` the first `cntOf n` registers hold the 64-bit words of their closed forms (`Regs`).
The first seven registers of the table are the ones carried around the loop: the loop counter
`%r1800` (the tile minus the number of tiles, as a 32-bit word), the parity `%r1801` and the
stage `%r1802` of the input pipeline, the parity `%r1803` and the stage `%r1804` of the output
pipeline, the gate offset `%r1641` and the election flag `%r180`. Besides the registers: the
role (`tid g < 128`), the tile is one of the sequence's (`t < T`), and the three flags that keep
the thread away from the breakpoints (`%p71`, `%p73`; `%p72` from the first poll's success on).
The data registers (the 128 carries and everything computed from memory) are opaque values of
the thread machine and have no fact; the one opaque slot with a fact is `remAddr32` at the last
position, the pointer `mapa` returns for the last arrival (`remPtr`).

**Ledger** (`led`): a function of the position, in the form `ledAt` of `Interface.lean`: at
position `n` of tile `t` the thread has polled the "empty" output mbarrier for `t` tiles and
once more if `n ≥ 1`, the "full" input mbarrier for `t` tiles and once more if `n ≥ 2`, made
`t` named barriers and one more if `n ≥ 265`, arrived on the "full" output mbarrier for `t`
tiles and once more if `n = 267`, arrived on the "empty" input mbarrier for `t` tiles, and made
`182 t + matOf n` matrix events.

**Counted events** (`Pos.idx`). An event *counts* (`Event.counts`) unless it is a failed poll.
The invariant also states how many counted events the thread has made since the entry:
`1 + 268 t + n` at position `n` of tile `t`. The number is strictly increasing along the
phase, so it identifies the position of every earlier event; the exports use it to find, for
an event of the thread, the earlier events that the contracts ask for (the fence between an
access and an arrival, the row writes before an arrival). The count is relative to the entry
(the trace position `j0` of the state at `bar_5`), so that the entry condition does not have to
state an absolute number.

Abbreviations: `T = tilesOf P g`, `S = P.sharedBase`, `W n` the 64-bit word of the number `n`.
Register ids are those of the generated thread machine (`%rN` is `306 + N`, `%pN` is `N`). -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Compute
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section

/-! ### The tables as functions -/

/-- The kind of the site of position `n` of a tile. -/
def skOf (n : Nat) : SK := skTab.getD n (.wait 7)

/-- The matrix events of the tile made before position `n`. -/
def matOf (n : Nat) : Nat := matTab.getD n 0

/-- The number of registers of `regKeys` assigned when the thread is at position `n`. -/
def cntOf (n : Nat) : Nat := cntTab.getD n 0

/-! ### Positions -/

/-- The positions of the phase. -/
inductive Pos where
  /-- The entry: `bar_5` (instruction 1402), before its event. -/
  | entry
  /-- Position `n` (below 268) of tile `t`. -/
  | tile (t n : Nat)
  deriving DecidableEq

/-- The site of a state at a position. -/
def Pos.At : Pos → Site → Prop
  | .entry, s => s = .bar 5
  | .tile _ n, s => (skOf n).At s

/-- The counted events (all events but failed polls) between the entry and a position. -/
def Pos.idx : Pos → Nat
  | .entry => 0
  | .tile t n => 1 + 268 * t + n

/-! ### Register facts -/

/-- **The registers `keys` hold the words of their closed forms `val`.** -/
def Regs (keys : List Nat) (val : Nat → Nat) (w : Nat → BitVec 64) : Prop :=
  ∀ r ∈ keys, w r = W (val r)

/-- The pointer that `mapa` (instruction 2927) writes to the register `remAddr32` (opaque slot
3434) for the "empty" mbarrier of the input stage of tile `t`: a 32-bit shared pointer into the
thread's own block (a block is its own cluster). -/
def remPtr (P : Params) (L : Launch) (g t : Nat) : Value :=
  mapaVal L g ⟨.shared, g / L.block, P.sharedBase + 8 * (t % 3) + 98328⟩

/-- **The facts of position `n` of tile `t`**, about the word file `w`, the predicate file `p`
and the opaque slots `x` of the state: the thread is a compute thread, the tile is one of its
sequence's, the registers assigned so far hold their closed forms, the flags `%p71`
(`not %p83`), `%p73` (`not (%p84 or %p85)`) and, after the first poll, `%p72`
(`%tid.x < 128`) are true, and at the last position the slot of `remAddr32` holds the pointer
to the mbarrier of the last arrival. -/
structure Tile (P : Params) (L : Launch) (g t n : Nat) (w : Nat → BitVec 64) (p : Nat → Bool)
    (x : Nat → Value) : Prop where
  compute : tid g < 128
  lt : t < tilesOf P g
  pos : n < 268
  regs : Regs (regKeys.take (cntOf n)) (regVal P g t) w
  p71 : p 71 = true
  p73 : p 73 = true
  p72 : 1 ≤ n → p 72 = true
  rem : n = 267 → x 3434 = remPtr P L g t

/-- **The registers at a position.** -/
def AtPos (P : Params) (L : Launch) (g : Nat) : Pos → D → Prop
  | .entry, d => Entry P g d
  | .tile t n, d => Tile P L g t n d.w d.p d.x

/-- **The reference invariant of a state at a position.** -/
structure RefAt (P : Params) (L : Launch) (g : Nat) (pos : Pos) (d : D) : Prop where
  site : pos.At d.site
  facts : AtPos P L g pos d

/-! ### The ledger -/

/-- 1 from position `k` on, 0 before. -/
def ind (k n : Nat) : Nat := if k ≤ n then 1 else 0

/-- **The ledger before a position.** -/
def led : Pos → Led
  | .entry => ledEntry
  | .tile t n =>
    ledAt (t + ind 1 n) (t + ind 2 n) (t + ind 265 n) (t + ind 267 n) t (182 * t + matOf n)

variable (P : Params) (L : Launch) (X : Execution) (g : Nat)

/-- The counted events of thread `g` among its events `j0` to `k - 1`. -/
def counted (j0 k : Nat) : Nat := (((X.tr g).take k).drop j0).countP Event.counts

/-- **The invariant of the Compute phase** before the thread's event `k`, for a thread whose
state before its event `j0` was the phase's entry: the state is at a position with that
position's register facts, the ledger of the first `k` events is the position's, and the
counted events since the entry are the position's. -/
def Inv (j0 k : Nat) (d : D) : Prop :=
  ∃ pos, RefAt P L g pos d ∧ ledOf L (g / L.block) ((X.tr g).take k) = led pos ∧ j0 ≤ k ∧
    counted X g j0 k = pos.idx

/-- **The exit condition of the Compute phase** before the thread's event `k`: the state at
`bar_7` with the exit's registers, the exit's ledger, and `1 + 268 T` counted events since the
entry (the sixth `bar.sync 0` and 268 per tile). -/
def Out (j0 k : Nat) (d : D) : Prop :=
  Exit P g d ∧ ledOf L (g / L.block) ((X.tr g).take k) = ledExit P g ∧ j0 ≤ k ∧
    counted X g j0 k = 1 + 268 * tilesOf P g

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Compute
