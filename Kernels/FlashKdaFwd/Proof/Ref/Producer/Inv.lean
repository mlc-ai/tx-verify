-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Producer.Tables

@[expose] public section

/-! # The reference invariant of the Producer phase (instructions 1403 to 2105): statement

The phase is the tile loop of the load leader (thread 128 of a block). For tile `t` of the
block's `T` tiles it polls the "empty" mbarrier of input stage `t % 3`, arrives on the "full"
mbarrier of that stage expecting 17984 bytes, and issues 70 tensor loads that complete on it;
after the last tile it polls the "empty" mbarriers of the stages `T % 3`, `(T + 1) % 3` and
`(T + 2) % 3` (the *tail*, executed for every `T`, also 0).

**How the code is laid out.** The loop is unrolled by two with a remainder, so the tile body
exists three times; we call the three bodies *copies* 0, 1, 2:

* copies 0 and 1 are the two halves of the unrolled loop (instructions 1438 to 1859); one
  iteration runs the tiles `u` (copy 0) and `u + 1` (copy 1) for an even *base index* `u` with
  `u + 2 ≤ T`;
* copy 2 (instructions 1864 to 2072) runs the last tile `u = T - 1` when `T` is odd.

**Positions.** A position (`Pos`) is a site of the phase together with the ghost indices that
say where the loop is: the copy `c`, the base index `u` and, inside a body, the load position
`i < 70`. The tile at a position of copy `c` with base index `u` is `tile c u` (`u + 1` in copy
1, `u` otherwise). `Pos.entry` is the phase's entry (the site `bar_5`), `Pos.tail j` the `j`-th
tail poll. The seven breakpoint sites of the phase are no positions: no state of the invariant
is at one of them.

**Register facts** (`AtPos`). At every position of the load leader: the registers that later
code reads, in closed form over the launch (`Params`), the thread and the ghost indices. Inside
a body: the stage-level registers of the body (`Body`: the base address of the stage's input
buffer, the address of its "full" mbarrier, the first token of the tile, the head, the constant
0, the workspace slot of the tile), the registers of the constants written so far (`Consts`),
and the two registers written for this load (`LoadAt`: the destination and the first
coordinate, by the tables of `Tables.lean`). The parity of the poll for tile `t` is `par t`
(1 for the first use of a stage, then alternating).

**Ledger** (`led`): a function of the position, in the form `ledAt` of `Interface.lean`.

Abbreviations: `S` the shared base `P.sharedBase`, `T = tilesOf P g`, `s` and `h` the sequence
and the head of the thread's block (`seqOf`, `headOf`), `cu i` the first token of sequence `i`,
`ft i` the first tile of sequence `i` (both from the startup phase), `W n` the 64-bit word of
the number `n`. Register ids are those of the generated thread machine (`%rN` is `306 + N`,
`%rdN` is `2246 + N`, `%pN` is `N`). -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Producer
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Proof.Ref.Startup (cu ft)

noncomputable section

/-! ### Positions -/

/-- The positions of the phase: sites with the ghost indices of the tile loop. -/
inductive Pos where
  /-- The entry: `bar_5` (instruction 1402), before its event. -/
  | entry
  /-- The poll of copy `c` (instructions 1443, 1650, 1869), at base index `u`. -/
  | poll (c : Fin 3) (u : Nat)
  /-- The arrival of copy `c` (instructions 1451, 1658, 1877), at base index `u`. -/
  | arrive (c : Fin 3) (u : Nat)
  /-- The tensor load at position `i` of copy `c`, at base index `u`. -/
  | load (c : Fin 3) (u : Nat) (i : Fin 70)
  /-- The `j`-th poll of the tail (instructions 2081, 2092, 2103). -/
  | tail (j : Fin 3)
  deriving DecidableEq

/-- The site of a position. -/
def Pos.site : Pos → Site
  | .entry => .bar 5
  | .poll c _ => .mbarWait ⟨c.val + 1, by omega⟩
  | .arrive c _ => .mbarArrive ⟨c.val + 1, by omega⟩
  | .load c _ i => .tensorCopy ⟨16 + (70 * c.val + i.val), by omega⟩
  | .tail j => .mbarWait ⟨j.val + 4, by omega⟩

/-- The tile that copy `c` runs at base index `u`. -/
def tile (c : Fin 3) (u : Nat) : Nat := if c.val = 1 then u + 1 else u

/-- The parity of the load leader's poll for tile `t` (for the tail: `t = T + j`): the stage
`t % 3` has been used `t / 3` times, and the first poll of an "empty" mbarrier has parity 1. -/
def par (t : Nat) : Nat := (t / 3 + 1) % 2

/-- The first coordinate of the load of the gate logits `beta` for tile `t`: the index of the
tile's first token in the `[heads, tokens]` array, rounded down to a multiple of 8 (the box of
32 elements has to start at a 16-byte boundary). -/
def betaIdx (P : Params) (g t : Nat) : Nat :=
  P.total * headOf P g + (cu P (seqOf P g) + 16 * t) -
    (P.total * headOf P g + (cu P (seqOf P g) + 16 * t)) % 8

/-! ### Register facts -/

/-- **The load leader in the tile loop**: the role (`tid g = 128`), the election flag `%r180`,
the role flags `%p88` and `%p87`, the two flags of the lane-0 check (`%p1 = %p85 ∨ %p86`,
`%p2` = "lane 0 or not elected"), the scale of the first coordinate of `v` (`%r15`, the word at
offset 128 of parameter object 0), the workspace slot of the block's first tile (`%r16`) and the
block's first token (`%rd2`). -/
def Lead (P : Params) (g : Nat) (d : D) : Prop :=
  tid g = 128 ∧ d.w 486 = W 1 ∧ d.p 88 = false ∧ d.p 87 = false ∧ d.p 1 = false ∧
    d.p 2 = true ∧ d.w 321 = W 1 ∧
    d.w 322 = W (P.totalTiles * headOf P g + ft P (seqOf P g)) ∧ d.w 2248 = W (cu P (seqOf P g))

/-- **The unrolled loop at base index `u`** (copies 0 and 1): `u` is even and the tiles `u` and
`u + 1` exist; the number of tiles (`%r9`), the number of tokens of the batch (`%r1784`,
parameter 12) and the two loop counters (`%r1796`, `%r1797`). -/
def Loop (P : Params) (g u : Nat) (d : D) : Prop :=
  u % 2 = 0 ∧ u + 2 ≤ tilesOf P g ∧ d.w 315 = W (tilesOf P g) ∧ d.w 2090 = W P.total ∧
    d.w 2102 = W u ∧ d.w 2103 = W u

/-- **The remainder at base index `u`** (copy 2): `u` is the last tile and is even; the tile
index (`%r1797`), the parity (`%r1798`) and the stage (`%r1799`). -/
def Rem (P : Params) (g u : Nat) (d : D) : Prop :=
  u % 2 = 0 ∧ u + 1 = tilesOf P g ∧ d.w 2103 = W u ∧ d.w 2104 = W (par u) ∧
    d.w 2105 = W (u % 3)

/-- **The stage-level registers of a body** that loads tile `t`: the base address of the input
buffer of stage `t % 3` minus 32768 (register `rb`), the address of the stage's "full" mbarrier
(`rm`), the tile's first token (`rt`), the head (`rh`), the constant 0 (`rz`) and the workspace
slot of the tile (`rs`). -/
def Body (P : Params) (g t rb rm rt rh rz rs : Nat) (d : D) : Prop :=
  d.w rb = W (P.sharedBase + 18048 * (t % 3)) ∧
    d.w rm = W (P.sharedBase + 98304 + 8 * (t % 3)) ∧
    d.w rt = W (cu P (seqOf P g) + 16 * t) ∧ d.w rh = W (headOf P g) ∧ d.w rz = W 0 ∧
    d.w rs = W (P.totalTiles * headOf P g + ft P (seqOf P g) + t)

/-- **The two registers written for the load at position `i`** of copy `c`, for tile `t`: the
shared destination and the first coordinate (for `beta`, position 16, `betaIdx`). -/
def LoadAt (P : Params) (g : Nat) (c : Fin 3) (t i : Nat) (d : D) : Prop :=
  d.w (dstReg (70 * c.val + i)) = W (P.sharedBase + 18048 * (t % 3) + dstAbs i) ∧
    match i with
    | 16 => d.w (c0Reg (70 * c.val + 16)) = W (betaIdx P g t)
    | _ => d.w (c0Reg (70 * c.val + i)) = W (c0Tab i)

/-- **The registers at a position.** -/
def AtPos (P : Params) (g : Nat) : Pos → D → Prop
  | .entry, d =>
    d.w 307 = W (tid g) ∧ d.p 85 = false ∧ d.p 86 = false ∧ d.p 87 = false ∧
      d.p 88 = decide (lane g ≠ 0) ∧ Startup.Scan P g d ∧
      d.w 486 = W (if lane g = 0 then 1 else 0)
  | .poll c u, d =>
    Lead P g d ∧
    match c.val with
    -- 1443: poll [%r364] with parity %r1798; %r366 = 8 * stage is read again by the arrival
    | 0 => Loop P g u d ∧ d.w 2104 = W (par u) ∧ d.w 2105 = W (u % 3) ∧
      d.w 670 = W (P.sharedBase + 98328 + 8 * (u % 3)) ∧ d.w 671 = W 10000000 ∧
      d.w 672 = W (8 * (u % 3))
    -- 1650: poll [%r479] with parity %r480; %r17 is the stage of tile `u + 1`
    | 1 => Loop P g u d ∧ d.p 37 = true ∧ d.w 323 = W ((u + 1) % 3) ∧
      d.w 786 = W (par (u + 1)) ∧ d.w 785 = W (P.sharedBase + 98328 + 8 * ((u + 1) % 3)) ∧
      d.w 787 = W 10000000 ∧ d.w 797 = W (8 * ((u + 1) % 3))
    -- 1869: poll [%r617] with parity %r1798
    | _ => Rem P g u d ∧ d.w 923 = W (P.sharedBase + 98328 + 8 * (u % 3)) ∧
      d.w 924 = W 10000000 ∧ d.w 925 = W (8 * (u % 3))
  | .arrive c u, d =>
    Lead P g d ∧
    match c.val with
    -- 1451: arrive on [%r370] expecting %r369 bytes
    | 0 => Loop P g u d ∧ d.w 2104 = W (par u) ∧ d.w 2105 = W (u % 3) ∧
      d.w 676 = W (P.sharedBase + 98304 + 8 * (u % 3)) ∧ d.w 675 = W 17984
    -- 1658: arrive on [%r494] expecting %r493 bytes
    | 1 => Loop P g u d ∧ d.p 37 = true ∧ d.w 323 = W ((u + 1) % 3) ∧
      d.w 786 = W (par (u + 1)) ∧ d.w 800 = W (P.sharedBase + 98304 + 8 * ((u + 1) % 3)) ∧
      d.w 799 = W 17984
    -- 1877: arrive on [%r623] expecting %r622 bytes
    | _ => Rem P g u d ∧ d.w 929 = W (P.sharedBase + 98304 + 8 * (u % 3)) ∧ d.w 928 = W 17984
  | .load c u i, d =>
    Lead P g d ∧
    (match c.val with
    | 0 => Loop P g u d ∧ d.p 37 = true ∧ d.w 2104 = W (par u) ∧ d.w 2105 = W (u % 3) ∧
      d.w 791 = W P.sharedBase ∧ Body P g u 793 680 682 685 681 717 d
    | 1 => Loop P g u d ∧ d.p 37 = true ∧ d.w 323 = W ((u + 1) % 3) ∧
      d.w 786 = W (par (u + 1)) ∧ Body P g (u + 1) 916 804 806 809 805 841 d
    | _ => Rem P g u d ∧ d.w 2091 = W P.total ∧ Body P g u 1043 933 935 938 934 970 d) ∧
    Consts c i.val d ∧ LoadAt P g c (tile c u) i.val d
  | .tail j, d =>
    tid g = 128 ∧ d.w 486 = W 1 ∧ d.w 1048 = W 10000000 ∧
    match j.val with
    -- 2081: poll [%r741] with parity %r1798; %r1799 is the stage `T % 3`
    | 0 => d.w 2105 = W (tilesOf P g % 3) ∧ d.w 2104 = W (par (tilesOf P g)) ∧
      d.w 1054 = W P.sharedBase ∧ d.w 1047 = W (P.sharedBase + 98328 + 8 * (tilesOf P g % 3))
    -- 2092: poll [%r743] with parity %r744; %r751 is the stage `(T + 1) % 3`
    | 1 => d.w 1057 = W ((tilesOf P g + 1) % 3) ∧ d.w 1050 = W (par (tilesOf P g + 1)) ∧
      d.w 1054 = W P.sharedBase ∧
      d.w 1049 = W (P.sharedBase + 98328 + 8 * ((tilesOf P g + 1) % 3))
    -- 2103: poll [%r745] with parity %r746
    | _ => d.w 1052 = W (par (tilesOf P g + 2)) ∧
      d.w 1051 = W (P.sharedBase + 98328 + 8 * ((tilesOf P g + 2) % 3))

/-- **The reference invariant of a state at a position.** -/
structure RefAt (P : Params) (g : Nat) (pos : Pos) (d : D) : Prop where
  site : d.site = pos.site
  pos : AtPos P g pos d

/-! ### The ledger -/

/-- **The ledger before a position.** At the entry it is the entry's; at the positions of the
load leader it is `ledAt a b n` with the tiles polled for, the tiles arrived for and the loads
issued: before the poll for tile `t` these are `t`, `t`, `70 t`; the poll adds one to the first,
the arrival to the second, each load to the third; the `j`-th tail poll has `T + j`, `T`,
`70 T`. -/
def led (P : Params) (g : Nat) : Pos → Led
  | .entry => ledEntry g
  | .poll c u => ledAt (tile c u) (tile c u) (70 * tile c u)
  | .arrive c u => ledAt (tile c u + 1) (tile c u) (70 * tile c u)
  | .load c u i => ledAt (tile c u + 1) (tile c u + 1) (70 * tile c u + i.val)
  | .tail j => ledAt (tilesOf P g + j.val) (tilesOf P g) (70 * tilesOf P g)

variable (P : Params) (L : Launch) (X : Execution) (g : Nat)

/-- **The invariant of the Producer phase** before the thread's event `k`. -/
def Inv (k : Nat) (d : D) : Prop :=
  ∃ pos, RefAt P g pos d ∧ ledOf L (g / L.block) ((X.tr g).take k) = led P g pos

/-- **The exit condition of the Producer phase** before the thread's event `k`. -/
def Out (k : Nat) (d : D) : Prop :=
  Exit P g d ∧ ledOf L (g / L.block) ((X.tr g).take k) = ledExit P g

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Producer
