-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Store.Interface

@[expose] public section

/-! # Store phase: positions, the invariant and the exit condition

The store leader (lane 0 of the store warp, thread index 160 of its block) runs one iteration
of the tile loop per tile `t` of its sequence (`t < tiles len`, `len` the sequence's length):

* it polls the "store full" mbarrier of output stage `t % 2` with parity `t / 2 % 2` until the
  poll succeeds (`Pos.wait`);
* a **full tile** (`16 * t + 16 ≤ len`) is written with 16 tensor stores through the tensor map
  `tma_store_out` (`Pos.ts t i`, one per block of 8 features) and a bulk-group commit
  (`Pos.commit`);
* a **partial tile** is written row by row (`row < len - 16 * t`) and, in a row, in 16 chunks
  of 8 features (`c < 16`): one vector load of four 32-bit words from the stage buffer (four
  element reads: `Pos.ld0` to `Pos.ld3`, which carry the values already read, as the machine's
  sites do) and eight 16-bit stores to the output array (`Pos.gst t row c j`);
* then it waits for its bulk group (`Pos.bwait`) and arrives on the "store empty" mbarrier of
  the stage (`Pos.arrive`).

A position is a site together with the ghost indices `t`, `row`, `c` of the loops; `Pos.entry`
is the entry of the phase (the site `bar_5`), which every thread of the store warp passes.

* `AtPos P g pos d`: the registers of the state `d` at the position, in closed form. `Tile`
  holds the registers of the tile loop: `%r20` (the number of tiles), `%r1805` (the tokens
  left, `len - 16 * t`), `%r1806` (`t`), `%r1807` (the poll parity), `%r1808` (the stage) and
  the fifteen feature coordinates `8, 16, …, 120` (`%r779` to `%r808`: products with the stride
  word of the tensor-map object, which the launch precondition fixes to 1).
* `led len pos`: the ledger before the position (`Interface.lean`), a function of the
  position.
* `Inv`, `Exit`, `Out`: the invariant before a thread's event, the state at the phase's exit
  (the site `bar_7`, instruction 3113) and the exit condition with its ledger. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Store
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section

/-- A position of the store phase: a site with the ghost loop indices (tile `t`, row `row` and
chunk `c` of a partial tile) and, inside a vector load, the elements already read. -/
inductive Pos where
  | entry
  | wait (t : Nat)
  | ts (t : Nat) (i : Fin 16)
  | commit (t : Nat)
  | ld0 (t row c : Nat)
  | ld1 (t row c : Nat) (v0 : Value)
  | ld2 (t row c : Nat) (v0 v1 : Value)
  | ld3 (t row c : Nat) (v0 v1 v2 : Value)
  | gst (t row c : Nat) (j : Fin 8)
  | bwait (t : Nat)
  | arrive (t : Nat)

/-- The site of a position. -/
def Pos.site : Pos → Site
  | .entry => .bar 5
  | .wait _ => .mbarWait 9
  | .ts _ i => .tensorCopy ⟨226 + i.val, by have := i.isLt; omega⟩
  | .commit _ => .bulkCommit 0
  | .ld0 .. => .load 177
  | .ld1 _ _ _ v0 => .loadEl1 0 v0
  | .ld2 _ _ _ v0 v1 => .loadEl2 0 v0 v1
  | .ld3 _ _ _ v0 v1 v2 => .loadEl3 0 v0 v1 v2
  | .gst _ _ _ j => .store ⟨10 + j.val, by have := j.isLt; omega⟩
  | .bwait _ => .bulkWait 0
  | .arrive _ => .mbarArrive 6

/-- The fifteen feature coordinates `8 * i` of the tensor stores 1 to 15 (`%r779`, `%r782`, …,
`%r808`). -/
def Mult (d : D) : Prop :=
  d.w 1085 = W 8 ∧ d.w 1088 = W 16 ∧ d.w 1090 = W 24 ∧ d.w 1092 = W 32 ∧ d.w 1094 = W 40 ∧
  d.w 1096 = W 48 ∧ d.w 1098 = W 56 ∧ d.w 1100 = W 64 ∧ d.w 1102 = W 72 ∧ d.w 1104 = W 80 ∧
  d.w 1106 = W 88 ∧ d.w 1108 = W 96 ∧ d.w 1110 = W 104 ∧ d.w 1112 = W 112 ∧ d.w 1114 = W 120

/-- **The registers of the tile loop** in iteration `t`, for the store leader: `%r20` (the
number of tiles), `%r1805` (the tokens left), `%r1806` (the tile), `%r1807` (the parity of the
next poll), `%r1808` (the output stage), and the feature coordinates. -/
def Tile (P : Params) (g t : Nat) (d : D) : Prop :=
  lane g = 0 ∧ t < tiles (P.length (seqOf P g)) ∧
  d.w 326 = W (tiles (P.length (seqOf P g))) ∧ d.w 2111 = W (P.length (seqOf P g) - 16 * t) ∧
  d.w 2112 = W t ∧ d.w 2113 = W (t / 2 % 2) ∧ d.w 2114 = W (t % 2) ∧ Mult d

/-- The register that holds the shared source address of tensor store `i` of a full tile
(`%r775`, `%r778`, …, `%r807`). -/
def tsSrc (i : Nat) : Nat :=
  [1081, 1084, 1087, 1089, 1091, 1093, 1095, 1097, 1099, 1101, 1103, 1105, 1107, 1109, 1111,
    1113].getD i 0

/-- The register that holds the feature coordinate of tensor store `i` (`%r776`, then the
fifteen registers of `Mult`). -/
def tsCoord (i : Nat) : Nat :=
  [1082, 1085, 1088, 1090, 1092, 1094, 1096, 1098, 1100, 1102, 1104, 1106, 1108, 1110, 1112,
    1114].getD i 0

/-- **A row of a partial tile** `t`, at chunk `c` of row `row`: the tile is partial, the row
counter `%r1809`, the shared address of the chunk `%r1810` (stage buffer `t % 2`, row `row`,
features `8 * c` to `8 * c + 7`: 16 bytes at offset `86912 + 4096 * (t % 2) + 16 * row +
256 * c` of the block's window), the feature counter `%r1811`, and `%rd1168`: the address of
feature `8 * c + 4` of the output row of token `16 * t + row` (the eight stores address it with
displacements `-8` to `6`). -/
def Row (P : Params) (g t row c : Nat) (d : D) : Prop :=
  P.length (seqOf P g) < 16 * t + 16 ∧ row < P.length (seqOf P g) - 16 * t ∧ c < 16 ∧
  d.w 2115 = W row ∧
  d.w 2116 = W (P.sharedBase + 4096 * (t % 2) + 16 * row + 86912 + 256 * c) ∧
  d.w 2117 = W (8 * c) ∧
  d.w 3414 = W (P.outputBase + 256 * ((firstToken P.length (seqOf P g) + (16 * t + row)) *
    P.heads + headOf P g) + 16 * c + 8)

/-- **The registers at a position**, in closed form. -/
def AtPos (P : Params) (g : Nat) : Pos → D → Prop
  | .entry, _ => True
  | .wait t, d => Tile P g t d ∧ d.w 1074 = W (P.sharedBase + 8 * (t % 2) + 98352) ∧
      d.w 1076 = W (8 * (t % 2))
  | .ts t i, d => Tile P g t d ∧ 16 * t + 16 ≤ P.length (seqOf P g) ∧
      d.w 1083 = W (16 * t + firstToken P.length (seqOf P g)) ∧ d.w 1086 = W (headOf P g) ∧
      d.w 1117 = W (P.sharedBase + 4096 * (t % 2)) ∧ d.w 1082 = W 0 ∧
      d.w (tsSrc i.val) = W (P.sharedBase + 4096 * (t % 2) + 86912 + 256 * i.val)
  | .commit t, d => Tile P g t d ∧ 16 * t + 16 ≤ P.length (seqOf P g)
  | .ld0 t row c, d => Tile P g t d ∧ Row P g t row c d
  | .ld1 t row c _, d => Tile P g t d ∧ Row P g t row c d
  | .ld2 t row c _ _, d => Tile P g t d ∧ Row P g t row c d
  | .ld3 t row c _ _ _, d => Tile P g t d ∧ Row P g t row c d
  | .gst t row c _, d => Tile P g t d ∧ Row P g t row c d
  | .bwait t, d => Tile P g t d ∧ d.p 66 = true
  | .arrive t, d => Tile P g t d ∧
      d.x 3436 = .ptr 32 false (.shared (cta g) (cta g))
        (W (P.sharedBase + 8 * (t % 2) + 98368))

/-- **The reference invariant of a state at a position.** -/
structure RefAt (P : Params) (g : Nat) (pos : Pos) (d : D) : Prop where
  site : d.site = pos.site
  keep : Keep P g d
  pos : AtPos P g pos d

/-- **The state at the exit of the store phase**: the site `bar_7` (instruction 3113, a
`bar.sync 0`), before its event, for a thread of the store warp: the inherited registers,
`%r1736` (the thread index, read again) and `%p77` (the thread is not a compute thread). -/
structure Exit (P : Params) (g : Nat) (d : D) : Prop where
  site : d.site = .bar 7
  keep : Keep P g d
  tid' : d.w 2042 = W (tid g)
  role : d.p 77 = true

/-! ### The ledger -/

instance : Add Led := ⟨fun a b =>
  ⟨a.bars + b.bars, a.pollS + b.pollS, a.pollF0 + b.pollF0, a.pollF1 + b.pollF1,
    a.arrE0 + b.arrE0, a.arrE1 + b.arrE1, a.tstores + b.tstores, a.commits + b.commits,
    a.waits + b.waits, a.gstores + b.gstores⟩⟩

theorem Led.add_def (a b : Led) : a + b =
    ⟨a.bars + b.bars, a.pollS + b.pollS, a.pollF0 + b.pollF0, a.pollF1 + b.pollF1,
      a.arrE0 + b.arrE0, a.arrE1 + b.arrE1, a.tstores + b.tstores, a.commits + b.commits,
      a.waits + b.waits, a.gstores + b.gstores⟩ := rfl

/-- The ledger of one event of thread `g`. -/
def ledEv (P : Params) (g : Nat) (e : Event) : Led :=
  ⟨if Execution.isBarId 0 e then 1 else 0, if okPoll (stateBar P g) e then 1 else 0,
    if okPoll (fullBar P g 0) e then 1 else 0, if okPoll (fullBar P g 1) e then 1 else 0,
    if arrivesOn (emptyBar P g 0) e then 1 else 0, if arrivesOn (emptyBar P g 1) e then 1 else 0,
    if isTStore e then 1 else 0, if isCommit e then 1 else 0, if isBWait e then 1 else 0,
    if isGWrite e then 1 else 0⟩

/-- The ledger of the store leader after the poll of tile `t` succeeded, with `ts` tensor
stores, `cm` commits, `wt` bulk-group waits and `gs` global writes made: six `bar.sync 0`, the
poll of the state mbarrier, the polls of the tiles `0` to `t` (the even tiles poll the "store
full" mbarrier of stage 0, the odd ones that of stage 1) and the arrivals of the tiles before
`t`. -/
def ledIn (t ts cm wt gs : Nat) : Led :=
  ⟨6, 1, (t + 2) / 2, (t + 1) / 2, (t + 1) / 2, t / 2, ts, cm, wt, gs⟩

/-- **The ledger before a position** (`len`: the length of the thread's sequence). The tiles
before `t` are full: each made 16 tensor stores, one commit and one bulk-group wait. -/
def led (len : Nat) : Pos → Led
  | .entry => ledEntry
  | .wait t => ⟨6, 1, (t + 1) / 2, t / 2, (t + 1) / 2, t / 2, 16 * t, t, t, 0⟩
  | .ts t i => ledIn t (16 * t + i.val) t t 0
  | .commit t => ledIn t (16 * t + 16) t t 0
  | .ld0 t row c => ledIn t (16 * t) t t (8 * (16 * row + c))
  | .ld1 t row c _ => ledIn t (16 * t) t t (8 * (16 * row + c))
  | .ld2 t row c _ _ => ledIn t (16 * t) t t (8 * (16 * row + c))
  | .ld3 t row c _ _ _ => ledIn t (16 * t) t t (8 * (16 * row + c))
  | .gst t row c j => ledIn t (16 * t) t t (8 * (16 * row + c) + j.val)
  | .bwait t => if 16 * t + 16 ≤ len then ledIn t (16 * t + 16) (t + 1) t 0
      else ledIn t (16 * t) t t (128 * (len - 16 * t))
  | .arrive t => if 16 * t + 16 ≤ len then ledIn t (16 * t + 16) (t + 1) (t + 1) 0
      else ledIn t (16 * t) t (t + 1) (128 * (len - 16 * t))

/-- **The ledger at the exit**: the store leader of a sequence of `len ≥ 1` tokens, with
`n = tiles len` tiles, has polled and arrived once per tile, stored the `len / 16` full tiles
by tensor stores and the `len % 16` rows of a partial last tile by `128` global writes each;
every other thread of the store warp (and the leader of an empty sequence) made only the sixth
`bar.sync 0`. -/
def ledExit (P : Params) (g : Nat) : Led :=
  if lane g = 0 ∧ 1 ≤ P.length (seqOf P g) then
    ⟨6, 1, (tiles (P.length (seqOf P g)) + 1) / 2, tiles (P.length (seqOf P g)) / 2,
      (tiles (P.length (seqOf P g)) + 1) / 2, tiles (P.length (seqOf P g)) / 2,
      16 * (P.length (seqOf P g) / 16), P.length (seqOf P g) / 16,
      tiles (P.length (seqOf P g)), 128 * (P.length (seqOf P g) % 16)⟩
  else ⟨6, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩

variable (P : Params) (X : Execution) (g : Nat)

/-- **The invariant of the store phase** before the thread's event `k`. -/
def Inv (k : Nat) (d : D) : Prop :=
  ∃ pos, RefAt P g pos d ∧ ledOf P g ((X.tr g).take k) = led (P.length (seqOf P g)) pos

/-- **The exit condition of the store phase** before the thread's event `k`. -/
def Out (k : Nat) (d : D) : Prop :=
  Exit P g d ∧ ledOf P g ((X.tr g).take k) = ledExit P g

/-- The entry condition is the invariant at the entry position. -/
theorem In.inv {k : Nat} {d : D} (h : In P X g k d) : Inv P X g k d :=
  ⟨.entry, ⟨h.1.site, h.1.keep, trivial⟩, h.2⟩

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Store
