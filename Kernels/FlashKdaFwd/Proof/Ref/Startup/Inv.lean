-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Lib

@[expose] public section

/-! # The reference invariant of the startup phase (instructions 0 to 387): statement

The startup phase of every thread: the role flags, three shuffles of the warp index and five
elections, the initialization of the ten pipeline mbarriers by the elected lane of warp 0
(before the first and the second `bar.sync 0`), the scan of the offsets array `cu_seqlens`
(21 loads) that computes the sequence's length, its number of tiles and its first tile, the
one-shot load of the initial state by the elected lane of warp 4 (an mbarrier initialization,
an arrival expecting 65536 bytes and 16 asynchronous loads, before the third `bar.sync 0`), and
the poll of that mbarrier by every thread. The phase ends when a thread's poll succeeds: its
next site is the proxy fence at instruction 387 (`Exit`).

**Form of the invariant.** A *position* (`Pos`) is a site of the phase. `AtPos P g pos d` states
the closed forms of the registers that matter at that site, over the launch, the thread index
and, at the sites of the scan loop, a ghost number `j` (the sequence index the loop has
reached). `RefAt P g pos d` adds the site of the state and the facts that hold from the entry on
(`Base`). `Led` is the ledger of a position: how many events of five classes the thread has
performed before it (`bar.sync 0`, mbarrier initializations, arrivals, asynchronous load
issues, successful polls, shuffles), a function of the position and of the thread's role.
`Inv` puts the
three together for a trace position `k`.

Abbreviations: `S` is the shared base `P.sharedBase`, `B` the address of the offsets array,
`s = seqOf P g` the sequence and `h = headOf P g` the head of the thread's block, `cu i` entry
`i` of the offsets array (the first token of sequence `i`), `ft i` the number of tiles of the
sequences before `i`. `W n` is the 64-bit word of the number `n`. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Startup
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section

/-- Entry `i` of the offsets array: the first token of sequence `i`. -/
abbrev cu (P : Params) (i : Nat) : Nat := firstToken P.length i
/-- The number of tiles of the sequences before `i` (the kernel's `tile_base` for `i`). -/
abbrev ft (P : Params) (i : Nat) : Nat := firstTile P.length i

/-! ### Positions -/

/-- The sites of the startup phase. -/
inductive Pos where
  | elect (j : Fin 5)
  | shfl (j : Fin 3)
  | init (j : Fin 11)
  | fence (j : Fin 3)
  | bar (j : Fin 3)
  | load (j : Fin 21)
  | arrive
  | copy (j : Fin 16)
  | wait
  deriving DecidableEq

/-- The site of a position. -/
def Pos.site : Pos → Site
  | .elect j => .elect j
  | .shfl j => .shfl j
  | .init j => .mbarInit j
  | .fence j => .fenceMbarInit j
  | .bar j => .bar ⟨j.val, by omega⟩
  | .load j => .load ⟨j.val, by omega⟩
  | .arrive => .mbarArrive 0
  | .copy j => .tensorCopy ⟨j.val, by omega⟩
  | .wait => .mbarWait 0

/-! ### Facts -/

/-- **Facts that hold from the entry on**: the thread index, the warp index and the pointer
to the offsets array (registers `%r1`, `%r2`, `%rd1`). -/
structure Base (P : Params) (g : Nat) (d : D) : Prop where
  tid : d.w 307 = W (tid g)
  warp : d.w 308 = W (warp g)
  offs : d.w 2247 = W P.offsetsBase

/-- The six role flags `%p83` to `%p88` of a predicate file. -/
def flagsOf (p : Nat → Bool) : Bool × Bool × Bool × Bool × Bool × Bool :=
  (p 83, p 84, p 85, p 86, p 87, p 88)

/-- The role flags of a thread by its class: compute (`tid < 128`), load warp
(`128 ≤ tid < 160`, where `%p88` says "this lane is not the elected one"), store warp. -/
def roleFlags (g : Nat) : Bool × Bool × Bool × Bool × Bool × Bool :=
  if tid g < 128 then (false, false, false, true, true, true)
  else if tid g < 160 then (true, true, false, false, false, decide (lane g ≠ 0))
  else (true, false, true, false, true, true)

/-- **The role flags** `%p83` to `%p88`, set at the entry (and after the first election in the
load warp), hold the values of the thread's class. -/
def Flags (g : Nat) (p : Nat → Bool) : Prop := flagsOf p = roleFlags g

/-- The sequence and the head of the thread's block (registers `%r3`, `%r4`, from instruction
111 on). -/
def Cta (P : Params) (g : Nat) (d : D) : Prop :=
  d.w 309 = W (seqOf P g) ∧ d.w 310 = W (headOf P g)

/-- The two entries of the thread's own sequence, loaded at instructions 115 and 116
(registers `%rd2`, `%rd3`). -/
def Own (P : Params) (g : Nat) (d : D) : Prop :=
  d.w 2248 = W (cu P (seqOf P g)) ∧ d.w 2249 = W (cu P (seqOf P g + 1))

/-- **The results of the scan** (from instruction 312 on): the length of the sequence
(`%r8`), its number of tiles (`%r9`), its first tile (`%r1793`) and its first token (`%rd2`). -/
def Scan (P : Params) (g : Nat) (d : D) : Prop :=
  d.w 314 = W (P.length (seqOf P g)) ∧ d.w 315 = W (tiles (P.length (seqOf P g))) ∧
    d.w 2099 = W (ft P (seqOf P g)) ∧ d.w 2248 = W (cu P (seqOf P g))

/-- The 8-fold unrolled loop of the scan, at sequence index `j`: the loop variables `%r1791`
and the pointer `%rd20`, and the two words of the loop's bound (`%r5 = seq % 8`,
`%r6 = seq - seq % 8`). -/
def Loop8 (P : Params) (g : Nat) (d : D) (j : Nat) : Prop :=
  j % 8 = 0 ∧ j + 8 ≤ seqOf P g ∧ d.w 311 = W (seqOf P g % 8) ∧
    d.w 312 = W (seqOf P g - seqOf P g % 8) ∧ d.w 2097 = W j ∧
    d.w 2266 = W (P.offsetsBase + 8 * j)

/-- A site inside a block of the scan: the tile count of the sequences before `i` is in
register `acc`, and entry `i` in register `prev`. -/
def Mid (P : Params) (d : D) (prev acc i : Nat) : Prop :=
  d.w prev = W (cu P i) ∧ d.w acc = W (ft P i)

/-- The register that holds the destination address of the `j`-th load of the initial state
(`shared_mem + 32768 + 4096 j`). -/
def copyDst (j : Nat) : Nat :=
  [498, 501, 503, 505, 507, 509, 511, 513, 515, 517, 519, 521, 523, 525, 527, 529].getD j 0

/-- The register that holds the first coordinate `8 j` of the `j`-th load of the initial
state (for `j = 0` the register of the constant 0). -/
def copyCoord (j : Nat) : Nat :=
  [499, 502, 504, 506, 508, 510, 512, 514, 516, 518, 520, 522, 524, 526, 528, 530].getD j 0

/-- **The registers at a position.** -/
def AtPos (P : Params) (g : Nat) : Pos → D → Prop
  | .elect j, d =>
    match j.val with
    | 0 => warp g = 4 ∧ d.w 331 = i32 (-1) ∧ d.w 330 = W 0
    | 1 => Flags g d.p ∧ d.w 334 = i32 (-1)
    | 2 => Flags g d.p ∧ warp g = 0 ∧ d.w 339 = i32 (-1) ∧ d.w 338 = W 0
    | 3 => Flags g d.p ∧ d.w 352 = W 0 ∧ warp g = 0 ∧ d.w 356 = i32 (-1) ∧ d.w 355 = W 0
    | _ => Flags g d.p ∧ d.w 352 = W 0 ∧ Scan P g d ∧ Cta P g d ∧ d.w 487 = i32 (-1) ∧
      d.w 486 = W 0
  | .shfl j, d =>
    match j.val with
    | 2 => Flags g d.p ∧ d.w 352 = W 0
    | _ => Flags g d.p
  | .init j, d =>
    let S := P.sharedBase
    match j.val with
    | 0 => Flags g d.p ∧ tid g = 0 ∧ d.w 348 = W S ∧ d.w 341 = W (S + 98304) ∧ d.w 340 = W 1
    | 1 => Flags g d.p ∧ tid g = 0 ∧ d.w 348 = W S ∧ d.w 343 = W (S + 98328) ∧
      d.w 342 = W 128 ∧ d.w 340 = W 1
    | 2 => Flags g d.p ∧ tid g = 0 ∧ d.w 348 = W S ∧ d.w 344 = W (S + 98312) ∧
      d.w 340 = W 1 ∧ d.w 342 = W 128
    | 3 => Flags g d.p ∧ tid g = 0 ∧ d.w 348 = W S ∧ d.w 345 = W (S + 98336) ∧
      d.w 342 = W 128 ∧ d.w 340 = W 1
    | 4 => Flags g d.p ∧ tid g = 0 ∧ d.w 348 = W S ∧ d.w 346 = W (S + 98320) ∧
      d.w 340 = W 1 ∧ d.w 342 = W 128
    | 5 => Flags g d.p ∧ tid g = 0 ∧ d.w 347 = W (S + 98344) ∧ d.w 342 = W 128
    | 6 => Flags g d.p ∧ d.w 352 = W 0 ∧ tid g = 0 ∧ d.w 363 = W S ∧
      d.w 358 = W (S + 98352) ∧ d.w 357 = W 128
    | 7 => Flags g d.p ∧ d.w 352 = W 0 ∧ tid g = 0 ∧ d.w 363 = W S ∧
      d.w 360 = W (S + 98368) ∧ d.w 359 = W 1 ∧ d.w 357 = W 128
    | 8 => Flags g d.p ∧ d.w 352 = W 0 ∧ tid g = 0 ∧ d.w 363 = W S ∧
      d.w 361 = W (S + 98360) ∧ d.w 357 = W 128 ∧ d.w 359 = W 1
    | 9 => Flags g d.p ∧ d.w 352 = W 0 ∧ tid g = 0 ∧ d.w 362 = W (S + 98376) ∧ d.w 359 = W 1
    | _ => Flags g d.p ∧ d.w 352 = W 0 ∧ Scan P g d ∧ Cta P g d ∧ tid g = 128 ∧
      d.w 486 = W 1 ∧ d.w 531 = W S ∧ d.w 2093 = W P.heads ∧ d.w 496 = W (S + 98384) ∧
      d.w 495 = W 1
  | .fence j, d =>
    match j.val with
    | 0 => Flags g d.p
    | 1 => Flags g d.p ∧ d.w 352 = W 0
    | _ => Flags g d.p ∧ d.w 352 = W 0 ∧ Scan P g d ∧ Cta P g d ∧ tid g = 128 ∧
      d.w 486 = W 1 ∧ d.w 531 = W P.sharedBase ∧ d.w 2093 = W P.heads ∧
      d.w 496 = W (P.sharedBase + 98384)
  | .bar j, d =>
    match j.val with
    | 0 => Flags g d.p
    | 1 => Flags g d.p ∧ d.w 352 = W 0
    | _ => Flags g d.p ∧ d.w 352 = W 0 ∧ Scan P g d ∧
      d.w 486 = W (if lane g = 0 then 1 else 0)
  | .arrive, d =>
    Flags g d.p ∧ d.w 352 = W 0 ∧ Scan P g d ∧ Cta P g d ∧ tid g = 128 ∧ d.w 486 = W 1 ∧
      d.w 531 = W P.sharedBase ∧ d.w 2093 = W P.heads ∧ d.w 496 = W (P.sharedBase + 98384) ∧
      d.w 497 = W 65536
  | .copy j, d =>
    Flags g d.p ∧ d.w 352 = W 0 ∧ Scan P g d ∧ tid g = 128 ∧ d.w 486 = W 1 ∧
      d.w 531 = W P.sharedBase ∧ d.w 496 = W (P.sharedBase + 98384) ∧ d.w 499 = W 0 ∧
      d.w 500 = W (P.heads * seqOf P g + headOf P g) ∧
      d.w (copyDst j.val) = W (P.sharedBase + (32768 + 4096 * j.val)) ∧
      d.w (copyCoord j.val) = W (8 * j.val)
  | .wait, d =>
    Flags g d.p ∧ d.w 352 = W 0 ∧ Scan P g d ∧ d.w 486 = W (if lane g = 0 then 1 else 0) ∧
      d.w 532 = W (P.sharedBase + 98384) ∧ d.w 533 = W 0 ∧ d.w 534 = W 10000000
  | .load j, d =>
    let B := P.offsetsBase
    let s := seqOf P g
    Flags g d.p ∧ d.w 352 = W 0 ∧ Cta P g d ∧
    match j.val with
    | 0 => d.w 2264 = W (B + 8 * s)
    | 1 => d.w 2264 = W (B + 8 * s) ∧ d.w 2248 = W (cu P s)
    | 2 => Own P g d ∧ 8 ≤ s ∧ d.w 311 = W (s % 8) ∧ d.w 312 = W (s - s % 8) ∧ d.w 2099 = W 0
    | 3 => Own P g d ∧ ∃ i, Loop8 P g d i ∧ d.w 2098 = W i ∧ d.w 2099 = W (ft P i) ∧
      d.w 3412 = W (cu P i)
    | 4 => Own P g d ∧ ∃ i, Loop8 P g d i ∧ d.w 2098 = W i ∧ Mid P d 364 372 (i + 1)
    | 5 => Own P g d ∧ ∃ i, Loop8 P g d i ∧ d.w 2098 = W i ∧ Mid P d 373 380 (i + 2)
    | 6 => Own P g d ∧ ∃ i, Loop8 P g d i ∧ d.w 2098 = W i ∧ Mid P d 381 388 (i + 3)
    | 7 => Own P g d ∧ ∃ i, Loop8 P g d i ∧ d.w 2098 = W i ∧ Mid P d 389 396 (i + 4)
    | 8 => Own P g d ∧ ∃ i, Loop8 P g d i ∧ d.w 2098 = W i ∧ Mid P d 397 404 (i + 5)
    | 9 => Own P g d ∧ ∃ i, Loop8 P g d i ∧ d.w 2098 = W i ∧ Mid P d 405 412 (i + 6)
    | 10 => Own P g d ∧ ∃ i, Loop8 P g d i ∧ d.w 2098 = W (i + 8) ∧ Mid P d 413 420 (i + 7)
    -- the block of four: `i = s - s % 8`, entered when `4 ≤ s % 8`
    | 11 => Own P g d ∧ 4 ≤ s % 8 ∧ d.w 313 = W (s % 4) ∧ d.w 2275 = W (B + 8 * (s - s % 8)) ∧
      d.w 2098 = W (s - s % 8) ∧ d.w 2099 = W (ft P (s - s % 8))
    | 12 => Own P g d ∧ 4 ≤ s % 8 ∧ d.w 313 = W (s % 4) ∧ d.w 2275 = W (B + 8 * (s - s % 8)) ∧
      d.w 2098 = W (s - s % 8) ∧ d.w 2099 = W (ft P (s - s % 8)) ∧
      d.w 2276 = W (cu P (s - s % 8 + 1))
    | 13 => Own P g d ∧ 4 ≤ s % 8 ∧ d.w 313 = W (s % 4) ∧ d.w 2275 = W (B + 8 * (s - s % 8)) ∧
      d.w 2098 = W (s - s % 8) ∧ Mid P d 429 436 (s - s % 8 + 1)
    | 14 => Own P g d ∧ 4 ≤ s % 8 ∧ d.w 313 = W (s % 4) ∧ d.w 2275 = W (B + 8 * (s - s % 8)) ∧
      d.w 2098 = W (s - s % 8) ∧ Mid P d 437 444 (s - s % 8 + 2)
    | 15 => Own P g d ∧ 4 ≤ s % 8 ∧ d.w 313 = W (s % 4) ∧ d.w 2275 = W (B + 8 * (s - s % 8)) ∧
      d.w 2098 = W (s - s % 8 + 4) ∧ Mid P d 445 452 (s - s % 8 + 3)
    -- the single sequence left when `s % 4 = 1`
    | 16 => Own P g d ∧ s % 2 = 1 ∧ d.w 2286 = W (B + 8 * (s - 1)) ∧ d.w 2098 = W (s - 1) ∧
      d.w 2099 = W (ft P (s - 1))
    -- the block of two: `i = s - s % 4`, entered when `2 ≤ s % 4`
    | 17 => Own P g d ∧ 2 ≤ s % 4 ∧ d.w 2282 = W (B + 8 * (s - s % 4)) ∧
      d.w 2098 = W (s - s % 4) ∧ d.w 2099 = W (ft P (s - s % 4))
    | 18 => Own P g d ∧ 2 ≤ s % 4 ∧ d.w 2282 = W (B + 8 * (s - s % 4)) ∧
      d.w 2098 = W (s - s % 4) ∧ d.w 2099 = W (ft P (s - s % 4)) ∧
      d.w 2283 = W (cu P (s - s % 4 + 1))
    | 19 => Own P g d ∧ 2 ≤ s % 4 ∧ d.w 2282 = W (B + 8 * (s - s % 4)) ∧
      d.w 2098 = W (s - s % 4 + 2) ∧ Mid P d 461 468 (s - s % 4 + 1)
    | _ => Own P g d ∧ s % 2 = 1 ∧ d.w 2288 = W (B + 8 * (s - 1)) ∧
      d.w 2099 = W (ft P (s - 1)) ∧ d.w 3413 = W (cu P (s - 1))

/-- **The reference invariant of a state at a position.** -/
structure RefAt (P : Params) (g : Nat) (pos : Pos) (d : D) : Prop where
  site : d.site = pos.site
  base : Base P g d
  pos : AtPos P g pos d

/-- **The state at the exit of the phase**: the proxy fence at instruction 387, reached when
the thread's poll of the state barrier succeeded. These are the registers the later phases
read: the role flags, `%cluster_ctarank`, the results of the scan, and the flag of the election
at instruction 312 (`%r180`: 1 in lane 0 of each warp). -/
structure Exit (P : Params) (g : Nat) (d : D) : Prop where
  site : d.site = .fenceProxy 0
  base : Base P g d
  flags : Flags g d.p
  rank : d.w 352 = W 0
  scan : Scan P g d
  elected : d.w 486 = W (if lane g = 0 then 1 else 0)

/-! ### The ledger -/

/-- Counts of six classes of events. -/
structure Led where
  /-- `bar.sync 0` events. -/
  bars : Nat
  /-- `mbarrier.init` events. -/
  inits : Nat
  /-- `mbarrier.arrive` events. -/
  arrs : Nat
  /-- Asynchronous tensor load issues. -/
  issues : Nat
  /-- Successful polls of an mbarrier. -/
  polls : Nat
  /-- Shuffles. -/
  shfls : Nat
  deriving DecidableEq

/-- Whether an event is an mbarrier initialization, an arrival, a tensor load issue, a
successful poll. -/
def isInit (e : Event) : Bool := match e.kind with | .mbInit .. => true | _ => false
def isArr (e : Event) : Bool := match e.kind with | .arrive .. => true | _ => false
def isIssue (e : Event) : Bool := match e.kind with | .tensorIssue .. => true | _ => false
def isOkPoll (e : Event) : Bool := match e.kind with | .wait _ _ true _ _ => true | _ => false

/-- The ledger of a list of events. -/
def ledOf (es : List Event) : Led :=
  ⟨es.countP (Execution.isBarId 0), es.countP isInit, es.countP isArr, es.countP isIssue,
    es.countP isOkPoll, es.countP Execution.isShfl⟩

/-- The ledger of one event. -/
def ledEv (e : Event) : Led :=
  ⟨if Execution.isBarId 0 e then 1 else 0, if isInit e then 1 else 0, if isArr e then 1 else 0,
    if isIssue e then 1 else 0, if isOkPoll e then 1 else 0,
    if Execution.isShfl e then 1 else 0⟩

instance : Add Led := ⟨fun a b =>
  ⟨a.bars + b.bars, a.inits + b.inits, a.arrs + b.arrs, a.issues + b.issues, a.polls + b.polls,
    a.shfls + b.shfls⟩⟩

theorem Led.add_def (a b : Led) : a + b =
    ⟨a.bars + b.bars, a.inits + b.inits, a.arrs + b.arrs, a.issues + b.issues,
      a.polls + b.polls, a.shfls + b.shfls⟩ := rfl

/-- **The ledger before a position**, by the thread's role: the init leader is thread 0 of its
block, the load leader thread 128. Every thread makes its three shuffles at the instructions
48, 55 and 87. -/
def led (g : Nat) : Pos → Led
  | .elect j => if j.val < 3 then ⟨0, 0, 0, 0, 0, j.val⟩
      else if j.val = 3 then ⟨1, if tid g = 0 then 6 else 0, 0, 0, 0, 3⟩
      else ⟨2, if tid g = 0 then 10 else 0, 0, 0, 0, 3⟩
  | .shfl j => if j.val < 2 then ⟨0, 0, 0, 0, 0, j.val⟩
      else ⟨1, if tid g = 0 then 6 else 0, 0, 0, 0, 2⟩
  | .init j => if j.val < 6 then ⟨0, j.val, 0, 0, 0, 2⟩
      else if j.val < 10 then ⟨1, j.val, 0, 0, 0, 3⟩ else ⟨2, 0, 0, 0, 0, 3⟩
  | .fence j => if j.val = 0 then ⟨0, if tid g = 0 then 6 else 0, 0, 0, 0, 2⟩
      else if j.val = 1 then ⟨1, if tid g = 0 then 10 else 0, 0, 0, 0, 3⟩
      else ⟨2, 1, 0, 0, 0, 3⟩
  | .bar j => if j.val = 0 then ⟨0, if tid g = 0 then 6 else 0, 0, 0, 0, 2⟩
      else if j.val = 1 then ⟨1, if tid g = 0 then 10 else 0, 0, 0, 0, 3⟩
      else ⟨2, if tid g = 0 then 10 else if tid g = 128 then 1 else 0,
        if tid g = 128 then 1 else 0, if tid g = 128 then 16 else 0, 0, 3⟩
  | .load _ => ⟨2, if tid g = 0 then 10 else 0, 0, 0, 0, 3⟩
  | .arrive => ⟨2, 1, 0, 0, 0, 3⟩
  | .copy j => ⟨2, 1, 1, j.val, 0, 3⟩
  | .wait => ⟨3, if tid g = 0 then 10 else if tid g = 128 then 1 else 0,
      if tid g = 128 then 1 else 0, if tid g = 128 then 16 else 0, 0, 3⟩

/-- The ledger at the exit. -/
def ledExit (g : Nat) : Led :=
  ⟨3, if tid g = 0 then 10 else if tid g = 128 then 1 else 0, if tid g = 128 then 1 else 0,
    if tid g = 128 then 16 else 0, 1, 3⟩

variable (P : Params) (L : Launch) (X : Execution) (g : Nat)

/-- **The invariant of the startup phase** before the thread's event `k`. -/
def Inv (k : Nat) (d : D) : Prop :=
  ∃ pos, RefAt P g pos d ∧ ledOf ((X.tr g).take k) = led g pos

/-- **The exit condition of the startup phase** before the thread's event `k`. -/
def Out (k : Nat) (d : D) : Prop :=
  Exit P g d ∧ ledOf ((X.tr g).take k) = ledExit g

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Startup
