-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Progress.Kda
public import Kernels.FlashKdaFwd.Proof.Progress.Bound
public import Kernels.FlashKdaFwd.Proof.Thread.StepAt
public import Kernels.FlashKdaFwd.Proof.Thread.Start
public import Kernels.FlashKdaFwd.Proof.Protocol.Export

@[expose] public section

/-!
# The progress instance on the real thread machine: definitions

Everything the progress skeleton (`Proof/Progress/Progress.lean`) is parametrized by, defined
for the generated thread machine `Thread.code L g` (state `Thread.D` = a site and three
register files).

* `siteCls`, `cls`: the class of a state by the kind of its site. A shuffle or an election is a
  warp collective; an `mbarrier.try_wait` is a poll; the matrix event of a warp matrix
  instruction (`mma`, `movmatrix`, the second event of `ldmatrix`, the first of `stmatrix`) is
  a matrix event; every other site is a free event (reads, stores, fences, mbarrier
  operations, issues, the arrival of a barrier or of a bulk-group wait, the row read of
  `ldmatrix`, the row write of `stmatrix`, a trap, the exit).
* `wkey`: the warp key of a thread (its block and its warp). `barG`: the participant warps of
  barrier 0 (all six) and of barrier 8 (the four compute warps).
* `pollEv`: the events a state fires, as the thread layer's step relation gives them. With this
  definition the premise `pollShape` is a tautology; what a poll state polls (which mbarrier,
  which parity) is a fact of followed states and is asked of the reference layer
  (`RefProgress.poll`, `Contract.lean`).
* `Nums`: the three numbers the time table and the rank read off a state and that only the
  reference layer can give in closed form: the tile count of the thread's block, the tile
  index of a state, and the number of counted events left.
* `timeAt`, `time`, `timed`: the time table. One block's timeline is: the startup at eight
  times the instruction index; then one slot of 16384 per tile, with the load leader's code
  (instructions 1403 to 2105) in the band from 2, the compute warps' code (2106 to 2944) in
  the band from 1024 at eight per instruction, the store leader's code (2945 to 3112) in the
  band from 8192; then the epilogue (from 3113) after the slot that follows the last tile. Twice
  the sub-step is added where an instruction has several events.
* `bar0Of`, `bar8Of`, `collOf`, `matBefore`: the counts of a thread's earlier `bar.sync 0`,
  named barriers, warp collectives and matrix events as functions of its position; the
  contract asks the reference layer for these equations.
* `Bar.round`, `Bar.poller`: for an mbarrier, how many successful polls a poller at tile `t`
  has made at most, and which threads poll it.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Progress

open PTX PTX.Sched PTX.Flow PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Protocol

noncomputable section

/-- The class of a site, by its kind. -/
def siteCls : Thread.Site → Cls
  | .elect _ | .shfl _ => .coll
  | .mbarWait _ => .poll
  | .warpMma _ | .matrixMove _ | .matrixStore _ | .matrixLoadMx _ _ => .matrix
  | _ => .free

/-- The class of a state: the class of its site. -/
def cls (_g : Nat) (d : Thread.D) : Cls := siteCls d.site

/-- The warp key of a thread: its block and its warp. -/
def wkey (L : Launch) (g : Nat) : Nat × Nat := (g / L.block, g % L.block / 32)

/-- The lanes of a warp have one key. -/
theorem wkey_eq {L : Launch} {g h : Nat} (hs : SameWarp L g h) : wkey L g = wkey L h := by
  simp only [wkey]
  rw [hs.1.2.2, hs.2]

/-- The participant warps of the barriers: all six warps for barrier 0, the four compute warps
for barrier 8. -/
def barG (id w : Nat) : Prop := (id = 0 ∧ w < 6) ∨ (id = 8 ∧ w < 4)

/-- The events a state fires: the events of the instruction at its site, from a concrete state
of it. -/
def pollEv (L : Launch) (g : Nat) (d : Thread.D) (e : Event) : Prop :=
  ∃ t ins o, (Thread.code L g).AtD d t ∧ kernel.code[d.site.pc]? = some ins ∧
    Fires d.site.pc (eventTmpl Assumptions.all L g t ins.op) e o

/-- **The numbers of a state that the reference layer supplies in closed form.** -/
structure Nums where
  /-- The tile count of the thread's block. -/
  tiles : Nat → Nat
  /-- The tile index of a state of a thread: 0 before the tile loops, the index of the tile
  being worked on inside a loop, the tile count after the loops. -/
  tile : Nat → Thread.D → Nat
  /-- The counted events a thread at a state still has to make, at most. -/
  left : Nat → Thread.D → Nat

/-- The width of a tile's slot of the time table. -/
def slot : Nat := 16384

/-- The place of an instruction of the tile loops inside a slot. -/
def band (pc sub : Nat) : Nat :=
  if pc ≤ 2105 then 2 + (pc - 1403)
  else if pc ≤ 2944 then 1024 + 8 * (pc - 2106) + 2 * sub
  else 8192 + (pc - 2945)

/-- **The time of a position**: tile count `T`, tile index `t`, instruction index, sub-step. -/
def timeAt (T t pc sub : Nat) : Nat :=
  if pc ≤ 1402 then 8 * pc + 2 * sub
  else if pc ≤ 3112 then slot * (min t T + 1) + band pc sub
  else slot * (T + 2) + 8 * (pc - 3113) + 2 * sub

/-- **The time of a state.** -/
def time (I : Nums) (g : Nat) (d : Thread.D) : Nat :=
  timeAt (I.tiles g) (I.tile g d) d.site.pc d.site.sub

/-- **The time table over the thread machine.** -/
@[reducible] def timed (L : Launch) (I : Nums) : Timed kernel Assumptions.all L :=
  ⟨Thread.code L, time I⟩

/-- The rank of a state for the termination bound: the counted events left. -/
def rank (I : Nums) (g : Nat) (d : Thread.D) : Nat := I.left g d

/-! ### Counts as functions of the position -/

/-- The `bar.sync 0` a thread at instruction `pc` has made: the nine positions below `pc`. -/
def bar0Of (pc : Nat) : Nat := (bar0Pcs.filter (· < pc)).length

/-- The named barriers a compute thread at instruction `pc` and tile `tile` has made. -/
def bar8Of (pc tile : Nat) : Nat := if 2913 < pc ∧ pc ≤ 2944 then tile + 1 else tile

/-- The positions of the warp collectives of a warp, in program order: warp 0 also elects the
lane that initializes the mbarriers (61, 93), warp 4 first elects the load leader (32). -/
def collPcs (w : Nat) : List Nat :=
  if w = 0 then [48, 52, 55, 61, 87, 93, 312]
  else if w = 4 then [32, 48, 52, 55, 87, 312]
  else [48, 52, 55, 87, 312]

/-- The warp collectives a thread of warp `w` at instruction `pc` has made. -/
def collOf (w pc : Nat) : Nat := ((collPcs w).filter (· < pc)).length

/-- The matrix events of the current tile that a compute thread at a site has made: the matrix
instructions below the site's, and its own once the row write of an `stmatrix` is next; none
after the tile loop, where the tile index is the tile count. -/
def matBefore (s : Thread.Site) : Nat :=
  if 3113 ≤ s.pc then 0
  else (Proof.Top.matrixSites.filter (fun e => e.1 < s.pc)).length +
    (match s with
      | .matrixStoreWr _ _ => 1
      | _ => 0)

/-- The successful polls of an mbarrier that a poller at tile `t` has made, at most: one per
earlier tile of the barrier's stage. -/
def roundOf : Bar → Nat → Nat
  | .loadFull s, t | .loadEmpty s, t => uses 3 t s.val
  | .storeFull o, t | .storeEmpty o, t => uses 2 t o.val
  | .state, _ => 0

/-- The threads of block `c` that poll an mbarrier. -/
def pollerOf (L : Launch) (c : Nat) : Bar → Nat → Prop
  | .loadFull _, g | .storeEmpty _, g => g / L.block = c ∧ g % L.block < 128
  | .loadEmpty _, g => g = loadLeader L c
  | .storeFull _, g => g = storeLeader L c
  | .state, _ => True

end

end PTX.Kernels.FlashKdaFwd.Proof.Progress
