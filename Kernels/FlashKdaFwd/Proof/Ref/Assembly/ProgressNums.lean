-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.Tracked
public import Kernels.FlashKdaFwd.Proof.Ref.Store.Progress
public import Kernels.FlashKdaFwd.Proof.Ref.Producer.Progress
public import Kernels.FlashKdaFwd.Proof.Ref.Conversion.Exports
public import Kernels.FlashKdaFwd.Proof.Ref.CarryLoad.Exports
public import Kernels.FlashKdaFwd.Proof.Ref.Compute.ExportsProgress
public import Kernels.FlashKdaFwd.Proof.Ref.Epilogue.Contract

@[expose] public section

/-!
# The numbers of the progress contract, for the whole run of a thread

The progress contract (`Proof/Schedule/Contract.lean: RefProgress L mem0 X I`) is stated for
numbers `I : Nums` that the reference layer chooses (`Proof/Schedule/Defs.lean`): the tile
count of a thread's block, the tile index of a state of the thread's machine and the number of
counted events the thread can still make from a state (a *counted* event is every event but a
failed poll of an mbarrier). This file defines them, `nums P L`, as functions of the state alone,
pieced together from the numbers of the seven phases of a thread's run by the instruction the
state is at (`d.site.pc`) and the thread's role (`tid g`, the thread's index in its block: a
compute thread has `tid g < 128`, the load warp is 128 to 159, the store warp 160 to 191).

**The tile count** is `Protocol.ctaTiles P (g / L.block)`: the tiles of the sequence of the
thread's block.

**The tile index** (`Progress.tileNum`): 0 up to the `bar.sync 0` of instruction 1402 (the
convention of the contract's field `tile_start`); the tile count from the `bar.sync 0` of
instruction 3113 on (`tile_end`); in between the tile index of the thread's tile loop:
`Compute.tileOf`, `Producer.tileOf` or `Store.tileOf`, by role.

**The counted events left** (`Progress.leftNum`): each phase has a number of events left in the
phase, read off the state; the number for the whole run adds a base per phase, chosen from the
last phase backwards so that the step from a phase into the next one does not raise the sum:

| instructions | phase | events left |
|---|---|---|
| up to 386 | startup | `2305 + 3100 T + Startup.leftOf` |
| 387 to 621 | conversion | `2130 + 3100 T + Conversion.leftOf` |
| 622 to 1401 | carry loads | `727 + 3100 T + CarryLoad.leftOf` |
| 1402 to 3112 | tile loop, by role | `723 +` `Compute.leftOf`, `Producer.leftOf`, `Store.leftOf` |
| from 3113 | epilogue | `3836 -` the instruction |

`T` is the tile count of the thread's sequence. The epilogue is a straight line of code for
every role, so the distance of the instruction from the end of the program bounds its events.
The bases are not tight: 3100 per tile is more than any role needs.

**The bound** `bound P`: at most `2705 + 100 N + 3100 * tiles (the number of tokens)` counted
events are left at the first state of every thread (`N` sequences).

Everything but `nums` and `bound` is in the sub-namespace `Assembly.Progress`.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Protocol (ctaTiles)

noncomputable section

namespace Progress

/-- **The tile index of a state**: 0 up to instruction 1402, the tile count of the thread's
block from instruction 3113 on, and in between the tile index of the thread's tile loop. -/
def tileNum (P : Params) (L : Launch) (g : Nat) (d : D) : Nat :=
  if d.site.pc ≤ 1402 then 0
  else if 3113 ≤ d.site.pc then ctaTiles P (g / L.block)
  else if tid g < 128 then Compute.tileOf P g d
  else if tid g < 160 then Producer.tileOf P g d
  else Store.tileOf d

/-- The counted events left in the tile loop of the thread's role, read off a state. -/
def loopLeft (P : Params) (g : Nat) (d : D) : Nat :=
  if tid g < 128 then Compute.leftOf P g d
  else if tid g < 160 then Producer.leftOf P g d
  else Store.leftOf P g d

/-- **The counted events a thread can still make from a state, at most**: the events left in
the phase the state's instruction belongs to, plus a bound on the events of the later phases
(see the table in the header). -/
def leftNum (P : Params) (g : Nat) (d : D) : Nat :=
  if d.site.pc < 387 then 2305 + 3100 * tiles (P.length (seqOf P g)) + Startup.leftOf P g d
  else if d.site.pc < 622 then
    2130 + 3100 * tiles (P.length (seqOf P g)) + Conversion.leftOf g d
  else if d.site.pc < 1402 then 727 + 3100 * tiles (P.length (seqOf P g)) + CarryLoad.leftOf d
  else if d.site.pc < 3113 then 723 + loopLeft P g d
  else 3836 - d.site.pc

end Progress

/-- **The numbers of the progress contract**: the tile count of a thread's block, the tile
index of a state and the counted events left at a state. -/
def nums (P : Params) (L : Launch) : Proof.Progress.Nums where
  tiles g := ctaTiles P (g / L.block)
  tile := Progress.tileNum P L
  left := Progress.leftNum P

/-- **The bound on the counted events of a thread**: `2705 + 100 N` for the startup, the
conversion and the carry loads of a launch with `N` sequences, and 3100 per tile of a sequence
as long as the whole batch. -/
def bound (P : Params) : Nat := 2705 + 100 * P.sequences + 3100 * tiles P.total

namespace Progress

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-- The tile count of the contract is the tile count of the thread's sequence. -/
theorem tiles_eq (hpre : Pre P L mem0) (g : Nat) :
    ctaTiles P (g / L.block) = tiles (P.length (seqOf P g)) := by
  simp only [ctaTiles, seqOf, hpre.block]

/-- The role of a thread in the contract's terms. -/
theorem role_eq (hpre : Pre P L mem0) (g : Nat) : g % L.block = tid g := block_mod hpre

/-- The warp of a thread in the contract's terms. -/
theorem warp_eq (hpre : Pre P L mem0) (g : Nat) : g % L.block / 32 = warp g := by
  rw [block_mod hpre]
  rfl

/-! ### The tile index, by instruction -/

theorem tileNum_start {d : D} (h : d.site.pc ≤ 1402) : tileNum P L g d = 0 := by
  simp only [tileNum, h, ↓reduceIte]

theorem tileNum_end {d : D} (h : 3113 ≤ d.site.pc) :
    tileNum P L g d = ctaTiles P (g / L.block) := by
  have h1 : ¬ d.site.pc ≤ 1402 := by omega
  simp only [tileNum, h1, h, ↓reduceIte]

theorem tileNum_compute {d : D} (h1 : 1402 < d.site.pc) (h2 : d.site.pc < 3113)
    (hr : tid g < 128) : tileNum P L g d = Compute.tileOf P g d := by
  have h3 : ¬ d.site.pc ≤ 1402 := by omega
  have h4 : ¬ 3113 ≤ d.site.pc := by omega
  simp only [tileNum, h3, h4, hr, ↓reduceIte]

theorem tileNum_producer {d : D} (h1 : 1402 < d.site.pc) (h2 : d.site.pc < 3113)
    (hr : warp g = 4) : tileNum P L g d = Producer.tileOf P g d := by
  have h3 : ¬ d.site.pc ≤ 1402 := by omega
  have h4 : ¬ 3113 ≤ d.site.pc := by omega
  obtain ⟨h5, h6⟩ := (warp_eq4_iff g).mp hr
  have h7 : ¬ tid g < 128 := by omega
  simp only [tileNum, h3, h4, h6, h7, ↓reduceIte]

theorem tileNum_store {d : D} (h1 : 1402 < d.site.pc) (h2 : d.site.pc < 3113)
    (hr : warp g = 5) : tileNum P L g d = Store.tileOf d := by
  have h3 : ¬ d.site.pc ≤ 1402 := by omega
  have h4 : ¬ 3113 ≤ d.site.pc := by omega
  have h5 := (warp_eq5_iff g).mp hr
  have h6 : ¬ tid g < 128 := by omega
  have h7 : ¬ tid g < 160 := by omega
  simp only [tileNum, h3, h4, h6, h7, ↓reduceIte]

/-! ### The events left, by instruction -/

theorem leftNum_startup {d : D} (h : d.site.pc < 387) :
    leftNum P g d = 2305 + 3100 * tiles (P.length (seqOf P g)) + Startup.leftOf P g d := by
  simp only [leftNum, h, ↓reduceIte]

theorem leftNum_conversion {d : D} (h1 : 387 ≤ d.site.pc) (h2 : d.site.pc < 622) :
    leftNum P g d = 2130 + 3100 * tiles (P.length (seqOf P g)) + Conversion.leftOf g d := by
  have h3 : ¬ d.site.pc < 387 := by omega
  simp only [leftNum, h3, h2, ↓reduceIte]

theorem leftNum_carry {d : D} (h1 : 622 ≤ d.site.pc) (h2 : d.site.pc < 1402) :
    leftNum P g d = 727 + 3100 * tiles (P.length (seqOf P g)) + CarryLoad.leftOf d := by
  have h3 : ¬ d.site.pc < 387 := by omega
  have h4 : ¬ d.site.pc < 622 := by omega
  simp only [leftNum, h3, h4, h2, ↓reduceIte]

theorem leftNum_loop {d : D} (h1 : 1402 ≤ d.site.pc) (h2 : d.site.pc < 3113) :
    leftNum P g d = 723 + loopLeft P g d := by
  have h3 : ¬ d.site.pc < 387 := by omega
  have h4 : ¬ d.site.pc < 622 := by omega
  have h5 : ¬ d.site.pc < 1402 := by omega
  simp only [leftNum, h3, h4, h5, h2, ↓reduceIte]

theorem leftNum_epilogue {d : D} (h : 3113 ≤ d.site.pc) : leftNum P g d = 3836 - d.site.pc := by
  have h3 : ¬ d.site.pc < 387 := by omega
  have h4 : ¬ d.site.pc < 622 := by omega
  have h5 : ¬ d.site.pc < 1402 := by omega
  have h6 : ¬ d.site.pc < 3113 := by omega
  simp only [leftNum, h3, h4, h5, h6, ↓reduceIte]

theorem loopLeft_compute {d : D} (hr : tid g < 128) : loopLeft P g d = Compute.leftOf P g d := by
  simp only [loopLeft, hr, ↓reduceIte]

theorem loopLeft_producer {d : D} (hr : warp g = 4) :
    loopLeft P g d = Producer.leftOf P g d := by
  obtain ⟨h5, h6⟩ := (warp_eq4_iff g).mp hr
  have h7 : ¬ tid g < 128 := by omega
  simp only [loopLeft, h6, h7, ↓reduceIte]

theorem loopLeft_store {d : D} (hr : warp g = 5) :
    loopLeft P g d = Store.leftOf P g d := by
  have h5 := (warp_eq5_iff g).mp hr
  have h6 : ¬ tid g < 128 := by omega
  have h7 : ¬ tid g < 160 := by omega
  simp only [loopLeft, h6, h7, ↓reduceIte]

/-- **The events left at the entry state of a tile loop** (the state at the `bar.sync 0` of
instruction 1402), whatever the role: at most `4 + 3100 T`. -/
theorem loopLeft_entry {d : D} (hs : d.site = .bar 5) :
    loopLeft P g d ≤ 4 + 3100 * tiles (P.length (seqOf P g)) := by
  have hpc : d.site.pc ≤ 1402 := by rw [hs]; decide
  unfold loopLeft
  split_ifs with h1 h2
  · simp only [Compute.leftOf, hpc, ↓reduceIte, Compute.tilesOf]
    omega
  · simp only [Producer.leftOf, hs, Producer.tilesOf]
    split_ifs <;> omega
  · simp only [Store.leftOf, hs, Store.partEv, tiles]
    split_ifs <;> omega

end Progress

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
