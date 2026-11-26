-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Lib

@[expose] public section

/-! # Epilogue phase: the entry condition

The epilogue is what every thread of a thread block does after the tile loops, instructions
3113 to 3835: a `bar.sync 0`; in a compute thread the 128 stores of its carry registers into the
FP32 state buffer; a proxy fence and a second `bar.sync 0`; in the store leader the 16 tensor
stores of the final state with a group commit and a group wait; a third `bar.sync 0` and `ret`.

Its entry is the state at the site `bar_7` (instruction 3113, the first of the three
`bar.sync 0`), **before** that barrier's event. Every thread reaches it, from one of the three
tile-loop phases, by role (`Ref/Common.lean`: the index of a thread in its block is `tid g`):

* a **compute thread** (`tid g < 128`) from the Compute phase (instructions 2106 to 2944);
* a thread of the **load warp** (`128 ≤ tid g < 160`) from the Producer phase (1403 to 2105);
* a thread of the **store warp** (`160 ≤ tid g`) from the Store phase (2945 to 3112).

All three arrive through the two instructions 3111 and 3112, which read the thread index again
(`mov.u32 %r1736, %tid.x`) and compare it with 127 (`setp.gt.u32 %p77, %r1736, 127`).

This file states what the epilogue needs there (`W n` is the 64-bit word of the number `n`;
a register is named by its id in the generated thread machine, `%rN` is `306 + N`):

* `Entry P g d`: the registers. `%r1736` (id 2042) holds the thread index and `%p77` says
  whether the thread is outside the compute warps, for every role. The flag `%r180` (id 486) of
  the election at instruction 312 (1 in lane 0 of a warp, else 0) is asked **of the store warp
  only**: it is live at `bar_7` for every role, but the code reads it only to decide whether a
  thread of the store warp is the store leader (instructions 3768 to 3777: `%p82 = (role ≠ 2) ∨
  (%r180 = 0)` skips the tensor stores), so a compute thread and a thread of the load warp
  need no fact about it. The 128 carry registers of a compute thread are data: the epilogue
  stores whatever they hold and asks nothing of them here. The tensor-map pointer `%rd14` of
  the store warp has a static kind in the machine and needs no fact.
* `In P X g k0 d`: the entry condition before the thread's event `k0`: `Entry`, and the one
  count the epilogue's own ledger starts from: the thread has made six `bar.sync 0` (at the
  instructions 85, 110, 379, 620, 621 and 1402).

Every other count of earlier events that a contract asks of a thread in the epilogue (named
barriers, matrix events, polls and arrivals per mbarrier, …) is not part of the entry
condition: no event of the epilogue belongs to these classes, `Exports.lean` proves that such a
count is the same at every position of the epilogue as at the entry (`count_in`, `count_exit`),
and each export that needs one takes it as a hypothesis about the first `k0` events.

`entry_of_compute`, `entry_of_load`, `entry_of_store` build the entry condition from the facts
the three tile-loop phases have at their exits. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Epilogue
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref

noncomputable section

/-- **The state at the entry of the epilogue**: the site `bar_7` (instruction 3113), before its
event. `%r1736` is the thread index, `%p77` says that it is above 127, and in the store warp
`%r180` is the election flag of the thread's lane. -/
structure Entry (P : Params) (g : Nat) (d : D) : Prop where
  site : d.site = .bar 7
  index : d.w 2042 = W (tid g)
  role : d.p 77 = decide (127 < tid g)
  elected : 160 ≤ tid g → d.w 486 = W (if lane g = 0 then 1 else 0)

/-- **The entry condition of the epilogue** before the thread's event `k0`: the registers of
`Entry`, and six earlier `bar.sync 0`. -/
def In (P : Params) (X : Execution) (g k0 : Nat) (d : D) : Prop :=
  Entry P g d ∧ ((X.tr g).take k0).countP (Execution.isBarId 0) = 6

variable {P : Params} {g : Nat} {d : D}

/-- The entry condition of a compute thread, from the exit of the Compute phase: `%p77` is
false. -/
theorem entry_of_compute (hr : tid g < 128) (hs : d.site = .bar 7) (ht : d.w 2042 = W (tid g))
    (hp : d.p 77 = false) : Entry P g d :=
  ⟨hs, ht, by rw [hp]; exact (decide_eq_false (by omega)).symm, fun h => by omega⟩

/-- The entry condition of a thread of the load warp, from the exit of the Producer phase
(`Producer.Exit`: its fields `site`, `tid`, `p77`). -/
theorem entry_of_load (hr : warp g = 4) (hs : d.site = .bar 7) (ht : d.w 2042 = W (tid g))
    (hp : d.p 77 = true) : Entry P g d := by
  have h := (warp_eq4_iff g).mp hr
  exact ⟨hs, ht, by rw [hp]; exact (decide_eq_true (by omega)).symm, fun h' => by omega⟩

/-- The entry condition of a thread of the store warp, from the exit of the Store phase
(`Store.Exit`: its fields `site`, `tid'`, `role` and `keep.elected`). -/
theorem entry_of_store (hr : warp g = 5) (hs : d.site = .bar 7) (ht : d.w 2042 = W (tid g))
    (hp : d.p 77 = true) (he : d.w 486 = W (if lane g = 0 then 1 else 0)) : Entry P g d := by
  have h := (warp_eq5_iff g).mp hr
  exact ⟨hs, ht, by rw [hp]; exact (decide_eq_true (by omega)).symm, fun _ => he⟩

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Epilogue
