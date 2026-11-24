-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.Role
public import Lemmas.Kernel.Progress.Slots

@[expose] public section

/-! # The roles' site times: one cluster, sequentially

The progress descent ranks a pending thread by the time of its next event in a sequential
schedule of its cluster. A thread's time is a function of its machine state alone: the role
states carry their item `i` and loop trip `t`, so the times are formulas in `(n, T, site, i, t)`,
with `n` the item's KV tiles and `T` the cluster's items. This file holds the schedule's
coordinates (slots, bands, fixed times) and the site tables of the thread's states, for the
progress layer, and their order (from the slot clock, `slotClock`); it is the thread layer's file
the progress layer may read. Within a role the times follow the program order, so a thread's next
event is never later than any event it has still to do.

**Slots.** Item `i` has `n + 1` slots; slot `s` of item `i` is the global slot
`gslot n i s = i (n + 1) + s`, starting at `base + span · gslot` (`slotTime`); the tail of the
cluster's items starts at the global slot of item `T` (`tailTime`). **Bands.** Within a slot
the roles run in bands: the loader `[0, 100)`, the MMA warp `[100, 400)`, softmax stage 0
`[400, 600)`, correction stage 0 `[600, 1000)`, softmax stage 1 `[1000, 1200)`, correction
stage 1 `[1200, 1600)`, the store warp `[1600, 1800)`. **Fixed times** below `base`: the
prologue, every role's `setmaxnreg` and the first barrier generations. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Progress

open PTX

noncomputable section

namespace Time

/-- The length of one slot (above twice the events of any role in a slot). -/
abbrev span : Nat := 4096

/-- The start of the first item, after every fixed time. -/
abbrev base : Nat := 256

/-- The global slot of slot `s` of item `i`. -/
def gslot (n i s : Nat) : Nat := i * (n + 1) + s

/-- The time at offset `o` of slot `s` of item `i`. -/
def slotTime (n i s o : Nat) : Nat := base + span * gslot n i s + o

/-- The time at offset `o` of the tail, after the `T` items. -/
def tailTime (n T o : Nat) : Nat := slotTime n T 0 o

/-- The slot times are a clock in slots (`Sched.SlotClock`). -/
theorem slotClock : Sched.SlotClock slotTime span base :=
  Sched.slotClock_std (by decide) (by decide)

/-! ### The order of the slot times -/

/-- Within a slot an earlier offset is earlier. -/
theorem lt_of_off {n i s o o' : Nat} (h : o < o') : slotTime n i s o < slotTime n i s o' :=
  slotClock.lt_of_off h

/-- A time in an earlier slot of the same item is earlier. -/
theorem lt_of_slot {n i s s' o o' : Nat} (h : s < s') (ho : o < span) :
    slotTime n i s o < slotTime n i s' o' :=
  slotClock.slot h ho

/-- A time in an earlier item is earlier. -/
theorem lt_of_item {n i i' s s' o o' : Nat} (hs : s ≤ n) (hi : i < i') (ho : o < span) :
    slotTime n i s o < slotTime n i' s' o' :=
  slotClock.item hs hi ho

/-- Every fixed time is before every slot. -/
theorem fixed_lt {x n i s o : Nat} (h : x < base) : x < slotTime n i s o :=
  slotClock.fixed_lt h

/-- Every slot is after the fixed times. -/
theorem base_le {n i s o : Nat} : base ≤ slotTime n i s o :=
  slotClock.base _ _ _ _

/-- Every slot of the cluster's items is before the tail. -/
theorem lt_tail {n T i s o o' : Nat} (hs : s ≤ n) (hi : i < T) (ho : o < span) :
    slotTime n i s o < tailTime n T o' :=
  slotClock.item hs hi ho

/-- Within the tail an earlier offset is earlier. -/
theorem tail_lt {n T o o' : Nat} (h : o < o') : tailTime n T o < tailTime n T o' :=
  slotClock.lt_of_off h

/-! ### Bands -/

/-- The loader's band. -/
abbrev bandL : Nat := 0
/-- The MMA warp's band. -/
abbrev bandM : Nat := 100
/-- Softmax stage `st`'s band. -/
abbrev bandS (st : Nat) : Nat := 400 + 600 * st
/-- Correction stage `st`'s band. -/
abbrev bandC (st : Nat) : Nat := 600 + 600 * st
/-- The store warp's band. -/
abbrev bandST : Nat := 1600

/-! ### Fixed times -/

/-- The prologue's cluster arrival and wait. -/
abbrev clArriveT : Nat := 180
abbrev clWaitT : Nat := 182
/-- Every role's `setmaxnreg`. -/
abbrev regT : Nat := 190
/-- The idle warp's exit. -/
abbrev idleExitT : Nat := 192
/-- The MMA warp's allocation and its write of the base. -/
abbrev allocT : Nat := 200
abbrev allocWriteT : Nat := 202
/-- Barrier 2's first generation (`bar.sync 2, 416` of the MMA, softmax and correction warps). -/
abbrev bar0T : Nat := 210
/-- The MMA warp's base load and Q-offset shuffle. -/
abbrev ldBaseT : Nat := 212
abbrev shflQT : Nat := 214
/-- The correction's initial O-free arrival of stage `st`. -/
abbrev freeT (st : Nat) : Nat := 220 + 2 * st

/-! ### Role coordinates -/

/-- The loader's use `b` of slot `s` of item `i` (at the head `b < 4`: K, Q0, Q1, V; in a trip
`b < 2`: K, V), at offset `o < 16` within the use (wait, election, arrival, copies). -/
def loaderUse (n i s b o : Nat) : Nat := slotTime n i s (bandL + 16 * b + o)

/-- The MMA warp's event at offset `o < 300` of slot `s` of item `i`. -/
def mmaAt (n i s o : Nat) : Nat := slotTime n i s (bandM + o)

/-- The store warp's event at offset `o < 200` of item `i` (in slot `n`). -/
def storeAt (n i o : Nat) : Nat := slotTime n i n (bandST + o)

/-- The MMA warp's exit stage: `relinquish` `+3000`, `bar1` `+3010`, `arrivePeer` `+3012`,
`waitDealloc` `+3020`, `dealloc` `+3022`, `exit` `+3024`. -/
def mmaTail (n T o : Nat) : Nat := tailTime n T (3000 + o)

/-! ### Site tables -/

/-- The prologue's times: all below the cluster wait at 182, increasing along every warp's
path. Warp 0 makes the rank broadcast `shfl3` (`24`) between its second and third election
groups, so the groups from the third on are four later. -/
def prologue : Prologue.Site → Nat
  | .shfl0 => 0 | .shfl1 => 2 | .shfl2 => 4 | .elect12 => 6 | .init320 => 8 | .fence0 => 10
  | .elect e => 12 + 2 * (Prologue.groupStart e).val + 2 * e.val + (if 2 ≤ e.val then 4 else 0)
  | .init j => 14 + 2 * j.val + 2 * (Prologue.groupOf j).val +
      (if 2 ≤ (Prologue.groupOf j).val then 4 else 0)
  | .shfl3 => 24 | .fence1 => 170 | .clArrive => clArriveT | .clWait => clWaitT

/-- The idle warp's times. -/
def idle : Idle.Site → Nat
  | .setMaxReg => regT
  | .exit => idleExitT

/-- The slot of a softmax tile: tile 0 in slot 0, the trip's tile `t + 1` in slot `t + 1`. -/
def softSlot (d : Softmax.D) (lp : Bool) : Nat := if lp then d.t + 1 else 0

/-- The times of a softmax thread of stage `st`. A credit poll is timed in the slot of the tile
its arrival follows: `statsW 0` slot 0, `statsW 1` slot 1, `statsW 2` of trip `t` slot `t + 2`;
the last tile's `lSt` and `gen 2` are in slot `n`. -/
def softmax (n T st : Nat) (d : Softmax.D) : Nat :=
  let tm := fun s o => slotTime n d.i s (bandS st + o)
  match d.site with
  | .setMaxReg => regT
  | .bar0 => bar0T
  | .statsW 0 => tm 0 0
  | .statsW 1 => tm 1 0
  | .statsW 2 => tm (d.t + 2) 0
  | .statsW 3 => tailTime n T (bandS st)
  | .sW lp => tm (softSlot d lp) 2
  | .ld lp c => tm (softSlot d lp) (4 + 4 * c.val)
  | .ldW lp c => tm (softSlot d lp) (6 + 4 * c.val)
  | .alphaSt => tm (d.t + 1) 20
  | .gen 0 => tm 0 22
  | .gen 1 => tm (d.t + 1) 22
  | .gen 2 => tm n 22
  | .lSt => tm n 20
  | .pst lp c => tm (softSlot d lp) (if c.val < 3 then 24 + 2 * c.val else 34)
  | .pwait lp h => tm (softSlot d lp) (30 + 6 * h.val)
  | .pArr lp => tm (softSlot d lp) 32
  | .warpBar lp => tm (softSlot d lp) 38
  | .el lp => tm (softSlot d lp) 40
  | .p2Arr lp => tm (softSlot d lp) 42
  | .barEnd => tailTime n T 2000
  | .exit => tailTime n T 2002

/-- The times of a correction thread. Its stage-`st` events are in band `C st`: the first
generation in slot 0, trip `t`'s in slot `t + 1`, the final part in slot `n`. -/
def correction (n T : Nat) (d : Correction.D) : Nat :=
  let tm := fun (s : Nat) (st : Fin 2) o => slotTime n d.i s (bandC st.val + o)
  match d.site with
  | .setMaxReg => regT
  | .bar0 => bar0T
  | .free st => freeT st.val
  | .sync st .first => tm 0 st 0
  | .sync st .loop => tm (d.t + 1) st 0
  | .sync st .last => tm n st 2
  | .credit 0 => tm 0 0 2
  | .credit 1 => tm (d.t + 1) 0 58
  | .credit 2 => tm (d.t + 1) 1 58
  | .credit 3 => tm n 0 0
  | .credit 4 => tm n 0 6
  | .credit 5 => tm n 1 6
  | .ldA st => tm (d.t + 1) st 2
  | .vote st => tm (d.t + 1) st 4
  | .rld st j => tm (d.t + 1) st (6 + 6 * j.val)
  | .rldW st j => tm (d.t + 1) st (8 + 6 * j.val)
  | .rst st j => tm (d.t + 1) st (10 + 6 * j.val)
  | .rwait st => tm (d.t + 1) st 54
  | .oFree st false => tm (d.t + 1) st 56
  | .oFree st true => tm n st 174
  | .ldL st => tm n st 4
  | .oWait st => tm n st 8
  | .fWait st => tm n st 10
  | .fld st j => tm n st (12 + 20 * j.val)
  | .fldW st j => tm n st (14 + 20 * j.val)
  | .fst st j h el => tm n st (16 + 20 * j.val + 8 * h.val + 2 * el.val)
  | .fence st => tm n st 172
  | .staged st => tm n st 176
  | .tailWait => tailTime n T 1200
  | .barEnd => tailTime n T 2000
  | .exit => tailTime n T 2002

/-- The use's slot of the loader's item: the head's four uses in slot 0, a trip's K and V in
slot `t + 1`. -/
def loaderSlot (t : Nat) : Loader.UseK → Nat
  | .k | .v => t + 1
  | _ => 0

/-- The use's band index in its slot: K, Q0, Q1, V at the head, K, V in a trip. -/
def loaderBand : Loader.UseK → Nat
  | .k0 | .k => 0
  | .q0 | .v => 1
  | .q1 => 2
  | .v0 => 3

/-- The times of a loader thread. In a use at band index `b`: the head's broadcast `+0`, the
empty poll `+1`, the election of the arrival `+2`, the arrival `+3`, the election and copy `j`
`+4 + 2j` and `+5 + 2j`. The drain and the tail's arrival are in the tail from `+0`. -/
def loader (n T : Nat) (d : Loader.D) : Nat :=
  let use := fun (u : Loader.UseK) o => loaderUse n d.i (loaderSlot d.t u) (loaderBand u) o
  match d.site with
  | .setMaxReg => regT
  | .head => loaderUse n d.i 0 0 0
  | .wait u => use u 1
  | .elA u => use u 2
  | .arrive u => use u 3
  | .elC u j => use u (4 + 2 * j.val)
  | .copy u j => use u (5 + 2 * j.val)
  | .drain k => tailTime n T (2 * k.val)
  | .drainQ => tailTime n T 12
  | .elTail => tailTime n T 14
  | .arriveTail => tailTime n T 16
  | .exit => tailTime n T 18

/-- The offset of asm block `b`'s election in its slot (the head's blocks 0 and 1, a trip's 2
to 5, the last V's 6 and 7); its MMA `j` is at `+2 + j`, one later after a PV block's second
poll (`+8`). -/
def mmaBlock : Fin 8 → Nat
  | 0 => 8 | 1 => 28 | 2 => 10 | 3 => 26 | 4 => 46 | 5 => 64 | 6 => 18 | 7 => 42

/-- The offset of commit election `c` in its slot (its commit is two later). -/
def mmaCommit : Fin 12 → Nat
  | 0 => 20 | 1 => 40 | 2 => 44 | 3 => 36 | 4 => 60 | 5 => 74 | 6 => 78 | 7 => 0 | 8 => 4
  | 9 => 32 | 10 => 56 | 11 => 60

/-- The offset of an MMA warp site in its slot, in program order. The head slot 0: Q poll `+0`,
K poll `+2`, the Q1 poll `+24`; a trip's slot: the V poll `+0`, the P poll `+2`, the K poll
`+22`, the second P poll `+40`; the last slot: the commits `+0 … +6`, the V poll `+8`. -/
def mmaOff : Mma.Site → Nat
  | .qWait k => 24 * k.val
  | .kvWait 0 => 2 | .kvWait 1 => 0 | .kvWait 2 => 22 | .kvWait 3 => 8
  | .pWait 0 => 2 | .pWait 1 => 40 | .pWait 2 => 10 | .pWait 3 => 36
  | .p2Wait k _ => mmaBlock (Mma.pvGrp k) + 8
  | .shfl 0 => 4 | .shfl 1 => 6 | .shfl 2 => 26 | .shfl 3 => 4 | .shfl 4 => 6 | .shfl 5 => 8
  | .shfl 6 => 24 | .shfl 7 => 42 | .shfl 8 => 44 | .shfl 9 => 12 | .shfl 10 => 14
  | .shfl 11 => 16 | .shfl 12 => 38 | .shfl 13 => 40
  | .elM b => mmaBlock b
  | .mma b j => mmaBlock b + 2 + j.val + (if Mma.isPv b ∧ 6 ≤ j.val then 1 else 0)
  | .elC c => mmaCommit c
  | .commit c => mmaCommit c + 2
  | _ => 0

/-- The times of an MMA thread: the allocation and the base's read-back at their fixed times,
an item's events in the slot of their part (before the loop slot 0, in it slot `t + 1`, after it
slot `n`), the exit stage in the tail. -/
def mma (n T : Nat) (d : Mma.D) : Nat :=
  let at_ := fun s => mmaAt n d.i s (mmaOff d.site)
  match d.site with
  | .setMaxReg => regT
  | .alloc => allocT
  | .allocWrite => allocWriteT
  | .bar0 => bar0T
  | .ldBase => ldBaseT
  | .shflQ => shflQT
  | .relinquish => mmaTail n T 0
  | .bar1 => mmaTail n T 10
  | .arrivePeer => mmaTail n T 12
  | .waitDealloc => mmaTail n T 20
  | .dealloc => mmaTail n T 22
  | .exit => mmaTail n T 24
  | s => if Mma.region s = 1 then at_ 0 else if Mma.region s = 2 then at_ (d.t + 1) else at_ n

/-- The times of a store thread: item `i`'s events in its slot `n`'s band, in program order: the
staged poll of stage 0 `+0`, its stores `+2`, `+4` and commit `+6`, the poll of stage 1 `+8`,
its stores `+10`, `+12` and commit `+14`, the drains and frees `+16 … +22`; the exit in the
tail. -/
def store (n T : Nat) (d : Store.D) : Nat :=
  match d.site with
  | .setMaxReg => regT
  | .wait st => storeAt n d.i (8 * st.val)
  | .tma st h => storeAt n d.i (2 + 8 * st.val + 2 * h.val)
  | .commit st => storeAt n d.i (6 + 8 * st.val)
  | .drain r => storeAt n d.i (16 + 4 * r.val)
  | .free st => storeAt n d.i (18 + 4 * st.val)
  | .exit => tailTime n T 2000

/-- Every prologue time is before the role entries. -/
theorem prologue_lt_reg (s : Prologue.Site) : prologue s < regT := by
  cases s with
  | elect e =>
    have := (Prologue.groupStart e).isLt
    have := e.isLt
    simp only [prologue, regT]
    split_ifs <;> omega
  | init j =>
    have := (Prologue.groupOf j).isLt
    have := j.isLt
    simp only [prologue, regT]
    split_ifs <;> omega
  | _ => simp [prologue, clArriveT, clWaitT, regT]

end Time

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Progress
