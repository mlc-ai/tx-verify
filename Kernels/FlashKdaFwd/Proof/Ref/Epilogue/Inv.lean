-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Epilogue.Interface
public import Kernels.FlashKdaFwd.Proof.Ref.Epilogue.Tables
public import Kernels.FlashKdaFwd.Proof.Ref.TensorLoad

@[expose] public section

/-! # Epilogue phase: positions, closed-form events and the invariant (statements)

The epilogue (instructions 3113 to 3835) has no loop and one branch per role, so a thread
passes a fixed sequence of sites, by its role:

* a **compute thread** (`tid g < 128`): `bar7`, the 128 stores `st 0` … `st 127`, `fence`,
  `bar8`, `bar9`, `exit` (133 events);
* the **store leader** (`tid g = 160`, lane 0 of the store warp): `bar7`, `fence`, `bar8`, the
  16 tensor stores `ts 0` … `ts 15`, `commit`, `bwait`, `bar9`, `exit` (23 events);
* every **other thread** (the load warp and the lanes 1 to 31 of the store warp): `bar7`,
  `fence`, `bar8`, `bar9`, `exit` (5 events).

Definitions (`W n` is the 64-bit word of the number `n`; `S` the address `P.sharedBase` of the
kernel's shared memory in the block's window; registers by their id in the generated machine):

* `Pos`, `Pos.site`: the positions and their sites. `OnPath g pos`: the position is one of the
  thread's role. `ord g pos`: the ordinal of the position in the role's sequence, so that the
  thread is at `pos` before its event `k0 + ord g pos` when it entered the epilogue before its
  event `k0`.
* `swzN a`: the *swizzle* of a shared address: bit 4 is flipped when bit 7 is set (the code's
  `a xor ((a >> 3) and 16)`); the tensor maps of the state use the same permutation.
* `carryBase t`: the offset of the base pointer of compute thread `t` (four times the index
  that instructions 3115 to 3123 compute from the thread index: the warp in bits 10 and 11,
  the lane's two low bits in bits 6 and 7, its three high bits in bits 2 to 4).
* `stAddr P g j`: the shared address that store `j` of compute thread `g` writes: the swizzle
  of `S + carryBase (tid g) + stOff j` (`stOff` is the table of `Tables.lean`: `32768` plus the
  bits 5, 8, 9, 12 to 15 of the store's class).
* `finalOwner P l`: the compute thread whose stores write the byte `l` of the buffer.
* `finalSpec P L g i`: the `i`-th tensor store of the final state: through the map of parameter
  object 9, 8 key columns from column `8 i` of the 128 rows of plane `H * seq + head`, from the
  4096 bytes at offset `32768 + 4096 i` of the block's window.
* `Ev P L g pos e`: **the event of a position, in closed form.** No alternative is an
  undefined-behaviour event.
* `AtPos P g pos d`: the registers of the state at a position: the role facts, the thread's
  base pointer and the address register at a store (opaque slots `d.x r` that hold a generic
  shared pointer into the block's own window), the operand registers at a tensor store, the two
  flags that decide the branch after `bar8`.
* `bars pos`: the number of `bar.sync 0` the thread has made before the position: 6, 7, 8, 9.
* `Trail P L X g k0 pos`: **the history**: every earlier position `q` of the thread's role was
  passed at event `k0 + ord g q`, the event there was `Ev … q`, and `bars q` barriers preceded
  it.
* `Quiet P L g c`: the class `c` of events contains no event of the epilogue.
* `Inv P L X g k0 k d`: **the invariant** before the thread's event `k`, for a thread that
  entered the epilogue before its event `k0`: the state is at a position `pos` with its
  registers, `k = k0 + ord g pos`, the thread has made `bars pos` `bar.sync 0`, the history,
  and every quiet class has as many events among the first `k` as among the first `k0`. There
  is no exit condition: the phase ends with the thread's `ret`.
* `InvW P X g k0 k d`: the part of the invariant without the history and the counts of the
  other classes; it is what holds at the state after the thread's last event. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Epilogue
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section

/-! ### Positions -/

/-- The positions of the epilogue: its sites. -/
inductive Pos where
  /-- The first `bar.sync 0` (3113): the entry. -/
  | bar7
  /-- Store `j` of a compute thread (instruction `3132 + 5 j`). -/
  | st (j : Fin 128)
  /-- The proxy fence (3774). -/
  | fence
  /-- The second `bar.sync 0` (3775). -/
  | bar8
  /-- Tensor store `i` of the store leader (instruction `3786 + 3 i`). -/
  | ts (i : Fin 16)
  /-- The group commit (3832). -/
  | commit
  /-- The group wait (3833). -/
  | bwait
  /-- The third `bar.sync 0` (3834). -/
  | bar9
  /-- `ret` (3835). -/
  | exit
  deriving DecidableEq

/-- The site of a position. -/
def Pos.site : Pos → Site
  | .bar7 => .bar 7
  | .st j => .store ⟨18 + j.val, by omega⟩
  | .fence => .fenceProxy 3
  | .bar8 => .bar 8
  | .ts i => .tensorCopy ⟨242 + i.val, by omega⟩
  | .commit => .bulkCommit 1
  | .bwait => .bulkWait 1
  | .bar9 => .bar 9
  | .exit => .exit 0

/-- The position is one of the role of thread `g`: only a compute thread stores its carries,
only the store leader issues the tensor stores. -/
def OnPath (g : Nat) : Pos → Prop
  | .st _ => tid g < 128
  | .ts _ | .commit | .bwait => tid g = 160
  | _ => True

/-- The ordinal of a position in the sequence of the role of thread `g`. -/
def ord (g : Nat) : Pos → Nat
  | .bar7 => 0
  | .st j => 1 + j.val
  | .fence => if tid g < 128 then 129 else 1
  | .bar8 => if tid g < 128 then 130 else 2
  | .ts i => 3 + i.val
  | .commit => 19
  | .bwait => 20
  | .bar9 => if tid g < 128 then 131 else if tid g = 160 then 21 else 3
  | .exit => if tid g < 128 then 132 else if tid g = 160 then 22 else 4

/-- The `bar.sync 0` a thread has made before a position. -/
def bars : Pos → Nat
  | .bar7 => 6
  | .st _ | .fence | .bar8 => 7
  | .ts _ | .commit | .bwait | .bar9 => 8
  | .exit => 9

/-! ### Addresses -/

/-- The swizzle of a shared address: bit 4 is flipped when bit 7 is set. -/
def swzN (a : Nat) : Nat :=
  if a / 128 % 2 = 1 then (if a / 16 % 2 = 0 then a + 16 else a - 16) else a

/-- The offset of the base pointer of compute thread `t` from `shared_mem`. -/
def carryBase (t : Nat) : Nat := 1024 * (t / 32) + 64 * (t % 4) + 4 * (t % 32 / 4)

/-- **The shared address that store `j` of compute thread `g` writes** (four bytes). -/
def stAddr (P : Params) (g j : Nat) : Nat :=
  swzN (P.sharedBase + carryBase (tid g) + stOff j)

/-- **The compute thread that writes the byte `l` of the FP32 state buffer** in the epilogue
(its index in the block): undo the swizzle and read the thread's bits off the offset. -/
def finalOwner (P : Params) (l : Loc) : Nat :=
  32 * ((swzN l.addr - P.sharedBase - 32768) / 1024 % 4) +
    4 * ((swzN l.addr - P.sharedBase - 32768) / 4 % 8) +
    (swzN l.addr - P.sharedBase - 32768) / 64 % 4

/-- **The `i`-th tensor store of the final state** by the store leader `g`: through the map of
parameter object 9 at the coordinates `(8 i, 0, H * seq + head)` (key column, row, plane), from
byte `32768 + 4096 i` of the shared window of the thread's block; a tile store without
reduction. It is `Ref/TensorStore.lean: storeSpec P (g / L.block) 9 [8 * i, 0, H * seq + head]
(S + (32768 + 4096 * i))` (`Shapes.lean: finalSpec_eq`); it is written out here so that this
file does not depend on that one. -/
def finalSpec (P : Params) (L : Launch) (g i : Nat) : TensorStore.Spec :=
  ⟨⟨(preMap P 9).1, (preMap P 9).2,
    fun axis => (([8 * i, 0, P.heads * seqOf P g + headOf P g].getD axis.val 0 : Nat) : Int),
    ⟨.shared, g / L.block, P.sharedBase + (32768 + 4096 * i)⟩, none⟩, none⟩

/-! ### Events -/

/-- **The event of a position**, in closed form. -/
def Ev (P : Params) (L : Launch) (g : Nat) : Pos → Event → Prop
  | .bar7, e => e = ⟨3113, .bar 0 none .sync⟩
  | .st j, e => ∃ bs, e = ⟨(Pos.st j).site.pc,
      .wr { loc := ⟨.shared, g / L.block, stAddr P g j.val⟩, size := 4 } bs⟩
  | .fence, e => e = ⟨3774, .fenceProxy (.async (some (.shared .cta))) none⟩
  | .bar8, e => e = ⟨3775, .bar 0 none .sync⟩
  | .ts i, e => e = ⟨(Pos.ts i).site.pc,
      .tensorStore (P.objectBase 9) (finalSpec P L g i.val)⟩
  | .commit, e => e = ⟨3832, .bulkCommit⟩
  | .bwait, e => e = ⟨3833, .bulkWait .read 0⟩
  | .bar9, e => e = ⟨3834, .bar 0 none .sync⟩
  | .exit, e => e = ⟨3835, .exit⟩

/-! ### Register facts -/

/-- The generic pointer to byte `a` of the shared window of the block of thread `g`, as the
machine holds it in an opaque slot. -/
abbrev ownPtr (g a : Nat) : Value := .ptr 64 true (.shared (cta g) (cta g)) (W a)

/-- **The flags that decide the branch after the second barrier**: `%p81` says that the thread
is outside the store warp, and in the store warp `%p78` says that the lane was not elected
(`%r180 = 0`), so `%p82 = %p81 ∨ %p78` is false exactly for the store leader. -/
def Flags (g : Nat) (d : D) : Prop :=
  d.p 81 = decide (tid g < 160) ∧ (160 ≤ tid g → d.p 78 = decide (lane g ≠ 0))

/-- **The registers at a position.** -/
def AtPos (P : Params) (g : Nat) : Pos → D → Prop
  -- 3113: `%r1736` is the thread index, `%p77` the role; `%r180` in the store warp
  | .bar7, d => d.w 2042 = W (tid g) ∧ d.p 77 = decide (127 < tid g) ∧
      (160 ≤ tid g → d.w 486 = W (if lane g = 0 then 1 else 0))
  -- a store: the base pointer `%rd651` and the address register of the store
  | .st j, d => tid g < 128 ∧ d.w 2042 = W (tid g) ∧
      d.x 2897 = ownPtr g (P.sharedBase + carryBase (tid g)) ∧
      d.x (stPtr j.val) = ownPtr g (stAddr P g j.val)
  | .fence, d => Flags g d
  | .bar8, d => Flags g d
  -- a tensor store: `%r1783` = `S`, the zero coordinate `%r1749`, the plane `%r1750`, the
  -- source address and the first coordinate of this store
  | .ts i, d => tid g = 160 ∧ d.w 2089 = W P.sharedBase ∧ d.w 2055 = W 0 ∧
      d.w 2056 = W (P.heads * seqOf P g + headOf P g) ∧
      d.w (tsSrc i.val) = W (P.sharedBase + (32768 + 4096 * i.val)) ∧
      d.w (tsCoord i.val) = W (8 * i.val)
  | .commit, _ => tid g = 160
  | .bwait, _ => tid g = 160
  | .bar9, _ => True
  | .exit, _ => True

/-- **The reference invariant of a state at a position.** -/
structure RefAt (P : Params) (g : Nat) (pos : Pos) (d : D) : Prop where
  site : d.site = pos.site
  pos : AtPos P g pos d

/-! ### The invariant -/

variable (P : Params) (L : Launch) (X : Execution) (g : Nat)

/-- **The history of a thread in the epilogue**, at a position `pos`, for a thread that entered
before its event `k0`: every earlier position `q` of its role was passed at event
`k0 + ord g q`, with the closed-form event of `q` and `bars q` earlier `bar.sync 0`. -/
def Trail (k0 : Nat) (pos : Pos) : Prop :=
  ∀ q, OnPath g q → ord g q < ord g pos →
    ∃ e, X.get (g, k0 + ord g q) = some e ∧ Ev P L g q e ∧
      ((X.tr g).take (k0 + ord g q)).countP (Execution.isBarId 0) = bars q

/-- **A class of events that no event of the epilogue belongs to** (a named barrier, a matrix
event, a poll or an arrival on an mbarrier, a tensor load, a shuffle, …). -/
def Quiet (c : Event → Bool) : Prop := ∀ pos e, Ev P L g pos e → c e = false

/-- **The invariant of the epilogue** before the thread's event `k`, for a thread that entered
the epilogue before its event `k0`. -/
def Inv (k0 k : Nat) (d : D) : Prop :=
  ∃ pos, RefAt P g pos d ∧ OnPath g pos ∧ k = k0 + ord g pos ∧
    ((X.tr g).take k).countP (Execution.isBarId 0) = bars pos ∧ Trail P L X g k0 pos ∧
    ∀ c, Quiet P L g c → ((X.tr g).take k).countP c = ((X.tr g).take k0).countP c

/-- **The weak invariant**: the position, its registers, its ordinal and the number of
`bar.sync 0`. It also holds at the state after a thread's last event (where the history of
`Inv` may fail: the last event may be an undefined-behaviour event). -/
def InvW (k0 k : Nat) (d : D) : Prop :=
  ∃ pos, RefAt P g pos d ∧ OnPath g pos ∧ k = k0 + ord g pos ∧
    ((X.tr g).take k).countP (Execution.isBarId 0) = bars pos

variable {P L X g}

/-- The entry condition is the invariant at the first barrier. -/
theorem In.inv {k0 : Nat} {d : D} (h : In P X g k0 d) : Inv P L X g k0 k0 d :=
  ⟨.bar7, ⟨h.1.site, h.1.index, h.1.role, h.1.elected⟩, trivial, rfl, h.2,
    fun _ _ hq => absurd hq (Nat.not_lt_zero _), fun _ _ => rfl⟩

/-- The invariant gives the weak invariant. -/
theorem Inv.weak {k0 k : Nat} {d : D} (h : Inv P L X g k0 k d) : InvW P X g k0 k d := by
  obtain ⟨pos, h1, h2, h3, h4, -⟩ := h
  exact ⟨pos, h1, h2, h3, h4⟩

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Epilogue
