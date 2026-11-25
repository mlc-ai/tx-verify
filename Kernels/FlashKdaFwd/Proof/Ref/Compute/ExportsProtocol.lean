-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Compute.ExportsProtocolLib
public import Kernels.FlashKdaFwd.Proof.Protocol.Export

@[expose] public section

/-! # Compute phase: its share of the contracts of the protocol layer

The protocol layer (`Proof/Protocol/`) asks the thread layer for facts about the events of the
threads, bundled in contract structures. This file proves the part of each contract that is
about the events of a compute thread (thread index below 128 in its block) in the tile loop
(the Compute phase, instructions 2106 to 2944, and the `bar.sync 0` at 1402 that enters it).

**Shape of every theorem.** The event is `X.get (g, k) = some e`, at a followed state `s` of the
thread's machine (`hs : At (code L) X g k s`) that satisfies the phase invariant
(`hI : Inv P L X g j0 k s`; `j0` is the trace position at which the thread was at the phase's
entry). The conclusion is the contract field's. A theorem that needs an earlier event of the
thread (the fence before an arrival, the row writes before an arrival, the bytes of a row, the
barrier schedule) also takes the entry: a followed state `s0` at `j0` with the entry condition
(`h0 : At (code L) X g j0 s0`, `hin : In P L X g j0 s0`). The assembly supplies `Inv` for every
state of the phase (`Trace.lean: inv_at`) and does the case split over the phases. A field
whose event a compute thread never makes in the tile loop (an arrival on a "full" input
mbarrier, a tensor load, …) is stated with the field's conclusion and proved from the absurd
hypothesis, so that it is used in the same way.

Words: an *mbarrier* is one of the eleven 8-byte synchronization objects of a block
(`Protocol.Bar`: `loadFull s`, `loadEmpty s` for the three input stages, `storeFull o`,
`storeEmpty o` for the two output stages, `state`); a *poll* is an `mbarrier.try_wait`; tile `t`
of a block uses input stage `t % 3` and output stage `t % 2`; `T = tilesOf P g` is the number of
tiles of the block's sequence (`ctaTiles P (g / L.block)` in the protocol layer:
`ctaTiles_eq`).

## By contract field

| contract field | theorem here |
|---|---|
| `BarFacts.shape` | `bar_shape` |
| `BarFacts.bar0_pc`, `bar8_pc` | `bar0_pc`, `bar8_pc` |
| `BarFacts.sched` | `bar_sched` (hypothesis `hB`: five barrier events before the entry) |
| `BarFacts.bar0_le`, `bar8_le`, for a thread still in the phase | `bar0_le`, `bar8_le` |
| `BarFacts.bar0_exit`, `bar8_exit` | no exit in the phase (`no_exit`); `exit_counts` |
| `InitFacts.use_ev` | `use_ev`; no initialization in the phase (`no_mbInit`) |
| `LoadFacts.full_poll`, `empty_arrive` | `load_full_poll`, `load_empty_arrive` |
| `LoadFacts.full_arrive`, `empty_poll` | `load_full_arrive`, `load_empty_poll` (no such event) |
| `LoadFacts.full_issue`, `no_tensor_empty`, `StoreFacts.no_tensor` | `no_tensorIssue` |
| `LoadFacts.in_fence` | `in_fence` |
| `StoreFacts.full_arrive`, `empty_poll` | `store_full_arrive`, `store_empty_poll` |
| `StoreFacts.full_poll`, `empty_arrive` | `store_full_poll`, `store_empty_arrive` (no such event) |
| `StoreFacts.out_fence` | `out_fence` |
| `StateFacts.arrive`, `poll`, `issue` | `no_state`: no event names the state mbarrier |
| `StateAccFacts.phase` | `stateAcc_phase` |
| `StateAccFacts.owner` | `stateAcc_owner` (two threads in the phase), from `stateAcc_own` |
| the premise `hrow` of `StateAccFacts.acc_read` | `stateAcc_row` (a whole 16-byte row) |
| `LifeFacts.state_polled` | `state_polled`; from the exit on: `exit_state_polled` |
| `LifeFacts.full_polled`, `UnionFacts.polled` | `union_polled` (in the phase), `exit_polled` |
| `UnionFacts.thread`, classes `input` and `output` | `union_thread` |
| `UnionFacts.load`, `store`, `StoreCover.store_in` | `no_tensorIssue`, `no_tensorStore` |
| `UnionFacts.bar_fence` | `bar_fence` (hypothesis `hF`: the fence before the entry) |
| `StoreCover.out_cover` | `out_cover` |
| `StoreCover.matrix_len` | `matrix_len` |
| `StoreCover.out_lt` | `outOwner_lt` |
| `SafetyFacts.mbarFrame` (an mbarrier of the thread's block) | `mbar_own`, `mbar_compute` |
| the frame of the writes | `wr_shared` (a write of the phase is to shared memory) |

The basis of all of them: `event_at` (the event at a state of the invariant is the closed-form
event `EvAt` of the state's position, `ExportsProtocolLib.lean`), and by kind of event
`kinds_compute`, `bar_compute`, `wait_compute`, `arrive_compute`, `access_compute`.

The last section restates the facts in the exact form of the three structures `ComputeOwes` of
the assembly (`Ref/Assembly/FactsABase.lean`, `FactsB.lean`, `BuffersLib.lean`), one theorem per
field (`owes_*`).

## The owner functions

`outOwner P l`: the compute thread (its index in the block) that writes the byte `l` of an
output buffer: `32 * (x / 1024) + x % 512 / 16` for the byte at offset `x` of the buffer (each
warp owns 1024 bytes of it, in which each lane writes two 16-byte rows 512 bytes apart). It is
the expression of `Assembly.outOwner`, so the two are equal by `rfl`. `accOwner L l`: the
compute thread that reads and rewrites the byte `l` of the bfloat16 state copy in the tile loop.

## What the assembly adds

1. `bar_sched` and `exit_bars` take `hB`: the first `j0` events of the thread have exactly five
   barrier events. The phase's entry condition only says that five of them are `bar.sync 0`.
2. `bar_fence` takes `hF`: the event before the entry is the proxy fence (instruction 1401,
   the last event of the phase before); `bar0_index` says that the `bar.sync 0` of the phase is
   the event at the entry index `j0`.
3. The fields about a thread's whole trace (`bar0_le`, `bar8_le`, the exits) need the Epilogue
   for a thread that has left the phase: `exit_counts`, `exit_bars`, `exit_polled` give the
   counts at the phase's exit, which is the Epilogue's entry, and `exit_first` says that the
   exit state is the first one.

Everything is in the namespace `Compute.Proto`. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Compute.Proto
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Protocol (Bar uses computeThread loadLeader storeLeader bar0Before
  bar0Pcs barSched InShared InStateAcc InInput InOutput InUnion ctaTiles Owners ThreadClass)

noncomputable section
set_option linter.unusedVariables false
set_option maxRecDepth 4000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat} {e : Event}

/-! ### The owner functions -/

/-- **The compute thread that writes a byte of an output buffer** (its index in the block): for
the byte at offset `x` of its 4096-byte buffer, `32 * (x / 1024) + x % 512 / 16` (warp
`x / 1024`, lane `x % 512 / 16`). The two output buffers start at offset 86912 of the block's
shared window. This is the function to take as `Owners.out`; it is the same expression as
`Assembly.outOwner`. -/
def outOwner (P : Params) (l : Loc) : Nat :=
  32 * ((l.addr - (P.sharedBase + 86912)) % 4096 / 1024) +
    (l.addr - (P.sharedBase + 86912)) % 4096 % 512 / 16

/-- **The compute thread that accesses a byte of the bfloat16 state copy in the tile loop**
(its index in the block): the bytes 0 to 32767 of the block's shared window are 16-byte rows,
and each lane reads and rewrites sixteen of them. -/
def accOwner (L : Launch) (l : Loc) : Nat :=
  32 * ((l.addr - L.sharedBase) % 2048 / 512) + 16 * ((l.addr - L.sharedBase) % 256 / 128) +
    8 * ((l.addr - L.sharedBase) % 4096 / 2048) + (l.addr - L.sharedBase) % 128 / 16

/-- `StoreCover.out_lt`: the owner of a byte of an output buffer is a compute thread. -/
theorem outOwner_lt (P : Params) (l : Loc) : outOwner P l < 128 := by
  unfold outOwner
  omega

/-! ### The events of a position, by kind -/

/-- **A barrier event** is the `bar.sync 0` of the entry (instruction 1402) or the named barrier
`bar.sync 8, 128` of a tile (instruction 2913, position 264). -/
theorem EvAt.bar {pos : Pos} {pc id : Nat} {cnt : Option Nat} {mode : BarMode}
    (h : EvAt P L g pos ⟨pc, .bar id cnt mode⟩) :
    (pos = .entry ∧ pc = 1402 ∧ id = 0 ∧ cnt = none ∧ mode = .sync) ∨
      ∃ t, pos = .tile t 264 ∧ pc = 2913 ∧ id = 8 ∧ cnt = some 128 ∧ mode = .sync := by
  cases pos with
  | entry =>
    cases h
    exact .inl ⟨rfl, rfl, rfl, rfl, rfl⟩
  | tile t n =>
    simp only [EvAt] at h
    split_ifs at h
    · obtain ⟨ok, h⟩ := h
      cases h
    · obtain ⟨ok, h⟩ := h
      cases h
    · cases h
      subst_vars
      exact .inr ⟨t, rfl, rfl, rfl, rfl, rfl⟩
    · cases h
    · cases h
    · cases h
    · rcases h with ⟨op, own, recv, h⟩ | ⟨f, h⟩ <;> cases h
    · rcases h with ⟨bs, h, -⟩ | ⟨bs, h, -⟩ <;> cases h

/-- **A poll** is the acquiring poll of the "empty" mbarrier of the tile's output stage
(instruction 2144, position 0) or of the "full" mbarrier of the tile's input stage (2186,
position 1), with the parity of the tile's use of the stage. -/
theorem EvAt.wait {pos : Pos} {pc q : Nat} {m : Loc} {ok acq : Bool} {sc : MbarScope}
    (h : EvAt P L g pos ⟨pc, .wait m q ok acq sc⟩) :
    acq = true ∧ sc = .cta ∧ ∃ t,
      (pos = .tile t 0 ∧ pc = 2144 ∧ m = (Bar.storeEmpty (stage2 t)).loc L (g / L.block) ∧
        q = (t / 2 + 1) % 2) ∨
      (pos = .tile t 1 ∧ pc = 2186 ∧ m = (Bar.loadFull (stage3 t)).loc L (g / L.block) ∧
        q = t / 3 % 2) := by
  cases pos with
  | entry => cases h
  | tile t n =>
    simp only [EvAt] at h
    split_ifs at h
    · obtain ⟨ok', h⟩ := h
      cases h
      subst_vars
      exact ⟨rfl, rfl, t, .inl ⟨rfl, rfl, rfl, rfl⟩⟩
    · obtain ⟨ok', h⟩ := h
      cases h
      subst_vars
      exact ⟨rfl, rfl, t, .inr ⟨rfl, rfl, rfl, rfl⟩⟩
    · cases h
    · cases h
    · cases h
    · cases h
    · rcases h with ⟨op, own, recv, h⟩ | ⟨f, h⟩ <;> cases h
    · rcases h with ⟨bs, h, -⟩ | ⟨bs, h, -⟩ <;> cases h

/-- **An arrival** is one release arrival without transaction bytes on the "full" mbarrier of
the tile's output stage (instruction 2920, position 266) or on the "empty" mbarrier of the
tile's input stage (2928, position 267). -/
theorem EvAt.arrive {pos : Pos} {pc tx cnt : Nat} {m : Loc} {rel : Bool} {sc : MbarScope}
    (h : EvAt P L g pos ⟨pc, .arrive m tx cnt rel sc⟩) :
    tx = 0 ∧ cnt = 1 ∧ rel = true ∧ sc = .cta ∧ ∃ t,
      (pos = .tile t 266 ∧ pc = 2920 ∧ m = (Bar.storeFull (stage2 t)).loc L (g / L.block)) ∨
      (pos = .tile t 267 ∧ pc = 2928 ∧ m = (Bar.loadEmpty (stage3 t)).loc L (g / L.block)) := by
  cases pos with
  | entry => cases h
  | tile t n =>
    simp only [EvAt] at h
    split_ifs at h
    · obtain ⟨ok', h⟩ := h
      cases h
    · obtain ⟨ok', h⟩ := h
      cases h
    · cases h
    · cases h
    · cases h
      subst_vars
      exact ⟨rfl, rfl, rfl, rfl, t, .inl ⟨rfl, rfl, rfl⟩⟩
    · cases h
      subst_vars
      exact ⟨rfl, rfl, rfl, rfl, t, .inr ⟨rfl, rfl, rfl⟩⟩
    · rcases h with ⟨op, own, recv, h⟩ | ⟨f, h⟩ <;> cases h
    · rcases h with ⟨bs, h, -⟩ | ⟨bs, h, -⟩ <;> cases h

/-- **A read** is the read of the footprint of a position with a memory access that is no row
write. -/
theorem EvAt.rd {pos : Pos} {pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (h : EvAt P L g pos ⟨pc, .rd a bs⟩) :
    ∃ t n, pos = .tile t n ∧ (addrOf n).2.2 ≠ 0 ∧ a = accOf P L g t n ∧
      isWr (skOf n) = false := by
  cases pos with
  | entry => cases h
  | tile t n =>
    simp only [EvAt] at h
    split_ifs at h
    · obtain ⟨ok', h⟩ := h
      cases h
    · obtain ⟨ok', h⟩ := h
      cases h
    · cases h
    · cases h
    · cases h
    · cases h
    · rcases h with ⟨op, own, recv, h⟩ | ⟨f, h⟩ <;> cases h
    · rename_i ha
      rcases h with ⟨bs', h, hw⟩ | ⟨bs', h, -⟩
      · cases h
        exact ⟨t, n, rfl, ha, rfl, hw⟩
      · cases h

/-- **A write** is the write of the footprint of a row-write position (the second event of an
`stmatrix`). -/
theorem EvAt.wr {pos : Pos} {pc : Nat} {a : Acc} {bs : List Byte}
    (h : EvAt P L g pos ⟨pc, .wr a bs⟩) :
    ∃ t n, pos = .tile t n ∧ (addrOf n).2.2 ≠ 0 ∧ a = accOf P L g t n ∧
      isWr (skOf n) = true := by
  cases pos with
  | entry => cases h
  | tile t n =>
    simp only [EvAt] at h
    split_ifs at h
    · obtain ⟨ok', h⟩ := h
      cases h
    · obtain ⟨ok', h⟩ := h
      cases h
    · cases h
    · cases h
    · cases h
    · cases h
    · rcases h with ⟨op, own, recv, h⟩ | ⟨f, h⟩ <;> cases h
    · rename_i ha
      rcases h with ⟨bs', h, -⟩ | ⟨bs', h, hw⟩
      · cases h
      · cases h
        exact ⟨t, n, rfl, ha, rfl, hw⟩

/-- **The kinds of events of the phase**: a barrier, a poll, an arrival, a proxy fence, a read,
a write, a warp matrix event, or undefined behaviour (at a matrix instruction only). -/
theorem EvAt.kinds {pos : Pos} (h : EvAt P L g pos e) :
    (∃ id cnt m, e.kind = .bar id cnt m) ∨ (∃ l q ok acq sc, e.kind = .wait l q ok acq sc) ∨
      (∃ l tx n rel sc, e.kind = .arrive l tx n rel sc) ∨
      (∃ px sc, e.kind = .fenceProxy px sc) ∨ (∃ a bs, e.kind = .rd a bs) ∨
      (∃ a bs, e.kind = .wr a bs) ∨ (∃ op own recv, e.kind = .matrix op own recv) ∨
      ∃ f, e.kind = .ub f := by
  cases pos with
  | entry =>
    rw [show e = _ from h]
    exact .inl ⟨_, _, _, rfl⟩
  | tile t n =>
    simp only [EvAt] at h
    split_ifs at h
    · obtain ⟨ok, rfl⟩ := h
      exact .inr (.inl ⟨_, _, _, _, _, rfl⟩)
    · obtain ⟨ok, rfl⟩ := h
      exact .inr (.inl ⟨_, _, _, _, _, rfl⟩)
    · rw [h]
      exact .inl ⟨_, _, _, rfl⟩
    · rw [h]
      exact .inr (.inr (.inr (.inl ⟨_, _, rfl⟩)))
    · rw [h]
      exact .inr (.inr (.inl ⟨_, _, _, _, _, rfl⟩))
    · rw [h]
      exact .inr (.inr (.inl ⟨_, _, _, _, _, rfl⟩))
    · rcases h with ⟨op, own, recv, h⟩ | ⟨f, h⟩
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, _, _, h⟩))))))
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨_, h⟩))))))
    · rcases h with ⟨bs, h, -⟩ | ⟨bs, h, -⟩
      · exact .inr (.inr (.inr (.inr (.inl ⟨_, _, h⟩))))
      · exact .inr (.inr (.inr (.inr (.inr (.inl ⟨_, _, h⟩)))))

/-- A barrier event of another barrier than barrier 0 and barrier 8. -/
def otherBar (e : Event) : Bool :=
  Execution.isBar e && !Execution.isBarId 0 e && !Execution.isBarId 8 e

/-- The barrier events of a list are its `bar.sync 0`, its arrivals on barrier 8 and those on
the other barriers. -/
theorem countP_isBar (es : List Event) : es.countP Execution.isBar =
    es.countP (Execution.isBarId 0) + es.countP (Execution.isBarId 8) + es.countP otherBar := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    rw [List.countP_cons, List.countP_cons, List.countP_cons, List.countP_cons, ih]
    have key : (if Execution.isBar e = true then 1 else 0) =
        (if Execution.isBarId 0 e = true then 1 else 0) +
          (if Execution.isBarId 8 e = true then 1 else 0) +
          (if otherBar e = true then 1 else 0) := by
      obtain ⟨pc, k⟩ := e
      cases k with
      | bar id cnt mode =>
        by_cases h0 : id = 0
        · subst h0
          rfl
        · by_cases h8 : id = 8
          · subst h8
            rfl
          · simp [Execution.isBarId, Execution.isBar, otherBar, h0, h8]
      | _ => rfl
    omega

/-- No event of the phase is an arrival on another barrier than barrier 0 and barrier 8. -/
theorem EvAt.otherBar {pos : Pos} (h : EvAt P L g pos e) : otherBar e = false := by
  obtain ⟨pc, kd⟩ := e
  cases kd with
  | bar id cnt mode =>
    rcases h.bar with ⟨-, -, rfl, -⟩ | ⟨t, -, -, rfl, -⟩ <;> rfl
  | _ => rfl

/-! ### Where the access of a position lies -/

set_option synthInstance.maxSize 4096 in
/-- **The accesses of a tile by region** (a closed check of the phase's table `addrTab`): a
position with a memory access is between the polls and the named barrier, a row write has 16
bytes, and the access is

* a 16-byte row at a register of the bfloat16 state copy (`accRegs`), or
* a read of a 16-byte row at a register of the input stage (`inRegs`), or
* the row write of `stmatrix` 0 or 1 (positions 165 and 167) at the registers `%r1366`
  (id 1672) and `%r1371` (id 1677) of the output stage, or
* the read of one of the two 2-byte gate logits (`%r1642`, id 1948, plus 36864 or 36880), or
* the read of one of the sixteen 4-byte decay factors (`%r1708`, id 2014, plus
  `49280 + 32 i`). -/
theorem acc_tab : ∀ n < 268, (addrOf n).2.2 ≠ 0 → 2 ≤ n ∧ n < 264 ∧
    (isWr (skOf n) = true → (addrOf n).2.2 = 16) ∧
    (((addrOf n).1 ∈ accRegs ∧ (addrOf n).2.1 = 0 ∧ (addrOf n).2.2 = 16) ∨
      ((addrOf n).1 ∈ inRegs ∧ (addrOf n).2.1 = 0 ∧ (addrOf n).2.2 = 16 ∧
        isWr (skOf n) = false) ∨
      ((n = 165 ∧ (addrOf n).1 = 1672 ∨ n = 167 ∧ (addrOf n).1 = 1677) ∧
        (addrOf n).2.1 = 0 ∧ (addrOf n).2.2 = 16 ∧ isWr (skOf n) = true) ∨
      ((addrOf n).1 = 1948 ∧ ((addrOf n).2.1 = 36864 ∨ (addrOf n).2.1 = 36880) ∧
        (addrOf n).2.2 = 2 ∧ isWr (skOf n) = false) ∨
      ((addrOf n).1 = 2014 ∧ 49280 ≤ (addrOf n).2.1 ∧ (addrOf n).2.1 ≤ 49760 ∧
        (addrOf n).2.1 % 4 = 0 ∧ (addrOf n).2.2 = 4 ∧ isWr (skOf n) = false)) := by
  decide +kernel

/-- The sixteen rows of the bfloat16 state copy of a lane: a register of `accRegs` holds the
address of the lane's first row plus a multiple of 4096, or that plus 256. -/
theorem acc_row {t r : Nat} (hr : r ∈ accRegs) :
    ∃ K, regVal P g t r = P.sharedBase + accOff g + K ∧ (K % 4096 = 0 ∨ K % 4096 = 256) ∧
      K ≤ 28928 := by
  simp only [accRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  · exact ⟨0, rfl, by decide, by decide⟩
  all_goals exact ⟨_, rfl, by decide, by decide⟩

/-- The owner function of the bfloat16 state copy on the rows of a lane (a closed check over
the 8192 combinations): `w` the warp, `a + 8 * c + 16 * b` the lane, `jj` the second row of a
pair, `r` the byte in the row. -/
theorem accOwner_dec : ∀ w < 4, ∀ a < 8, ∀ b < 2, ∀ c < 2, ∀ jj < 2, ∀ r < 16,
    32 * ((512 * w + 16 * a + 128 * b + 2048 * c + 256 * jj + r) % 2048 / 512) +
      16 * ((512 * w + 16 * a + 128 * b + 2048 * c + 256 * jj + r) % 256 / 128) +
      8 * ((512 * w + 16 * a + 128 * b + 2048 * c + 256 * jj + r) % 4096 / 2048) +
      (512 * w + 16 * a + 128 * b + 2048 * c + 256 * jj + r) % 128 / 16 =
        32 * w + 16 * b + 8 * c + a := by decide +kernel

/-- A thread index below 128 from its warp and the three parts of its lane. -/
theorem tid_split : ∀ n < 128, 32 * (n / 32) + 16 * (n / 16 % 2) + 8 * (n / 8 % 2) + n % 8 = n := by
  decide +kernel

/-- The owner of a byte of a row of the bfloat16 state copy of a lane is the lane. -/
theorem accOwner_row {K r : Nat} (hc : tid g < 128) (hK : K % 4096 = 0 ∨ K % 4096 = 256)
    (hr : r < 16) :
    32 * ((accOff g + K + r) % 2048 / 512) + 16 * ((accOff g + K + r) % 256 / 128) +
      8 * ((accOff g + K + r) % 4096 / 2048) + (accOff g + K + r) % 128 / 16 = tid g := by
  obtain ⟨i, jj, hjj, rfl⟩ : ∃ i jj, jj < 2 ∧ K = 256 * jj + 4096 * i :=
    ⟨K / 4096, K % 4096 / 256, by omega, by omega⟩
  have hx : accOff g + (256 * jj + 4096 * i) + r =
      512 * (tid g / 32) + 16 * (tid g % 8) + 128 * (tid g / 16 % 2) +
        2048 * (tid g / 8 % 2) + 256 * jj + r + 4096 * i := by
    unfold accOff
    omega
  have hd := accOwner_dec (tid g / 32) (by omega) (tid g % 8) (by omega) (tid g / 16 % 2)
    (by omega) (tid g / 8 % 2) (by omega) jj hjj r hr
  have h1 : ∀ y, (y + 4096 * i) % 2048 = y % 2048 := fun y => by omega
  have h2 : ∀ y, (y + 4096 * i) % 256 = y % 256 := fun y => by omega
  have h3 : ∀ y, (y + 4096 * i) % 4096 = y % 4096 := fun y => by omega
  have h4 : ∀ y, (y + 4096 * i) % 128 = y % 128 := fun y => by omega
  rw [hx, h1, h2, h3, h4, hd]
  exact tid_split (tid g) hc

/-- The owner function of an output buffer on the rows of a lane (a closed check over the 4096
combinations): `w` the warp, `v` the lane, `h` the second row, `r` the byte in the row. -/
theorem outOwner_dec : ∀ w < 4, ∀ h < 2, ∀ v < 32, ∀ r < 16,
    32 * ((1024 * w + 512 * h + 16 * v + r) / 1024) +
      (1024 * w + 512 * h + 16 * v + r) % 512 / 16 = 32 * w + v := by decide +kernel

/-- A byte of an output buffer (offset `y`) is in one of the two rows of its owner: the row at
`1024 * warp + 16 * lane`, or the one 512 bytes further. -/
theorem outOwner_inv' : ∀ a < 16, ∀ b < 256,
    256 * a + b = 1024 * ((32 * ((256 * a + b) / 1024) + (256 * a + b) % 512 / 16) / 32) +
      512 * ((256 * a + b) % 1024 / 512) +
      16 * ((32 * ((256 * a + b) / 1024) + (256 * a + b) % 512 / 16) % 32) +
      (256 * a + b) % 16 := by decide +kernel

theorem outOwner_inv {y : Nat} (hy : y < 4096) :
    y = 1024 * ((32 * (y / 1024) + y % 512 / 16) / 32) + 512 * (y % 1024 / 512) +
      16 * ((32 * (y / 1024) + y % 512 / 16) % 32) + y % 16 := by
  have h := outOwner_inv' (y / 256) (by omega) (y % 256) (by omega)
  rwa [show 256 * (y / 256) + y % 256 = y by omega] at h

/-- **Where the bytes of the access of a position lie**: in the shared memory of the thread's
own block, and

* in the bfloat16 state copy (offsets below 32768), at a byte the thread owns (`accOwner`),
  and the access is a whole row: 16 bytes at a multiple of 16 from the base of the window; or
* in the input stage of the tile (the 18048 bytes from `32768 + 18048 * (t % 3)`), and the
  access is a read; or
* in the output stage of the tile (the 4096 bytes from `86912 + 4096 * (t % 2)`), at a byte the
  thread owns (`outOwner`), and the access is a row write. -/
theorem acc_region (hpre : Pre P L mem0) (hc : tid g < 128) {t n : Nat} (hn : n < 268)
    (ha : (addrOf n).2.2 ≠ 0) {l : Loc} (hl : (accOf P L g t n).Covers l) :
    l.space = .shared ∧ l.cta = g / L.block ∧
      ((L.sharedBase ≤ l.addr ∧ l.addr < L.sharedBase + 32768 ∧ accOwner L l = tid g ∧
          (accOf P L g t n).size = 16 ∧
          ∃ r, (accOf P L g t n).loc.addr = L.sharedBase + 16 * r) ∨
        (isWr (skOf n) = false ∧ L.sharedBase + (32768 + 18048 * (t % 3)) ≤ l.addr ∧
          l.addr < L.sharedBase + (32768 + 18048 * (t % 3 + 1))) ∨
        (isWr (skOf n) = true ∧ L.sharedBase + (86912 + 4096 * (t % 2)) ≤ l.addr ∧
          l.addr < L.sharedBase + (86912 + 4096 * (t % 2 + 1)) ∧ outOwner P l = tid g)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hl
  have h3' : regVal P g t (addrOf n).1 + (addrOf n).2.1 ≤ l.addr := h3
  have h4' : l.addr < regVal P g t (addrOf n).1 + (addrOf n).2.1 + (addrOf n).2.2 := h4
  refine ⟨h1, h2, ?_⟩
  have hb := hpre.sharedBase
  have b3 : t % 3 < 3 := Nat.mod_lt _ (by decide)
  have b2 : t % 2 < 2 := Nat.mod_lt _ (by decide)
  obtain ⟨-, -, -, hcls⟩ := acc_tab n hn ha
  rcases hcls with ⟨hr, hc0, hsz⟩ | ⟨hr, hc0, hsz, hw⟩ | ⟨hr, hc0, hsz, hw⟩ |
    ⟨hr, hc0, hsz, hw⟩ | ⟨hr, hc1, hc2, hc3, hsz, hw⟩
  · left
    obtain ⟨K, hK, hK4, hK2⟩ := acc_row (P := P) (g := g) (t := t) hr
    obtain ⟨h16, hlo, -⟩ := acc_addr hpre hc (t := t) hr
    have hal := hpre.sharedAlignment
    have ho := accOff_le hc
    have hrow : ∃ r, regVal P g t (addrOf n).1 + (addrOf n).2.1 = L.sharedBase + 16 * r :=
      ⟨(regVal P g t (addrOf n).1 - P.sharedBase) / 16, by omega⟩
    rw [hK, hc0] at h3' h4'
    rw [hsz] at h4'
    obtain ⟨r, hr16, hlr⟩ : ∃ r, r < 16 ∧ l.addr - L.sharedBase = accOff g + K + r :=
      ⟨l.addr - (P.sharedBase + accOff g + K), by omega, by omega⟩
    refine ⟨by omega, by omega, ?_, hsz, hrow⟩
    unfold accOwner
    rw [hlr]
    exact accOwner_row hc hK4 hr16
  · right
    left
    obtain ⟨-, hlo, hhi⟩ := in_addr hpre hc (t := t) hr
    rw [hc0] at h3' h4'
    rw [hsz] at h4'
    exact ⟨hw, by omega, by omega⟩
  · right
    right
    have hwl : warpOff g = 1024 * (tid g / 32) := rfl
    have hll : laneOff g = 16 * (tid g % 32) := rfl
    rw [hc0] at h3' h4'
    rw [hsz] at h4'
    -- the byte is byte `r` of row `h` (0 or 1) of the lane
    have hrow : ∃ h r, h < 2 ∧ r < 16 ∧ l.addr = P.sharedBase + 86912 + 4096 * (t % 2) +
        (1024 * (tid g / 32) + 512 * h + 16 * (tid g % 32) + r) := by
      rcases hr with ⟨-, hr⟩ | ⟨-, hr⟩
      · rw [hr, rv_1672] at h3' h4'
        exact ⟨0, l.addr - (P.sharedBase + 4096 * (t % 2) + (warpOff g + laneOff g) + 86912),
          by decide, by omega, by omega⟩
      · rw [hr, rv_1677] at h3' h4'
        exact ⟨1, l.addr - (P.sharedBase + 4096 * (t % 2) + (warpOff g + laneOff g) + 87424),
          by decide, by omega, by omega⟩
    obtain ⟨h, r, hh, hr16, hla⟩ := hrow
    have hd := outOwner_dec (tid g / 32) (by omega) h hh (tid g % 32) (by omega) r hr16
    have hmod : (l.addr - (P.sharedBase + 86912)) % 4096 =
        1024 * (tid g / 32) + 512 * h + 16 * (tid g % 32) + r := by
      rw [hla]
      omega
    refine ⟨hw, by omega, by omega, ?_⟩
    unfold outOwner
    rw [hmod, hd]
    omega
  · right
    left
    rw [hr] at h3' h4'
    rw [hsz] at h4'
    obtain ⟨-, hlo, hhi⟩ := gate_addr hpre hc (t := t) hc0
    exact ⟨hw, by omega, by omega⟩
  · right
    left
    obtain ⟨-, hlo, hhi⟩ := decay_addr hpre hc (t := t) hc1 hc2 hc3
    rw [hr] at h3' h4'
    rw [hsz] at h4'
    exact ⟨hw, by omega, by omega⟩

/-- The number of tiles of the thread's block, in the protocol layer's notation
(`Protocol.ctaTiles`, the `T` of `BarFacts` and `LifeFacts`). -/
theorem ctaTiles_eq (hpre : Pre P L mem0) : ctaTiles P (g / L.block) = tilesOf P g := by
  rw [hpre.block]
  rfl

/-- A thread is the thread with its index in its block, as a compute thread of the protocol
layer. -/
theorem computeThread_self (hpre : Pre P L mem0) (hc : g % L.block < 128) :
    g = computeThread L (g / L.block) ⟨g % L.block, hc⟩ :=
  (Protocol.thr_eq hpre.block g).symm

/-- The event of a thread access: a read, a write or an atomic of its footprint. -/
theorem access_event {i : Nat} {a : Acc} {w : Bool} (h : X.Access (g, i) a w) :
    ∃ ev, X.get (g, i) = some ev ∧ ((∃ bs, ev.kind = .rd a bs) ∨ (∃ bs, ev.kind = .wr a bs) ∨
      ∃ o n, ev.kind = .rmw a o n) := by
  rcases h with ⟨bs, ⟨pc, he⟩, -⟩ | ⟨bs, ⟨pc, he⟩, -⟩ | ⟨o, n, pc, he⟩
  · exact ⟨_, he, .inl ⟨bs, rfl⟩⟩
  · exact ⟨_, he, .inr (.inl ⟨bs, rfl⟩)⟩
  · exact ⟨_, he, .inr (.inr ⟨o, n, rfl⟩)⟩

/-- The known bytes of a row of known bytes: as many as the row has. -/
theorem reduceOption_length {α : Type} {l : List (Option α)} (h : l.all Option.isSome = true) :
    l.reduceOption.length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.all_cons, Bool.and_eq_true] at h
    cases a with
    | none => cases h.1
    | some v =>
      show (v :: l.reduceOption).length = (some v :: l).length
      rw [List.length_cons, List.length_cons, ih h.2]

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  {j0 k : Nat} {s : D} (hs : At (code L) X g k s) (hI : Inv P L X g j0 k s)
include hpre hX hs hI

/-- **An event at a state of the invariant** is the event of the state's position. -/
theorem event_at (he : X.get (g, k) = some e) :
    ∃ pos, InvAt P L X g j0 k pos s ∧ EvAt P L g pos e := by
  obtain ⟨pos, hR, h⟩ := hI
  exact ⟨pos, ⟨hR, h⟩, ev_at hpre hX hR hs he⟩

omit hX hs in
/-- A state of the invariant is a state of a compute thread. -/
theorem compute_at : g % L.block < 128 := by
  obtain ⟨pos, hR, -⟩ := hI
  rw [block_mod hpre]
  exact refAt_compute hR

/-! ### `Protocol.BarFacts` -/

/-- **A barrier event of the phase**: the sixth `bar.sync 0` at the entry (instruction 1402,
five `bar.sync 0` and no named barrier before it), or the named barrier of a tile `t`
(instruction 2913, six `bar.sync 0` and `t` named barriers before it). -/
theorem bar_compute {pc id : Nat} {cnt : Option Nat} {mode : BarMode}
    (he : X.get (g, k) = some ⟨pc, .bar id cnt mode⟩) :
    g % L.block < 128 ∧ mode = .sync ∧
      ((InvAt P L X g j0 k .entry s ∧ id = 0 ∧ cnt = none ∧ pc = 1402 ∧
          bar0Before X (g, k) = 5 ∧ ((X.tr g).take k).countP (Execution.isBarId 8) = 0) ∨
        ∃ t, InvAt P L X g j0 k (.tile t 264) s ∧ id = 8 ∧ cnt = some 128 ∧ pc = 2913 ∧
          bar0Before X (g, k) = 6 ∧ ((X.tr g).take k).countP (Execution.isBarId 8) = t ∧
          t < tilesOf P g) := by
  obtain ⟨pos, hA, hev⟩ := event_at hpre hX hs hI he
  have hc := compute_at hpre hI
  rcases hev.bar with ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨t, rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨h0, h8, -⟩ := cnt_entry hA.2.1
    exact ⟨hc, rfl, .inl ⟨hA, rfl, rfl, rfl, h0, h8⟩⟩
  · exact ⟨hc, rfl, .inr ⟨t, hA, rfl, rfl, rfl, cnt_bar0 hA.2.1, cnt_bar8 hA.2.1,
      hA.1.facts.lt⟩⟩

/-- `BarFacts.shape` for a barrier event of the phase. -/
theorem bar_shape {pc id : Nat} {cnt : Option Nat} {mode : BarMode}
    (he : X.get (g, k) = some ⟨pc, .bar id cnt mode⟩) :
    mode = .sync ∧ ((id = 0 ∧ cnt = none) ∨ (id = 8 ∧ cnt = some 128 ∧ g % L.block < 128)) := by
  obtain ⟨hc, hm, ⟨-, h1, h2, -⟩ | ⟨t, -, h1, h2, -⟩⟩ := bar_compute hpre hX hs hI he
  · exact ⟨hm, .inl ⟨h1, h2⟩⟩
  · exact ⟨hm, .inr ⟨h1, h2, hc⟩⟩

/-- `BarFacts.bar0_pc` for a `bar.sync 0` of the phase: the sixth, at instruction 1402. -/
theorem bar0_pc {pc : Nat} {cnt : Option Nat} {mode : BarMode}
    (he : X.get (g, k) = some ⟨pc, .bar 0 cnt mode⟩) :
    bar0Pcs[bar0Before X (g, k)]? = some pc := by
  obtain ⟨-, -, ⟨-, -, -, rfl, h5, -⟩ | ⟨t, -, h8, -⟩⟩ := bar_compute hpre hX hs hI he
  · rw [h5]
    rfl
  · exact absurd h8 (by decide)

/-- `BarFacts.bar8_pc` for a named barrier of the phase. -/
theorem bar8_pc {pc : Nat} {cnt : Option Nat} {mode : BarMode}
    (he : X.get (g, k) = some ⟨pc, .bar 8 cnt mode⟩) : pc = 2913 := by
  obtain ⟨-, -, ⟨-, h0, -⟩ | ⟨t, -, -, -, hpc, -⟩⟩ := bar_compute hpre hX hs hI he
  · exact absurd h0 (by decide)
  · exact hpc

omit hpre hX hs in
/-- `BarFacts.bar0_le` for a thread whose last state is in the phase (`k` the length of its
trace): at most six `bar.sync 0` before a state of the phase. -/
theorem bar0_le : bar0Before X (g, k) ≤ 6 := by
  obtain ⟨pos, hR, hled, -⟩ := hI
  show ((X.tr g).take k).countP (Execution.isBarId 0) ≤ 6
  cases pos with
  | entry =>
    rw [(cnt_entry hled).1]
    decide
  | tile t n => rw [cnt_bar0 hled]

omit hX hs in
/-- `BarFacts.bar8_le` for a thread whose last state is in the phase: at most one named barrier
per tile before a state of the phase. -/
theorem bar8_le :
    ((X.tr g).take k).countP (Execution.isBarId 8) ≤ ctaTiles P (g / L.block) := by
  obtain ⟨pos, hR, hled, -⟩ := hI
  rw [ctaTiles_eq hpre]
  cases pos with
  | entry =>
    rw [(cnt_entry hled).2.1]
    exact Nat.zero_le _
  | tile t n =>
    have h1 : t < tilesOf P g := hR.facts.lt
    rw [cnt_bar8 hled]
    unfold ind
    split_ifs <;> omega

/-! ### The kinds of event the phase does not have -/

/-- **The kinds of events of the phase**: a barrier, a poll, an arrival, a proxy fence, a read,
a write, a warp matrix event or undefined behaviour. -/
theorem kinds_compute (he : X.get (g, k) = some e) :
    (∃ id cnt m, e.kind = .bar id cnt m) ∨ (∃ l q ok acq sc, e.kind = .wait l q ok acq sc) ∨
      (∃ l tx n rel sc, e.kind = .arrive l tx n rel sc) ∨
      (∃ px sc, e.kind = .fenceProxy px sc) ∨ (∃ a bs, e.kind = .rd a bs) ∨
      (∃ a bs, e.kind = .wr a bs) ∨ (∃ op own recv, e.kind = .matrix op own recv) ∨
      ∃ f, e.kind = .ub f := by
  obtain ⟨pos, -, hev⟩ := event_at hpre hX hs hI he
  exact hev.kinds

/-- `LoadFacts.full_issue`, `no_tensor_empty`, `StoreFacts.no_tensor`, `StateFacts.issue`,
`UnionFacts.load`: no tensor load is issued in the phase. -/
theorem no_tensorIssue {pc al : Nat} {sp : TensorCopy.Spec}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue al sp⟩) : False := by
  rcases kinds_compute hpre hX hs hI he with ⟨_, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ |
    ⟨_, _, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, h⟩ <;> cases h

/-- `UnionFacts.store`, `StoreCover.store_in`, `StoreFacts.store_wait`: no tensor store is
issued in the phase. -/
theorem no_tensorStore {pc al : Nat} {sp : TensorStore.Spec}
    (he : X.get (g, k) = some ⟨pc, .tensorStore al sp⟩) : False := by
  rcases kinds_compute hpre hX hs hI he with ⟨_, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ |
    ⟨_, _, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, h⟩ <;> cases h

/-- `InitFacts.init_ev`, `init_once`: no mbarrier is initialized in the phase. -/
theorem no_mbInit {pc n : Nat} {m : Loc} (he : X.get (g, k) = some ⟨pc, .mbInit m n⟩) :
    False := by
  rcases kinds_compute hpre hX hs hI he with ⟨_, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ |
    ⟨_, _, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, h⟩ <;> cases h

/-- `BarFacts.bar0_exit`, `bar8_exit`, the `LifeFacts` fields: no thread exits in the phase. -/
theorem no_exit {pc : Nat} (he : X.get (g, k) = some ⟨pc, .exit⟩) : False := by
  rcases kinds_compute hpre hX hs hI he with ⟨_, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ |
    ⟨_, _, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, h⟩ <;> cases h

/-! ### Polls: `LoadFacts.full_poll`, `StoreFacts.empty_poll` -/

/-- **A poll of the phase**: acquiring, with six `bar.sync 0` before it, in a tile `t`: of the
"empty" mbarrier of output stage `t % 2`, polled successfully `t / 2` times before, with parity
`(t / 2 + 1) % 2`; or of the "full" mbarrier of input stage `t % 3`, polled successfully
`t / 3` times before, with parity `t / 3 % 2`. -/
theorem wait_compute {pc q : Nat} {m : Loc} {ok acq : Bool} {sc : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .wait m q ok acq sc⟩) :
    acq = true ∧ sc = .cta ∧ bar0Before X (g, k) = 6 ∧ ∃ t, t < tilesOf P g ∧
      ((InvAt P L X g j0 k (.tile t 0) s ∧ pc = 2144 ∧
          m = (Bar.storeEmpty (stage2 t)).loc L (g / L.block) ∧ q = (t / 2 + 1) % 2 ∧
          okPolls m ((X.tr g).take k) = t / 2) ∨
        (InvAt P L X g j0 k (.tile t 1) s ∧ pc = 2186 ∧
          m = (Bar.loadFull (stage3 t)).loc L (g / L.block) ∧ q = t / 3 % 2 ∧
          okPolls m ((X.tr g).take k) = t / 3)) := by
  obtain ⟨pos, hA, hev⟩ := event_at hpre hX hs hI he
  obtain ⟨rfl, rfl, t, ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩⟩ := hev.wait
  · exact ⟨rfl, rfl, cnt_bar0 hA.2.1, t, hA.1.facts.lt, .inl ⟨hA, rfl, rfl, rfl,
      (cnt_pe hA.2.1 (stage2 t)).trans (uses2_self t)⟩⟩
  · exact ⟨rfl, rfl, cnt_bar0 hA.2.1, t, hA.1.facts.lt, .inr ⟨hA, rfl, rfl, rfl,
      (cnt_pf hA.2.1 (stage3 t)).trans (uses3_self t)⟩⟩

/-- `LoadFacts.full_poll` for a poll of the phase. -/
theorem load_full_poll {pc p c : Nat} {st : Fin 3} {ok acq : Bool} {sc : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .wait ((Bar.loadFull st).loc L c) p ok acq sc⟩) :
    g % L.block < 128 ∧ c = g / L.block ∧
      p % 2 = okPolls ((Bar.loadFull st).loc L c) ((X.tr g).take k) % 2 ∧
      (ok = true → acq = true) := by
  obtain ⟨hacq, -, -, t, -, ⟨-, -, hm, -⟩ | ⟨-, -, hm, hq, hp⟩⟩ :=
    wait_compute hpre hX hs hI he
  · cases (Bar.loc_inj hm).1
  · refine ⟨compute_at hpre hI, (Bar.loc_inj hm).2, ?_, fun _ => hacq⟩
    rw [hp, hq]
    omega

/-- `LoadFacts.empty_poll`: a compute thread does not poll an "empty" input mbarrier in the
phase. -/
theorem load_empty_poll {pc p c : Nat} {st : Fin 3} {ok acq : Bool} {sc : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .wait ((Bar.loadEmpty st).loc L c) p ok acq sc⟩) :
    g = loadLeader L c ∧
      p % 2 = (okPolls ((Bar.loadEmpty st).loc L c) ((X.tr g).take k) + 1) % 2 ∧
      (ok = true → acq = true) := by
  obtain ⟨-, -, -, t, -, ⟨-, -, hm, -⟩ | ⟨-, -, hm, -⟩⟩ := wait_compute hpre hX hs hI he <;>
    cases (Bar.loc_inj hm).1

/-- `StoreFacts.empty_poll` for a poll of the phase. -/
theorem store_empty_poll {pc p c : Nat} {o : Fin 2} {ok acq : Bool} {sc : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .wait ((Bar.storeEmpty o).loc L c) p ok acq sc⟩) :
    g % L.block < 128 ∧ c = g / L.block ∧
      p % 2 = (okPolls ((Bar.storeEmpty o).loc L c) ((X.tr g).take k) + 1) % 2 ∧
      (ok = true → acq = true) := by
  obtain ⟨hacq, -, -, t, -, ⟨-, -, hm, hq, hp⟩ | ⟨-, -, hm, -⟩⟩ :=
    wait_compute hpre hX hs hI he
  · refine ⟨compute_at hpre hI, (Bar.loc_inj hm).2, ?_, fun _ => hacq⟩
    rw [hp, hq]
    omega
  · cases (Bar.loc_inj hm).1

/-- `StoreFacts.full_poll`: a compute thread does not poll a "full" output mbarrier in the
phase. -/
theorem store_full_poll {pc p c : Nat} {o : Fin 2} {ok acq : Bool} {sc : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .wait ((Bar.storeFull o).loc L c) p ok acq sc⟩) :
    g = storeLeader L c ∧
      p % 2 = okPolls ((Bar.storeFull o).loc L c) ((X.tr g).take k) % 2 ∧
      (ok = true → acq = true) := by
  obtain ⟨-, -, -, t, -, ⟨-, -, hm, -⟩ | ⟨-, -, hm, -⟩⟩ := wait_compute hpre hX hs hI he <;>
    cases (Bar.loc_inj hm).1

/-! ### Arrivals: `LoadFacts.empty_arrive`, `StoreFacts.full_arrive` -/

/-- **An arrival of the phase**: one release arrival without transaction bytes, with six
`bar.sync 0` before it, in a tile `t`: on the "full" mbarrier of output stage `t % 2` after
`t / 2` earlier arrivals on it and `t / 2 + 1` successful polls of the stage's "empty"
mbarrier; or on the "empty" mbarrier of input stage `t % 3` after `t / 3` earlier arrivals on
it and `t / 3 + 1` successful polls of the stage's "full" mbarrier. -/
theorem arrive_compute {pc tx cnt : Nat} {m : Loc} {rel : Bool} {sc : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .arrive m tx cnt rel sc⟩) :
    tx = 0 ∧ cnt = 1 ∧ rel = true ∧ sc = .cta ∧ bar0Before X (g, k) = 6 ∧
      ∃ t, t < tilesOf P g ∧
      ((InvAt P L X g j0 k (.tile t 266) s ∧ pc = 2920 ∧
          m = (Bar.storeFull (stage2 t)).loc L (g / L.block) ∧
          arrivals m ((X.tr g).take k) = t / 2 ∧
          okPolls ((Bar.storeEmpty (stage2 t)).loc L (g / L.block)) ((X.tr g).take k) =
            t / 2 + 1) ∨
        (InvAt P L X g j0 k (.tile t 267) s ∧ pc = 2928 ∧
          m = (Bar.loadEmpty (stage3 t)).loc L (g / L.block) ∧
          arrivals m ((X.tr g).take k) = t / 3 ∧
          okPolls ((Bar.loadFull (stage3 t)).loc L (g / L.block)) ((X.tr g).take k) =
            t / 3 + 1)) := by
  obtain ⟨pos, hA, hev⟩ := event_at hpre hX hs hI he
  obtain ⟨rfl, rfl, rfl, rfl, t, ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩⟩ := hev.arrive
  · exact ⟨rfl, rfl, rfl, rfl, cnt_bar0 hA.2.1, t, hA.1.facts.lt, .inl ⟨hA, rfl, rfl,
      (cnt_af hA.2.1 (stage2 t)).trans (uses2_self t),
      (cnt_pe hA.2.1 (stage2 t)).trans (uses2_succ t)⟩⟩
  · exact ⟨rfl, rfl, rfl, rfl, cnt_bar0 hA.2.1, t, hA.1.facts.lt, .inr ⟨hA, rfl, rfl,
      (cnt_ae hA.2.1 (stage3 t)).trans (uses3_self t),
      (cnt_pf hA.2.1 (stage3 t)).trans (uses3_succ t)⟩⟩

/-- `LoadFacts.empty_arrive` for an arrival of the phase. -/
theorem load_empty_arrive {pc tx cnt c : Nat} {st : Fin 3} {rel : Bool} {sc : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .arrive ((Bar.loadEmpty st).loc L c) tx cnt rel sc⟩) :
    g % L.block < 128 ∧ c = g / L.block ∧ tx = 0 ∧ cnt = 1 ∧ rel = true ∧
      arrivals ((Bar.loadEmpty st).loc L c) ((X.tr g).take k) + 1 ≤
        okPolls ((Bar.loadFull st).loc L c) ((X.tr g).take k) := by
  obtain ⟨h1, h2, h3, -, -, t, -, ⟨-, -, hm, -⟩ | ⟨-, -, hm, ha, hp⟩⟩ :=
    arrive_compute hpre hX hs hI he
  · cases (Bar.loc_inj hm).1
  · obtain ⟨hb, rfl⟩ := Bar.loc_inj hm
    obtain rfl : st = stage3 t := Bar.loadEmpty.inj hb
    exact ⟨compute_at hpre hI, rfl, h1, h2, h3, by rw [ha, hp]⟩

/-- `LoadFacts.full_arrive`: a compute thread does not arrive on a "full" input mbarrier in the
phase. -/
theorem load_full_arrive {pc tx cnt c : Nat} {st : Fin 3} {rel : Bool} {sc : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .arrive ((Bar.loadFull st).loc L c) tx cnt rel sc⟩) :
    g = loadLeader L c ∧ tx = 17984 ∧ cnt = 1 ∧ rel = true ∧
      arrivals ((Bar.loadFull st).loc L c) ((X.tr g).take k) + 1 ≤
        okPolls ((Bar.loadEmpty st).loc L c) ((X.tr g).take k) := by
  obtain ⟨-, -, -, -, -, t, -, ⟨-, -, hm, -⟩ | ⟨-, -, hm, -⟩⟩ :=
    arrive_compute hpre hX hs hI he <;> cases (Bar.loc_inj hm).1

/-- `StoreFacts.full_arrive` for an arrival of the phase. -/
theorem store_full_arrive {pc tx cnt c : Nat} {o : Fin 2} {rel : Bool} {sc : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .arrive ((Bar.storeFull o).loc L c) tx cnt rel sc⟩) :
    g % L.block < 128 ∧ c = g / L.block ∧ tx = 0 ∧ cnt = 1 ∧ rel = true ∧
      arrivals ((Bar.storeFull o).loc L c) ((X.tr g).take k) + 1 ≤
        okPolls ((Bar.storeEmpty o).loc L c) ((X.tr g).take k) := by
  obtain ⟨h1, h2, h3, -, -, t, -, ⟨-, -, hm, ha, hp⟩ | ⟨-, -, hm, -⟩⟩ :=
    arrive_compute hpre hX hs hI he
  · obtain ⟨hb, rfl⟩ := Bar.loc_inj hm
    obtain rfl : o = stage2 t := Bar.storeFull.inj hb
    exact ⟨compute_at hpre hI, rfl, h1, h2, h3, by rw [ha, hp]⟩
  · cases (Bar.loc_inj hm).1

/-- `StoreFacts.empty_arrive`: a compute thread does not arrive on an "empty" output mbarrier
in the phase. -/
theorem store_empty_arrive {pc tx cnt c : Nat} {o : Fin 2} {rel : Bool} {sc : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .arrive ((Bar.storeEmpty o).loc L c) tx cnt rel sc⟩) :
    g = storeLeader L c ∧ tx = 0 ∧ cnt = 1 ∧ rel = true ∧
      arrivals ((Bar.storeEmpty o).loc L c) ((X.tr g).take k) + 1 ≤
        okPolls ((Bar.storeFull o).loc L c) ((X.tr g).take k) := by
  obtain ⟨-, -, -, -, -, t, -, ⟨-, -, hm, -⟩ | ⟨-, -, hm, -⟩⟩ :=
    arrive_compute hpre hX hs hI he <;> cases (Bar.loc_inj hm).1

/-! ### `Protocol.InitFacts.use_ev` and the state mbarrier -/

/-- **The mbarrier an event of the phase names** is one of the four pipeline mbarriers of the
stages of a tile, of the thread's own block; six `bar.sync 0` precede the event. -/
theorem mbar_compute {m : Loc} (he : X.get (g, k) = some e) (hm : Frame.MbarOf e m) :
    bar0Before X (g, k) = 6 ∧ ∃ t,
      m = (Bar.storeEmpty (stage2 t)).loc L (g / L.block) ∨
      m = (Bar.loadFull (stage3 t)).loc L (g / L.block) ∨
      m = (Bar.storeFull (stage2 t)).loc L (g / L.block) ∨
      m = (Bar.loadEmpty (stage3 t)).loc L (g / L.block) := by
  obtain ⟨pc, kd⟩ := e
  rcases kinds_compute hpre hX hs hI he with ⟨_, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ |
    ⟨_, _, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, h⟩ <;>
    simp only at h <;> subst h
  · exact hm.elim
  · obtain rfl : m = _ := hm
    obtain ⟨-, -, hb, t, -, ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩⟩ := wait_compute hpre hX hs hI he
    · exact ⟨hb, t, .inl h⟩
    · exact ⟨hb, t, .inr (.inl h)⟩
  · obtain rfl : m = _ := hm
    obtain ⟨-, -, -, -, hb, t, -, ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩⟩ :=
      arrive_compute hpre hX hs hI he
    · exact ⟨hb, t, .inr (.inr (.inl h))⟩
    · exact ⟨hb, t, .inr (.inr (.inr h))⟩
  · exact hm.elim
  · exact hm.elim
  · exact hm.elim
  · exact hm.elim
  · exact hm.elim

/-- **An event of the phase that names an mbarrier names one of the eleven of the thread's
block.** -/
theorem mbar_own {m : Loc} (he : X.get (g, k) = some e) (hm : Frame.MbarOf e m) :
    ∃ b : Bar, m = b.loc L (g / L.block) := by
  obtain ⟨-, t, h | h | h | h⟩ := mbar_compute hpre hX hs hI he hm <;> exact ⟨_, h⟩

/-- `InitFacts.use_ev` for an event of the phase: the mbarrier it names is one of the thread's
own block, and the `bar.sync 0` that publishes it (the first or the second) is among the six
before the event. -/
theorem use_ev {m : Loc} (he : X.get (g, k) = some e) (hm : Frame.MbarOf e m)
    (hni : ∀ n, e.kind ≠ .mbInit m n) :
    ∃ b : Bar, m = b.loc L (g / L.block) ∧
      (b.gen + 1 ≤ bar0Before X (g, k) ∨
        g = b.owner L (g / L.block) ∧
          ∃ j pcj, j < k ∧ X.get (g, j) = some ⟨pcj, .mbInit m b.count⟩) := by
  obtain ⟨hb, t, h | h | h | h⟩ := mbar_compute hpre hX hs hI he hm
  · exact ⟨_, h, .inl (by rw [hb]; simp [Bar.gen])⟩
  · exact ⟨_, h, .inl (by rw [hb]; simp [Bar.gen])⟩
  · exact ⟨_, h, .inl (by rw [hb]; simp [Bar.gen])⟩
  · exact ⟨_, h, .inl (by rw [hb]; simp [Bar.gen])⟩

/-- `StateFacts.arrive`, `poll`, `issue`: no event of the phase names the state mbarrier of a
block. -/
theorem no_state {c : Nat} (he : X.get (g, k) = some e)
    (hm : Frame.MbarOf e (Bar.state.loc L c)) : False := by
  obtain ⟨-, t, h | h | h | h⟩ := mbar_compute hpre hX hs hI he hm <;>
    cases (Bar.loc_inj h).1

/-! ### Memory accesses: `StateAccFacts`, `UnionFacts.thread` -/

/-- **A memory access of the phase** (a read, a write or an atomic event): the read or the
write of the footprint of a position `n` of a tile `t`, between the polls and the named
barrier; it writes exactly at the row-write positions. -/
theorem access_compute {a : Acc} {w : Bool} (hacc : X.Access (g, k) a w) :
    ∃ t n, InvAt P L X g j0 k (.tile t n) s ∧ 2 ≤ n ∧ n < 264 ∧ (addrOf n).2.2 ≠ 0 ∧
      a = accOf P L g t n ∧ w = isWr (skOf n) := by
  rcases hacc with ⟨bs, ⟨pc, he⟩, rfl⟩ | ⟨bs, ⟨pc, he⟩, rfl⟩ | ⟨o, n, pc, he⟩
  · obtain ⟨pos, hA, hev⟩ := event_at hpre hX hs hI he
    obtain ⟨t, n, rfl, ha, rfl, hw⟩ := hev.rd
    obtain ⟨h2, h264, -⟩ := acc_tab n hA.1.facts.pos ha
    exact ⟨t, n, hA, h2, h264, ha, rfl, hw.symm⟩
  · obtain ⟨pos, hA, hev⟩ := event_at hpre hX hs hI he
    obtain ⟨t, n, rfl, ha, rfl, hw⟩ := hev.wr
    obtain ⟨h2, h264, -⟩ := acc_tab n hA.1.facts.pos ha
    exact ⟨t, n, hA, h2, h264, ha, rfl, hw.symm⟩
  · rcases kinds_compute hpre hX hs hI he with ⟨_, _, _, h⟩ | ⟨_, _, _, _, _, h⟩ |
      ⟨_, _, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, h⟩ <;>
      cases h

/-- The frame of the writes: a write event of the phase is in shared memory. -/
theorem wr_shared {pc : Nat} {a : Acc} {bs : List Byte}
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) : a.loc.space = .shared := by
  obtain ⟨pos, -, hev⟩ := event_at hpre hX hs hI he
  obtain ⟨t, n, -, -, rfl, -⟩ := hev.wr
  rfl

/-- **An access of the bfloat16 state copy in the phase**: of the thread's own block, after six
`bar.sync 0`, at a byte the thread owns. -/
theorem stateAcc_own {a : Acc} {w : Bool} {l : Loc} {c : Nat} (hacc : X.Access (g, k) a w)
    (hcov : a.Covers l) (hl : InStateAcc L c l) :
    c = g / L.block ∧ bar0Before X (g, k) = 6 ∧ accOwner L l = g % L.block := by
  obtain ⟨t, n, hA, -, -, ha, rfl, -⟩ := access_compute hpre hX hs hI hacc
  obtain ⟨-, hcta, hreg⟩ := acc_region hpre (refAt_compute hA.1) hA.1.facts.pos ha hcov
  obtain ⟨-, hlc, hlo, hhi⟩ := hl
  rcases hreg with ⟨-, -, ho, -⟩ | ⟨-, h1, -⟩ | ⟨-, h1, -⟩
  · exact ⟨hlc.symm.trans hcta, cnt_bar0 hA.2.1, by rw [block_mod hpre]; exact ho⟩
  · omega
  · omega

/-- `StateAccFacts.phase` for an access of the phase. -/
theorem stateAcc_phase {a : Acc} {w : Bool} {l : Loc} {c : Nat} (hacc : X.Access (g, k) a w)
    (hcov : a.Covers l) (hl : InStateAcc L c l) :
    g < L.threads ∧ c = g / L.block ∧
      (bar0Before X (g, k) = 3 ∨ bar0Before X (g, k) = 6) := by
  obtain ⟨ev, he, -⟩ := access_event hacc
  obtain ⟨h1, h2, -⟩ := stateAcc_own hpre hX hs hI hacc hcov hl
  exact ⟨Frame.lt_of_get hX he, h1, .inr h2⟩

/-- **An access of the bfloat16 state copy in the phase is an access of a whole row**: 16 bytes
at a multiple of 16 from the base of the block's shared window (the scalar loads and the rows
of the two stages are in the buffer region, from offset 32768 on). -/
theorem stateAcc_row {a : Acc} {w : Bool} {l : Loc} {c : Nat} (hacc : X.Access (g, k) a w)
    (hcov : a.Covers l) (hl : InStateAcc L c l) :
    a.size = 16 ∧ ∃ r, a.loc.addr = L.sharedBase + 16 * r := by
  obtain ⟨t, n, hA, -, -, ha, rfl, -⟩ := access_compute hpre hX hs hI hacc
  obtain ⟨-, hcta, hreg⟩ := acc_region hpre (refAt_compute hA.1) hA.1.facts.pos ha hcov
  obtain ⟨-, hlc, hlo, hhi⟩ := hl
  rcases hreg with ⟨-, -, -, h1, h2⟩ | ⟨-, h1, -⟩ | ⟨-, h1, -⟩
  · exact ⟨h1, h2⟩
  · omega
  · omega

/-- **An access of the union region in the phase** (offsets 32768 to 98304 of a block's shared
window): of the thread's own block, after six `bar.sync 0` and the poll of the state mbarrier,
in a tile `t`: a read of the input buffer of stage `t % 3`, between the tile's poll of the
"full" mbarrier and its arrival on the "empty" one; or a write of a byte the thread owns of the
output buffer of stage `t % 2`, between the tile's poll of the "empty" mbarrier and its arrival
on the "full" one. -/
theorem union_compute {a : Acc} {w : Bool} {l : Loc} {c : Nat} (hacc : X.Access (g, k) a w)
    (hcov : a.Covers l) (hl : InUnion L c l) :
    g / L.block = c ∧ okPolls (Bar.state.loc L c) ((X.tr g).take k) = 1 ∧
      bar0Before X (g, k) = 6 ∧ ∃ t,
      (w = false ∧ InInput L c (stage3 t).val l ∧
        arrivals ((Bar.loadEmpty (stage3 t)).loc L c) ((X.tr g).take k) + 1 ≤
          okPolls ((Bar.loadFull (stage3 t)).loc L c) ((X.tr g).take k)) ∨
      (w = true ∧ InOutput L c (stage2 t).val l ∧ outOwner P l = g % L.block ∧
        arrivals ((Bar.storeFull (stage2 t)).loc L c) ((X.tr g).take k) + 1 ≤
          okPolls ((Bar.storeEmpty (stage2 t)).loc L c) ((X.tr g).take k)) := by
  obtain ⟨t, n, hA, h2, h264, ha, rfl, rfl⟩ := access_compute hpre hX hs hI hacc
  obtain ⟨hsp, hcta, hreg⟩ := acc_region hpre (refAt_compute hA.1) hA.1.facts.pos ha hcov
  obtain ⟨-, hlc, hlo, hhi⟩ := hl
  obtain rfl : g / L.block = c := hcta.symm.trans hlc
  have hled := hA.2.1
  have i1 : ind 1 n = 1 := ite_eq_left (show 1 ≤ n by omega)
  have i2 : ind 2 n = 1 := ite_eq_left h2
  have i267 : ind 267 n = 0 := ite_eq_right (show ¬ 267 ≤ n by omega)
  refine ⟨rfl, cnt_state hled, cnt_bar0 hled, t, ?_⟩
  rcases hreg with ⟨h1, h3, -⟩ | ⟨hw, h1, h3⟩ | ⟨hw, h1, h3, ho⟩
  · omega
  · have hinp : InInput L (g / L.block) (stage3 t).val l := by
      unfold InInput InShared
      exact ⟨hsp, hlc, h1, h3⟩
    refine .inl ⟨hw, hinp, ?_⟩
    rw [cnt_ae hled (stage3 t), cnt_pf hled (stage3 t), i2]
    exact (Nat.add_le_add_right (uses3_self t).le 1).trans (uses3_succ t).ge
  · have hout : InOutput L (g / L.block) (stage2 t).val l := by
      unfold InOutput InShared
      exact ⟨hsp, hlc, h1, h3⟩
    refine .inr ⟨hw, hout, by rw [block_mod hpre]; exact ho, ?_⟩
    rw [cnt_af hled (stage2 t), cnt_pe hled (stage2 t), i1, i267]
    exact (Nat.add_le_add_right (uses2_self t).le 1).trans (uses2_succ t).ge

/-- `UnionFacts.thread` for an access of the phase, for owner functions `O` with
`O.out = outOwner P`: the classes `input` and `output`. -/
theorem union_thread {O : Owners} (hO : O.out = outOwner P) {a : Acc} {w : Bool} {l : Loc}
    {c : Nat} (hacc : X.Access (g, k) a w) (hcov : a.Covers l) (hl : InUnion L c l) :
    g / L.block = c ∧ 1 ≤ okPolls (Bar.state.loc L c) ((X.tr g).take k) ∧
      ThreadClass L X O c g k w l := by
  obtain ⟨rfl, hst, hbar, t, ⟨hw, hinp, hgate⟩ | ⟨hw, hout, hown, hgate⟩⟩ :=
    union_compute hpre hX hs hI hacc hcov hl
  · exact ⟨rfl, hst.ge, .input ⟨g % L.block, compute_at hpre hI⟩ (stage3 t)
      (computeThread_self hpre _) hw hbar hinp hgate⟩
  · exact ⟨rfl, hst.ge, .output ⟨g % L.block, compute_at hpre hI⟩ (stage2 t)
      (computeThread_self hpre _) hw hbar hout hgate (by rw [hO]; exact hown)⟩

omit hpre hX hs in
/-- `LifeFacts.state_polled`, for a thread at a state of the phase: it has polled the state
mbarrier of its block successfully (in the startup phase). -/
theorem state_polled : 1 ≤ okPolls (Bar.state.loc L (g / L.block)) ((X.tr g).take k) := by
  obtain ⟨pos, hR, hled, -⟩ := hI
  cases pos with
  | entry => exact (cnt_entry hled).2.2.ge
  | tile t n => exact (cnt_state hled).ge

omit hpre hX hs in
/-- `UnionFacts.polled` for an event of the phase: none has seven `bar.sync 0` before it. -/
theorem union_polled {c : Nat} (st : Fin 3) (a : Fin 128) (hga : g = computeThread L c a)
    (h7 : 7 ≤ bar0Before X (g, k)) :
    uses 3 (ctaTiles P c) st ≤ okPolls ((Bar.loadFull st).loc L c) ((X.tr g).take k) := by
  have h6 : bar0Before X (g, k) ≤ 6 := bar0_le hI
  omega

end

/-- `StateAccFacts.owner` for two accesses of the phase: two compute threads that access one
byte of the bfloat16 state copy in the tile loop are the same thread. -/
theorem stateAcc_owner (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    {g h j0 j0' k k' : Nat} {s s' : D} (hs : At (code L) X g k s)
    (hI : Inv P L X g j0 k s) (hs' : At (code L) X h k' s') (hI' : Inv P L X h j0' k' s')
    {a b : Acc} {w w' : Bool} {l : Loc} {c : Nat} (ha : X.Access (g, k) a w)
    (hb : X.Access (h, k') b w') (hca : a.Covers l) (hcb : b.Covers l)
    (hl : InStateAcc L c l) : g = h := by
  obtain ⟨h1, -, h2⟩ := stateAcc_own hpre hX hs hI ha hca hl
  obtain ⟨h3, -, h4⟩ := stateAcc_own hpre hX hs' hI' hb hcb hl
  have e1 := Nat.div_add_mod g L.block
  have e2 := Nat.div_add_mod h L.block
  rw [← h1, ← h2] at e1
  rw [← h3, ← h4] at e2
  exact e1.symm.trans e2

/-! ### Earlier events: the barrier schedule, the fences, the rows -/

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads) {j0 k : Nat} {s0 s : D} (h0 : At (code L) X g j0 s0)
  (hin : In P L X g j0 s0) (hs : At (code L) X g k s) (hI : Inv P L X g j0 k s)
include hpre hX hg h0 hin hs hI

/-- **The barrier events before a state of the phase** are the thread's `bar.sync 0` and its
named barriers, when there are five barrier events before the entry (`hB`). -/
theorem bars_count (hk : k ≤ (X.tr g).length)
    (hB : ((X.tr g).take j0).countP Execution.isBar = 5) :
    ((X.tr g).take k).countP Execution.isBar =
      ((X.tr g).take k).countP (Execution.isBarId 0) +
        ((X.tr g).take k).countP (Execution.isBarId 8) := by
  have hjk : j0 ≤ k := by
    obtain ⟨pos, -, -, h, -⟩ := hI
    exact h
  have h1 : ((X.tr g).take k).countP otherBar = ((X.tr g).take j0).countP otherBar :=
    countP_take_eq otherBar hjk fun i ev hi0 hik hev => by
      obtain ⟨si, hsi, pos, hR, -⟩ := inv_before hpre hX hg h0 hin hk hs hI hi0 hik.le
      exact (ev_at hpre hX hR hsi hev).otherBar
  have h2 := countP_isBar ((X.tr g).take j0)
  have h3 := countP_isBar ((X.tr g).take k)
  have h4 : ((X.tr g).take j0).countP (Execution.isBarId 0) = 5 := congrArg Led.bar0 hin.2
  omega

/-- `BarFacts.sched` for a barrier event of the phase. `hB`: the first `j0` events of the
thread (the events before the phase's entry) have exactly five barrier events. -/
theorem bar_sched (hB : ((X.tr g).take j0).countP Execution.isBar = 5) {pc id : Nat}
    {cnt : Option Nat} {mode : BarMode} (he : X.get (g, k) = some ⟨pc, .bar id cnt mode⟩) :
    (id, cnt, mode) = barSched (decide (g % L.block < 128)) (ctaTiles P (g / L.block))
      (((X.tr g).take k).countP Execution.isBar) := by
  have hk : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  have hc := bars_count hpre hX hg h0 hin hs hI hk hB
  have hd : decide (g % L.block < 128) = true := decide_eq_true (compute_at hpre hI)
  rw [hc, ctaTiles_eq hpre, hd]
  unfold barSched
  obtain ⟨-, rfl, ⟨-, rfl, rfl, -, h5, h8⟩ | ⟨t, -, rfl, rfl, -, h6, h8, ht⟩⟩ :=
    bar_compute hpre hX hs hI he
  · have h5' : ((X.tr g).take k).countP (Execution.isBarId 0) = 5 := h5
    rw [h5', h8, ite_eq_right (by rintro ⟨-, h, -⟩; omega)]
  · have h6' : ((X.tr g).take k).countP (Execution.isBarId 0) = 6 := h6
    rw [h6', h8, ite_eq_left ⟨rfl, by omega, by omega⟩]

omit hg in
/-- **The `bar.sync 0` of the phase is the event at the entry index.** -/
theorem bar0_index {pc : Nat} {cnt : Option Nat} {mode : BarMode}
    (he : X.get (g, k) = some ⟨pc, .bar 0 cnt mode⟩) : k = j0 := by
  have hk : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  obtain ⟨-, -, ⟨hA, -⟩ | ⟨t, -, h8, -⟩⟩ := bar_compute hpre hX hs hI he
  · exact entry_at hpre hX h0 hin hk hA
  · exact absurd h8 (by decide)

omit hg in
/-- `UnionFacts.bar_fence` for the `bar.sync 0` of the phase (the thread's sixth, at
instruction 1402). `hF`: the event before the phase's entry is the proxy fence (instruction
1401, the last event of the phase before). -/
theorem bar_fence
    (hF : 0 < j0 ∧ ∃ pcf, X.get (g, j0 - 1) =
      some ⟨pcf, .fenceProxy (.async (some (.shared .cta))) none⟩)
    {pc : Nat} {cnt : Option Nat} {mode : BarMode}
    (he : X.get (g, k) = some ⟨pc, .bar 0 cnt mode⟩)
    (hb : bar0Before X (g, k) = 5 ∨ bar0Before X (g, k) = 7) :
    0 < k ∧ ∃ pcf, X.get (g, k - 1) =
      some ⟨pcf, .fenceProxy (.async (some (.shared .cta))) none⟩ := by
  obtain rfl := bar0_index hpre hX h0 hin hs hI he
  exact hF

omit hI in
/-- **The two events before the second arrival of a tile**: the proxy fence and the first
arrival. -/
theorem before_arriveE {t : Nat} (hk : k ≤ (X.tr g).length)
    (hA : InvAt P L X g j0 k (.tile t 267) s) :
    2 ≤ k ∧ X.get (g, k - 2) = some ⟨2914, .fenceProxy (.async (some (.shared .cta))) none⟩ ∧
      X.get (g, k - 1) = some ⟨2920,
        .arrive ((Bar.storeFull (stage2 t)).loc L (g / L.block)) 0 1 true .cta⟩ := by
  obtain ⟨hk2, s2, hs2, hA2⟩ := back hpre hX hg h0 hin hk hs hA 2 (by decide)
  obtain ⟨-, s1, hs1, hA1⟩ := back hpre hX hg h0 hin hk hs hA 1 (by decide)
  obtain ⟨e2, he2⟩ : ∃ e2, X.get (g, k - 2) = some e2 :=
    ⟨_, List.getElem?_eq_getElem (show k - 2 < (X.tr g).length by omega)⟩
  obtain ⟨e1, he1⟩ : ∃ e1, X.get (g, k - 1) = some e1 :=
    ⟨_, List.getElem?_eq_getElem (show k - 1 < (X.tr g).length by omega)⟩
  have hev2 : EvAt P L g (.tile t 265) e2 := ev_at hpre hX hA2.1 hs2 he2
  have hev1 : EvAt P L g (.tile t 266) e1 := ev_at hpre hX hA1.1 hs1 he1
  rw [evAt_265.mp hev2] at he2
  rw [evAt_266.mp hev1] at he1
  exact ⟨hk2, he2, he1⟩

/-- `LoadFacts.in_fence` for an arrival of the phase on the "empty" mbarrier of an input stage:
the proxy fence of the tile (instruction 2914) is two events before the arrival, after every
earlier memory access of the thread. -/
theorem in_fence {i pce tx cnt : Nat} {a : Acc} {w : Bool} {st : Fin 3} {rel : Bool}
    {sc : MbarScope} (hacc : X.Access (g, i) a w) (hik : i < k)
    (he : X.get (g, k) =
      some ⟨pce, .arrive ((Bar.loadEmpty st).loc L (g / L.block)) tx cnt rel sc⟩) :
    ∃ f pcf, i < f ∧ f < k ∧
      X.get (g, f) = some ⟨pcf, .fenceProxy (.async (some (.shared .cta))) none⟩ := by
  have hk : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  obtain ⟨-, -, -, -, -, t, -, ⟨-, -, hm, -⟩ | ⟨hA, -⟩⟩ := arrive_compute hpre hX hs hI he
  · cases (Bar.loc_inj hm).1
  · obtain ⟨hk2, hf, ha⟩ := before_arriveE hpre hX hg h0 hin hs hk hA
    obtain ⟨ev, hev, hkind⟩ := access_event hacc
    refine ⟨k - 2, 2914, ?_, by omega, hf⟩
    by_contra hlt
    obtain rfl | rfl : i = k - 1 ∨ i = k - 2 := by omega
    · rw [ha] at hev
      obtain rfl := Option.some.inj hev
      rcases hkind with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h
    · rw [hf] at hev
      obtain rfl := Option.some.inj hev
      rcases hkind with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h

/-- `StoreFacts.out_fence` for an arrival of the phase on the "full" mbarrier of an output
stage: the proxy fence of the tile (instruction 2914) is the event before the arrival, after
every earlier memory access of the thread. -/
theorem out_fence {i pce tx cnt : Nat} {a : Acc} {w : Bool} {o : Fin 2} {rel : Bool}
    {sc : MbarScope} (hacc : X.Access (g, i) a w) (hik : i < k)
    (he : X.get (g, k) =
      some ⟨pce, .arrive ((Bar.storeFull o).loc L (g / L.block)) tx cnt rel sc⟩) :
    ∃ f pcf, i < f ∧ f < k ∧
      X.get (g, f) = some ⟨pcf, .fenceProxy (.async (some (.shared .cta))) none⟩ := by
  have hk : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  obtain ⟨-, -, -, -, -, t, -, ⟨hA, -⟩ | ⟨-, -, hm, -⟩⟩ := arrive_compute hpre hX hs hI he
  · obtain ⟨hk1, s1, hs1, hA1⟩ := back hpre hX hg h0 hin hk hs hA 1 (by decide)
    obtain ⟨e1, he1⟩ : ∃ e1, X.get (g, k - 1) = some e1 :=
      ⟨_, List.getElem?_eq_getElem (show k - 1 < (X.tr g).length by omega)⟩
    have hev1 : EvAt P L g (.tile t 265) e1 := ev_at hpre hX hA1.1 hs1 he1
    rw [evAt_265.mp hev1] at he1
    obtain ⟨ev, hev, hkind⟩ := access_event hacc
    refine ⟨k - 1, 2914, ?_, by omega, he1⟩
    by_contra hlt
    obtain rfl : i = k - 1 := by omega
    rw [he1] at hev
    obtain rfl := Option.some.inj hev
    rcases hkind with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, _, h⟩ <;> cases h
  · cases (Bar.loc_inj hm).1

/-- `StoreCover.matrix_len` for a write event of the phase: the write of an `stmatrix` lane
carries the 16 bytes the lane received at the instruction's matrix event, one event earlier.
(The entry is needed: the bytes are part of the state's site, and that there are 16 of them is
a fact about the step that led to the state.) -/
theorem matrix_len {pc : Nat} {a : Acc} {bs : List Byte}
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) : bs.length = a.size := by
  have hk : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  obtain ⟨pos, hA, hev⟩ := event_at hpre hX hs hI he
  obtain ⟨t, n, rfl, ha, rfl, hw⟩ := hev.wr
  have hn : n < 268 := hA.1.facts.pos
  obtain ⟨h2, -, hsz, -⟩ := acc_tab n hn ha
  have h3 : 3 ≤ n := by
    rcases Nat.lt_or_ge n 3 with h | h
    · obtain rfl : n = 2 := by omega
      cases hw
    · exact h
  obtain ⟨-, s1, e1, hs1, hA1, he1, hnext⟩ := step_back hpre hX hg h0 hin hk hs hA h3
  obtain ⟨site1, w1, p1, x1⟩ := s1
  have hw' : isWr (skOf (n - 1 + 1)) = true := by
    rw [show n - 1 + 1 = n by omega]
    exact hw
  obtain ⟨j, row, hsite, hlen, hall⟩ :=
    st_row (show n - 1 < 268 by omega) hw' hA1.1.site hnext
  obtain ⟨tt, ins, o, hat, -, hc, hf⟩ := Frame.fired_site (sounds hpre) hX he hs
  obtain ⟨site, w, p, x⟩ := s
  rcases acc_at hpre hA.1.facts hA.1.site hat hc hf ha with ⟨bs', -, hw2⟩ |
    ⟨j', row', hsite', hkind, -⟩
  · rw [hw] at hw2
    cases hw2
  · obtain rfl : site = .matrixStoreWr j row := hsite
    obtain ⟨-, rfl⟩ := Site.matrixStoreWr.inj hsite'
    cases hkind
    show row.reduceOption.length = (addrOf n).2.2
    rw [reduceOption_length hall, hlen, hsz hw]

/-- `StoreCover.out_cover` for an arrival of the phase on the "full" mbarrier of an output
stage: the thread wrote each byte it owns (`outOwner`) of the stage's output buffer at one of
its two row writes of the tile (`stmatrix` 0 and 1, 101 and 99 events before the arrival),
after its previous arrival on that mbarrier. -/
theorem out_cover {pc tx cnt : Nat} {rel : Bool} {sc : MbarScope} (o : Fin 2) {l : Loc}
    (he : X.get (g, k) =
      some ⟨pc, .arrive ((Bar.storeFull o).loc L (g / L.block)) tx cnt rel sc⟩)
    (hl : InOutput L (g / L.block) o.val l) (hown : outOwner P l = g % L.block) :
    ∃ i pcw aw bs, i < k ∧ X.get (g, i) = some ⟨pcw, .wr aw bs⟩ ∧ aw.Covers l ∧
      arrivals ((Bar.storeFull o).loc L (g / L.block)) ((X.tr g).take i) =
        arrivals ((Bar.storeFull o).loc L (g / L.block)) ((X.tr g).take k) := by
  have hk : k ≤ (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1.le
  obtain ⟨-, -, -, -, -, t, -, ⟨hA, -, hm, -⟩ | ⟨-, -, hm, -⟩⟩ :=
    arrive_compute hpre hX hs hI he
  swap
  · cases (Bar.loc_inj hm).1
  obtain rfl : o = stage2 t := Bar.storeFull.inj (Bar.loc_inj hm).1
  have hc : tid g < 128 := refAt_compute hA.1
  rw [block_mod hpre] at hown
  obtain ⟨hsp, hlc, hlo, hhi⟩ := hl
  have hlo' : L.sharedBase + (86912 + 4096 * (t % 2)) ≤ l.addr := hlo
  have hhi' : l.addr < L.sharedBase + (86912 + 4096 * (t % 2 + 1)) := hhi
  have hbase := hpre.sharedBase
  have b2 : t % 2 < 2 := Nat.mod_lt _ (by decide)
  have hwl : warpOff g = 1024 * (tid g / 32) := rfl
  have hll : laneOff g = 16 * (tid g % 32) := rfl
  -- the row write at position `n` of the tile, `d` events before the arrival
  have key : ∀ d n, d + n = 266 → (n = 165 ∨ n = 167) → (accOf P L g t n).Covers l →
      ∃ i pcw aw bs, i < k ∧ X.get (g, i) = some ⟨pcw, .wr aw bs⟩ ∧ aw.Covers l ∧
        arrivals ((Bar.storeFull (stage2 t)).loc L (g / L.block)) ((X.tr g).take i) =
          arrivals ((Bar.storeFull (stage2 t)).loc L (g / L.block)) ((X.tr g).take k) := by
    intro d n hdn hn hcov
    obtain ⟨hdk, sd, hsd, hAd⟩ := back hpre hX hg h0 hin hk hs hA d (by omega)
    rw [show 266 - d = n by omega] at hAd
    obtain ⟨ed, hed⟩ : ∃ ed, X.get (g, k - d) = some ed :=
      ⟨_, List.getElem?_eq_getElem (show k - d < (X.tr g).length by omega)⟩
    have hevd : EvAt P L g (.tile t n) ed := ev_at hpre hX hAd.1 hsd hed
    rw [evAt_body (by omega) (by omega)] at hevd
    have hwr : ∃ bs, ed.kind = .wr (accOf P L g t n) bs := by
      rcases hn with rfl | rfl
      · rw [ite_eq_right (by decide)] at hevd
        rcases hevd with ⟨bs, -, hw⟩ | ⟨bs, hkd, -⟩
        · cases hw
        · exact ⟨bs, hkd⟩
      · rw [ite_eq_right (by decide)] at hevd
        rcases hevd with ⟨bs, -, hw⟩ | ⟨bs, hkd, -⟩
        · cases hw
        · exact ⟨bs, hkd⟩
    obtain ⟨bs, hkd⟩ := hwr
    obtain ⟨pcw, kd⟩ := ed
    simp only at hkd
    subst hkd
    refine ⟨k - d, pcw, _, bs, by omega, hed, hcov, ?_⟩
    rw [cnt_af hAd.2.1 (stage2 t), cnt_af hA.2.1 (stage2 t),
      show ind 267 n = 0 from ite_eq_right (show ¬ 267 ≤ n by omega)]
    rfl
  -- the byte's offset `y` in its buffer
  obtain ⟨y, hy, hy4⟩ : ∃ y, l.addr = P.sharedBase + 86912 + 4096 * (t % 2) + y ∧ y < 4096 :=
    ⟨l.addr - (P.sharedBase + 86912 + 4096 * (t % 2)), by omega, by omega⟩
  have hmod : (l.addr - (P.sharedBase + 86912)) % 4096 = y := by
    rw [hy]
    omega
  unfold outOwner at hown
  rw [hmod] at hown
  have hinv := outOwner_inv hy4
  rw [hown] at hinv
  by_cases hh : y % 1024 < 512
  · refine key 101 165 rfl (.inl rfl)
      (show l.space = Space.shared ∧ l.cta = g / L.block ∧ regVal P g t 1672 + 0 ≤ l.addr ∧
        l.addr < regVal P g t 1672 + 0 + 16 from ⟨hsp, hlc, ?_, ?_⟩)
    · have e1 := rv_1672 (P := P) (g := g) (t := t)
      omega
    · have e1 := rv_1672 (P := P) (g := g) (t := t)
      omega
  · refine key 99 167 rfl (.inr rfl)
      (show l.space = Space.shared ∧ l.cta = g / L.block ∧ regVal P g t 1677 + 0 ≤ l.addr ∧
        l.addr < regVal P g t 1677 + 0 + 16 from ⟨hsp, hlc, ?_, ?_⟩)
    · have e1 := rv_1677 (P := P) (g := g) (t := t)
      omega
    · have e1 := rv_1677 (P := P) (g := g) (t := t)
      omega

end

/-! ### At the exit of the phase -/

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads) {j0 j : Nat} {s0 s1 : D} (h0 : At (code L) X g j0 s0)
  (hin : In P L X g j0 s0) (hs1 : At (code L) X g j s1) (hout : Out P L X g j0 j s1)
include hout

/-- **The counts at the exit of the phase** (the state at instruction 3113, the first
`bar.sync 0` of the epilogue, before its event): six `bar.sync 0`, one named barrier per tile,
the poll of the state mbarrier, and for each stage one successful poll and one arrival per tile
that uses the stage. -/
theorem exit_counts :
    ((X.tr g).take j).countP (Execution.isBarId 0) = 6 ∧
      ((X.tr g).take j).countP (Execution.isBarId 8) = tilesOf P g ∧
      okPolls (Bar.state.loc L (g / L.block)) ((X.tr g).take j) = 1 ∧
      (∀ o : Fin 2, okPolls ((Bar.storeEmpty o).loc L (g / L.block)) ((X.tr g).take j) =
          uses 2 (tilesOf P g) o.val ∧
        arrivals ((Bar.storeFull o).loc L (g / L.block)) ((X.tr g).take j) =
          uses 2 (tilesOf P g) o.val) ∧
      ∀ st : Fin 3, okPolls ((Bar.loadFull st).loc L (g / L.block)) ((X.tr g).take j) =
          uses 3 (tilesOf P g) st.val ∧
        arrivals ((Bar.loadEmpty st).loc L (g / L.block)) ((X.tr g).take j) =
          uses 3 (tilesOf P g) st.val := by
  have hl : ledOf L (g / L.block) ((X.tr g).take j) = ledExit P g := hout.2.1
  refine ⟨congrArg Led.bar0 hl, congrArg Led.bar8 hl, congrArg Led.pollS hl, fun o => ?_,
    fun st => ?_⟩
  · fin_cases o
    · exact ⟨congrArg Led.pe0 hl, congrArg Led.af0 hl⟩
    · exact ⟨congrArg Led.pe1 hl, congrArg Led.af1 hl⟩
  · fin_cases st
    · exact ⟨congrArg Led.pf0 hl, congrArg Led.ae0 hl⟩
    · exact ⟨congrArg Led.pf1 hl, congrArg Led.ae1 hl⟩
    · exact ⟨congrArg Led.pf2 hl, congrArg Led.ae2 hl⟩

include hpre in
/-- `LifeFacts.full_polled` and `UnionFacts.polled`, from the exit of the phase on: a compute
thread that has left the tile loop has polled the "full" mbarrier of each input stage
successfully once per tile that uses the stage. -/
theorem exit_polled (st : Fin 3) {i : Nat} (hji : j ≤ i) :
    uses 3 (ctaTiles P (g / L.block)) st ≤
      okPolls ((Bar.loadFull st).loc L (g / L.block)) ((X.tr g).take i) := by
  rw [ctaTiles_eq hpre, ← ((exit_counts hout).2.2.2.2 st).1]
  exact (List.take_sublist_take_left hji).countP_le

/-- `LifeFacts.state_polled`, from the exit of the phase on. -/
theorem exit_state_polled {i : Nat} (hji : j ≤ i) :
    1 ≤ okPolls (Bar.state.loc L (g / L.block)) ((X.tr g).take i) := by
  rw [← (exit_counts hout).2.2.1]
  exact (List.take_sublist_take_left hji).countP_le

include hpre hX hg h0 hin hs1

/-- **The exit is the first**: every followed state between the entry and the exit state
satisfies the invariant (the event of an exit state, a `bar.sync 0`, counts, so the thread
cannot have been at an exit state before). -/
theorem exit_first (hj : j ≤ (X.tr g).length) {i : Nat} (hi0 : j0 ≤ i) (hij : i < j) :
    ∃ si, At (code L) X g i si ∧ Inv P L X g j0 i si := by
  obtain ⟨si, hsi⟩ := followed_of_le hs1 hij.le
  refine ⟨si, hsi, ?_⟩
  rcases inv_at hpre hX hg h0 hin hi0 (by omega) hsi with h | ⟨j', s', -, h2, hs', hout'⟩
  · exact h
  · obtain ⟨e', he'⟩ : ∃ e', X.get (g, j') = some e' :=
      ⟨_, List.getElem?_eq_getElem (show j' < (X.tr g).length by omega)⟩
    have hpc : s'.site.pc ∈ bar0Pcs := by
      rw [hout'.1.site]
      decide
    have hev := bar0_event (sounds hpre) hX he' hs' hpc
    have hc : e'.counts = true := by
      rw [hev]
      rfl
    have h1 := counted_succ hout'.2.2.1 he'
    rw [hout'.2.2.2, hc] at h1
    simp only [ite_true] at h1
    have h3 := counted_mono X g j0 (show j' + 1 ≤ j by omega)
    rw [h1, hout.2.2.2] at h3
    omega

/-- **The barrier events at the exit of the phase**: six `bar.sync 0` and one named barrier per
tile, when there are five barrier events before the entry (`hB`). This is the hypothesis `hT`
of the Epilogue's `bar_sched`. -/
theorem exit_bars (hj : j ≤ (X.tr g).length)
    (hB : ((X.tr g).take j0).countP Execution.isBar = 5) :
    ((X.tr g).take j).countP Execution.isBar = 6 + ctaTiles P (g / L.block) := by
  have h1 : ((X.tr g).take j).countP otherBar = ((X.tr g).take j0).countP otherBar :=
    countP_take_eq otherBar hout.2.2.1 fun i ev hi0 hik hev => by
      obtain ⟨si, hsi, pos, hR, -⟩ := exit_first hpre hX hg h0 hin hs1 hout hj hi0 hik
      exact (ev_at hpre hX hR hsi hev).otherBar
  have h2 := countP_isBar ((X.tr g).take j0)
  have h3 := countP_isBar ((X.tr g).take j)
  have h4 : ((X.tr g).take j0).countP (Execution.isBarId 0) = 5 := congrArg Led.bar0 hin.2
  obtain ⟨h5, h6, -⟩ := exit_counts hout
  rw [ctaTiles_eq hpre]
  omega

end

/-! ### In the form of the assembly's structures `ComputeOwes`

One theorem per field of the three structures `ComputeOwes` of the assembly, with the field's
hypotheses in the field's order (after `hpre` and `hX`), so that `field := owes_field hpre hX`
builds the structure. Group A (`Ref/Assembly/FactsABase.lean`): `owes_bar8`, `owes_mbar`.
Group B (`FactsB.lean`): `owes_kinds`, `owes_poll`, `owes_arrive`, `owes_in_fence`,
`owes_out_fence`, `owes_acc_phase`, `owes_acc_owner`. The buffers (`BuffersLib.lean`):
`owes_thread`, `owes_out_cover`, `owes_matrix_len` (which takes the entry, see `matrix_len`),
`owes_wr_shared`. The value ends (`ValuesEndsRef.lean`): `owes_ends_wr_shared`,
`owes_ends_acc_row`. -/

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
include hpre hX

/-- Group A, `bar8`: a barrier event at the instruction of the named barrier (2913) is
`bar.sync 8, 128`, and the thread has made fewer named barriers before it than its sequence has
tiles. -/
theorem owes_bar8 {g j0 k pc id : Nat} {cnt : Option Nat} {mode : BarMode} {s : D}
    (hs : At (code L) X g k s) (hI : Inv P L X g j0 k s)
    (he : X.get (g, k) = some ⟨pc, .bar id cnt mode⟩) (hpc : s.site.pc = 2913) :
    id = 8 ∧ cnt = some 128 ∧ mode = .sync ∧
      ((X.tr g).take k).countP (Execution.isBarId 8) < tilesOf P g := by
  obtain ⟨-, hm, ⟨hA, -⟩ | ⟨t, -, h1, h2, -, -, h8, ht⟩⟩ := bar_compute hpre hX hs hI he
  · have hsite : s.site = .bar 5 := hA.1.site
    rw [hsite] at hpc
    exact absurd hpc (by decide)
  · exact ⟨h1, h2, hm, by rw [h8]; exact ht⟩

/-- Group A, `mbar`: an event that names an mbarrier names one of the eleven mbarriers of the
thread's block. -/
theorem owes_mbar {g j0 k : Nat} {e : Event} {m : Loc} {s : D} (hs : At (code L) X g k s)
    (hI : Inv P L X g j0 k s) (he : X.get (g, k) = some e) (hm : Frame.MbarOf e m) :
    ∃ b : Bar, m = b.loc L (g / L.block) :=
  mbar_own hpre hX hs hI he hm

/-- Group B, `kinds`: the kinds of the events of the phase. -/
theorem owes_kinds {g j0 k : Nat} {s0 s : D} {e : Event} (hg : g < L.threads)
    (hc : tid g < 128) (h0 : At (code L) X g j0 s0) (hin : In P L X g j0 s0)
    (hs : At (code L) X g k s) (hI : Inv P L X g j0 k s) (he : X.get (g, k) = some e) :
    (∃ id cnt m, e.kind = .bar id cnt m) ∨ (∃ l q ok acq sc, e.kind = .wait l q ok acq sc) ∨
      (∃ l tx n rel sc, e.kind = .arrive l tx n rel sc) ∨
      (∃ px sc, e.kind = .fenceProxy px sc) ∨ (∃ a bs, e.kind = .rd a bs) ∨
      (∃ a bs, e.kind = .wr a bs) ∨ (∃ op own recv, e.kind = .matrix op own recv) ∨
      ∃ f, e.kind = .ub f :=
  kinds_compute hpre hX hs hI he

/-- Group B, `poll`: a poll of the phase acquires; it is a poll of the "full" mbarrier of a
load stage of the thread's block, with the parity of the thread's earlier successful polls of
it, or of the "empty" mbarrier of a store stage, with that parity plus one. -/
theorem owes_poll {g j0 k pc p : Nat} {m : Loc} {ok acq : Bool} {sc : MbarScope} {s0 s : D}
    (hg : g < L.threads) (hc : tid g < 128) (h0 : At (code L) X g j0 s0)
    (hin : In P L X g j0 s0) (hs : At (code L) X g k s) (hI : Inv P L X g j0 k s)
    (he : X.get (g, k) = some ⟨pc, .wait m p ok acq sc⟩) :
    acq = true ∧
      ((∃ st : Fin 3, m = (Bar.loadFull st).loc L (g / L.block) ∧
          p % 2 = okPolls m ((X.tr g).take k) % 2) ∨
        (∃ o : Fin 2, m = (Bar.storeEmpty o).loc L (g / L.block) ∧
          p % 2 = (okPolls m ((X.tr g).take k) + 1) % 2)) := by
  obtain ⟨hacq, -, -, t, -, ⟨-, -, hm, hq, hp⟩ | ⟨-, -, hm, hq, hp⟩⟩ :=
    wait_compute hpre hX hs hI he
  · exact ⟨hacq, .inr ⟨stage2 t, hm, by rw [hp, hq]; omega⟩⟩
  · exact ⟨hacq, .inl ⟨stage3 t, hm, by rw [hp, hq]; omega⟩⟩

/-- Group B, `arrive`: an arrival of the phase is one release arrival without transaction
bytes, on the "empty" mbarrier of a load stage of the thread's block after more successful
polls of the stage's "full" mbarrier than earlier arrivals, or on the "full" mbarrier of a
store stage after more successful polls of the stage's "empty" mbarrier than earlier
arrivals. -/
theorem owes_arrive {g j0 k pc tx cnt : Nat} {m : Loc} {rel : Bool} {sc : MbarScope}
    {s0 s : D} (hg : g < L.threads) (hc : tid g < 128) (h0 : At (code L) X g j0 s0)
    (hin : In P L X g j0 s0) (hs : At (code L) X g k s) (hI : Inv P L X g j0 k s)
    (he : X.get (g, k) = some ⟨pc, .arrive m tx cnt rel sc⟩) :
    tx = 0 ∧ cnt = 1 ∧ rel = true ∧
      ((∃ st : Fin 3, m = (Bar.loadEmpty st).loc L (g / L.block) ∧
          arrivals m ((X.tr g).take k) + 1 ≤
            okPolls ((Bar.loadFull st).loc L (g / L.block)) ((X.tr g).take k)) ∨
        (∃ o : Fin 2, m = (Bar.storeFull o).loc L (g / L.block) ∧
          arrivals m ((X.tr g).take k) + 1 ≤
            okPolls ((Bar.storeEmpty o).loc L (g / L.block)) ((X.tr g).take k))) := by
  obtain ⟨h1, h2, h3, -, -, t, -, ⟨-, -, hm, ha, hp⟩ | ⟨-, -, hm, ha, hp⟩⟩ :=
    arrive_compute hpre hX hs hI he
  · exact ⟨h1, h2, h3, .inr ⟨stage2 t, hm, by rw [ha, hp]⟩⟩
  · exact ⟨h1, h2, h3, .inl ⟨stage3 t, hm, by rw [ha, hp]⟩⟩

/-- Group B, `in_fence`: between an earlier memory access of the thread and an arrival of the
phase on the "empty" mbarrier of a load stage, the thread executes the proxy fence (two events
before the arrival). -/
theorem owes_in_fence {g j0 i e pce tx cnt : Nat} {a : Acc} {w : Bool} {l : Loc} {st : Fin 3}
    {rel : Bool} {sc : MbarScope} {s0 se : D} (hg : g < L.threads) (hc : tid g < 128)
    (h0 : At (code L) X g j0 s0) (hin : In P L X g j0 s0) (hs : At (code L) X g e se)
    (hI : Inv P L X g j0 e se)
    (he : X.get (g, e) =
      some ⟨pce, .arrive ((Bar.loadEmpty st).loc L (g / L.block)) tx cnt rel sc⟩)
    (hacc : X.Access (g, i) a w) (hcov : a.Covers l)
    (hl : InInput L (g / L.block) st.val l) (hie : i < e) :
    ∃ f pcf, i < f ∧ f < e ∧
      X.get (g, f) = some ⟨pcf, .fenceProxy (.async (some (.shared .cta))) none⟩ :=
  in_fence hpre hX hg h0 hin hs hI hacc hie he

/-- Group B, `out_fence`: between an earlier memory access of the thread and an arrival of the
phase on the "full" mbarrier of a store stage, the thread executes the proxy fence (the event
before the arrival). -/
theorem owes_out_fence {g j0 i e pce tx cnt : Nat} {a : Acc} {w : Bool} {l : Loc} {o : Fin 2}
    {rel : Bool} {sc : MbarScope} {s0 se : D} (hg : g < L.threads) (hc : tid g < 128)
    (h0 : At (code L) X g j0 s0) (hin : In P L X g j0 s0) (hs : At (code L) X g e se)
    (hI : Inv P L X g j0 e se)
    (he : X.get (g, e) =
      some ⟨pce, .arrive ((Bar.storeFull o).loc L (g / L.block)) tx cnt rel sc⟩)
    (hacc : X.Access (g, i) a w) (hcov : a.Covers l)
    (hl : InOutput L (g / L.block) o.val l) (hie : i < e) :
    ∃ f pcf, i < f ∧ f < e ∧
      X.get (g, f) = some ⟨pcf, .fenceProxy (.async (some (.shared .cta))) none⟩ :=
  out_fence hpre hX hg h0 hin hs hI hacc hie he

/-- Group B, `acc_phase`: a memory access of the phase that covers a byte of the bfloat16 state
copy of a block `c` is in the thread's own block, with six `bar.sync 0` before it. -/
theorem owes_acc_phase {g j0 k c : Nat} {a : Acc} {w : Bool} {l : Loc} {s0 s : D}
    (hg : g < L.threads) (hc : tid g < 128) (h0 : At (code L) X g j0 s0)
    (hin : In P L X g j0 s0) (hs : At (code L) X g k s) (hI : Inv P L X g j0 k s)
    (hacc : X.Access (g, k) a w) (hcov : a.Covers l) (hl : InStateAcc L c l) :
    c = g / L.block ∧ bar0Before X (g, k) = 6 :=
  let ⟨h1, h2, _⟩ := stateAcc_own hpre hX hs hI hacc hcov hl
  ⟨h1, h2⟩

/-- Group B, `acc_owner`: two memory accesses of the phase (of compute threads `g` and `h`,
each at a state of its own invariant) that cover one byte of the bfloat16 state copy are one
thread's. -/
theorem owes_acc_owner {g h j0 j0' k k' c : Nat} {a b : Acc} {w w' : Bool} {l : Loc}
    {s0 s s0' s' : D} (hg : g < L.threads) (hc : tid g < 128) (h0 : At (code L) X g j0 s0)
    (hin : In P L X g j0 s0) (hs : At (code L) X g k s) (hI : Inv P L X g j0 k s)
    (hh : h < L.threads) (hc' : tid h < 128) (h0' : At (code L) X h j0' s0')
    (hin' : In P L X h j0' s0') (hs' : At (code L) X h k' s') (hI' : Inv P L X h j0' k' s')
    (ha : X.Access (g, k) a w) (hb : X.Access (h, k') b w') (hw : w = true ∨ w' = true)
    (hca : a.Covers l) (hcb : b.Covers l) (hl : InStateAcc L c l) : g = h :=
  stateAcc_owner hpre hX hs hI hs' hI' ha hb hca hcb hl

/-- The buffers, `thread`: `UnionFacts.thread` without the state poll, for owner functions `O`
with `O.out = outOwner P`. -/
theorem owes_thread {g j0 k c : Nat} {s0 s : D} {a : Acc} {w : Bool} {l : Loc} (O : Owners)
    (hO : O.out = outOwner P) (hg : g < L.threads) (h0 : At (code L) X g j0 s0)
    (hin : In P L X g j0 s0) (hs : At (code L) X g k s) (hI : Inv P L X g j0 k s)
    (hacc : X.Access (g, k) a w) (hcov : a.Covers l) (hl : InUnion L c l) :
    g / L.block = c ∧ ThreadClass L X O c g k w l :=
  let ⟨h1, _, h2⟩ := union_thread hpre hX hs hI hO hacc hcov hl
  ⟨h1, h2⟩

/-- The buffers, `out_cover`: `StoreCover.out_cover` for an arrival of the phase. -/
theorem owes_out_cover {g j0 k pc tx cnt : Nat} {s0 s : D} {rel : Bool} {sc : MbarScope}
    (o : Fin 2) {l : Loc} (hg : g < L.threads) (h0 : At (code L) X g j0 s0)
    (hin : In P L X g j0 s0) (hs : At (code L) X g k s) (hI : Inv P L X g j0 k s)
    (he : X.get (g, k) =
      some ⟨pc, .arrive ((Bar.storeFull o).loc L (g / L.block)) tx cnt rel sc⟩)
    (hl : InOutput L (g / L.block) o.val l) (hown : outOwner P l = g % L.block) :
    ∃ i pcw aw bs, i < k ∧ X.get (g, i) = some ⟨pcw, .wr aw bs⟩ ∧ aw.Covers l ∧
      arrivals ((Bar.storeFull o).loc L (g / L.block)) ((X.tr g).take i) =
        arrivals ((Bar.storeFull o).loc L (g / L.block)) ((X.tr g).take k) :=
  out_cover hpre hX hg h0 hin hs hI o he hl hown

/-- The buffers, `matrix_len`: `StoreCover.matrix_len` for a write event of the phase. It takes
the entry (`h0`, `hin`), which the field of `BuffersLib.lean` did not have when this was
written: see `matrix_len`. -/
theorem owes_matrix_len {g j0 k pc : Nat} {s0 s : D} {a : Acc} {bs : List Byte}
    (hg : g < L.threads) (h0 : At (code L) X g j0 s0) (hin : In P L X g j0 s0)
    (hs : At (code L) X g k s) (hI : Inv P L X g j0 k s)
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) : bs.length = a.size :=
  matrix_len hpre hX hg h0 hin hs hI he

/-- The buffers, `wr_shared`: a write event of the phase is in shared memory. -/
theorem owes_wr_shared {g j0 k pc : Nat} {s : D} {a : Acc} {bs : List Byte}
    (hg : g < L.threads) (hs : At (code L) X g k s) (hI : Inv P L X g j0 k s)
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) : a.loc.space = .shared :=
  wr_shared hpre hX hs hI he

/-- The value ends (`Ref/Assembly/ValuesEndsRef.lean`), `wr_shared`: a write event of the phase
is to shared memory. -/
theorem owes_ends_wr_shared : ∀ g j0 k s pc a bs, g < L.threads →
    Frame.stateAt (code L) X g k = some (some s) → Inv P L X g j0 k s →
    X.get (g, k) = some ⟨pc, .wr a bs⟩ → a.loc.space = .shared :=
  fun g j0 k s pc a bs _ hs hI he => wr_shared hpre hX hs hI he

/-- The value ends, `acc_row`: an access of the phase that covers a byte of the bfloat16 state
copy is an access of a whole row. -/
theorem owes_ends_acc_row : ∀ g j0 k s a w l c, g < L.threads →
    Frame.stateAt (code L) X g k = some (some s) → Inv P L X g j0 k s →
    X.Access (g, k) a w → a.Covers l → InStateAcc L c l →
    a.size = 16 ∧ ∃ r, a.loc.addr = L.sharedBase + 16 * r :=
  fun g j0 k s a w l c _ hs hI hacc hcov hl => stateAcc_row hpre hX hs hI hacc hcov hl

end

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Compute.Proto
