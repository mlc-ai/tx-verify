-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Safety.Handoff
public import Lemmas.Protocol.BarTable

@[expose] public section

/-! # Names for the synchronization objects of one thread block of the FlashKDA kernel

The protocol layer talks about one thread block (a "CTA": 192 threads, six warps of 32) at a
time. This file only gives names; it proves nothing about the program.

* **Threads.** `thr L c tid` is thread `tid` of CTA `c`. The 128 *compute threads* are
  `tid < 128` (`computeThread`). Under the assumption `electZero` (a full-mask election elects
  lane 0) the three threads with a private job are fixed: the *init leader* `tid = 0` (it
  initializes the ten pipeline barriers), the *load leader* `tid = 128` (it initializes the state
  barrier and issues every asynchronous load of the copy engine, "TMA") and the *store leader*
  `tid = 160` (it issues every asynchronous store).
* **Memory barriers** ("mbarriers", `Bar`): eleven 8-byte objects at fixed offsets of the CTA's
  shared memory. `loadFull s` / `loadEmpty s` are the two barriers of stage `s < 3` of the load
  pipeline, `storeFull o` / `storeEmpty o` those of stage `o < 2` of the store pipeline, `state`
  guards the one-shot load of the initial state. `Bar.count` is the arrival count the barrier is
  initialized with, `Bar.gen` the number of `bar.sync 0` instructions its initializing thread
  (`Bar.owner`) executed before the initialization, `Bar.delta` the parity offset of its polls
  (1 when the first poll must pass on the fresh barrier).
* **Regions** of the CTA's shared memory: `InStateAcc` (the bf16 state, offsets `[0, 32768)`),
  `InUnion` (offsets `[32768, 98304)`: the FP32 state buffer, which shares its bytes with the
  three input buffers `InInput s` and the two output buffers `InOutput o`).
* **Tiles.** A CTA processes `T` tiles of 16 tokens (`T = 0` for an empty sequence). Tile `t`
  uses load stage `t % 3` and store stage `t % 2`; `uses n T s` is the number of tiles `t < T`
  with `t % n = s`, i.e. how often stage `s` of an `n`-stage pipeline is used.
* **Counts along a trace.** `bar0Before X e` is the number of `bar.sync 0` events of the thread
  of `e` before `e`; `bar0UpTo X e` counts `e` itself too. -/

namespace PTX.Kernels.FlashKdaFwd.Protocol
open PTX PTX.Flow

/-! ### Threads -/

/-- Thread `tid` of CTA `c`. -/
def thr (L : Launch) (c tid : Nat) : Nat := c * L.block + tid

/-- Compute thread `a` of CTA `c` (warps 0 to 3). -/
def computeThread (L : Launch) (c : Nat) (a : Fin 128) : Nat := thr L c a.val

/-- The thread of CTA `c` that initializes the ten pipeline barriers (lane 0 of warp 0). -/
def initLeader (L : Launch) (c : Nat) : Nat := thr L c 0

/-- The thread of CTA `c` that issues the asynchronous loads (lane 0 of warp 4). -/
def loadLeader (L : Launch) (c : Nat) : Nat := thr L c 128

/-- The thread of CTA `c` that issues the asynchronous stores (lane 0 of warp 5). -/
def storeLeader (L : Launch) (c : Nat) : Nat := thr L c 160

theorem thr_lt {L : Launch} {c tid : Nat} (hb : L.block = 192) (hc : c < L.grid)
    (ht : tid < 192) : thr L c tid < L.threads := by
  unfold thr Launch.threads
  rw [hb]
  nlinarith

theorem thr_div {L : Launch} {c tid : Nat} (hb : L.block = 192) (ht : tid < 192) :
    thr L c tid / L.block = c := by
  unfold thr
  rw [hb]
  omega

theorem thr_mod {L : Launch} {c tid : Nat} (hb : L.block = 192) (ht : tid < 192) :
    thr L c tid % L.block = tid := by
  unfold thr
  rw [hb]
  omega

/-- A launched thread is thread `g % 192` of CTA `g / 192`. -/
theorem thr_eq {L : Launch} (hb : L.block = 192) (g : Nat) :
    thr L (g / L.block) (g % L.block) = g := by
  unfold thr
  rw [hb]
  omega

theorem cta_lt {L : Launch} {g : Nat} (hb : L.block = 192) (hg : g < L.threads) :
    g / L.block < L.grid := by
  unfold Launch.threads at hg
  rw [hb] at hg ⊢
  exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hg)

/-- Two threads of CTA `c` are in one CTA. -/
theorem sameCta_thr {L : Launch} {c s t : Nat} (hb : L.block = 192) (hc : c < L.grid)
    (hs : s < 192) (ht : t < 192) : SameCta L (thr L c s) (thr L c t) :=
  ⟨thr_lt hb hc hs, thr_lt hb hc ht, by rw [thr_div hb hs, thr_div hb ht]⟩

theorem computeThread_inj (L : Launch) (c : Nat) : Function.Injective (computeThread L c) :=
  fun a b h => Fin.ext (by unfold computeThread thr at h; omega)

/-- A launched thread with `tid < 128` is a compute thread of its CTA. -/
theorem computeThread_of {L : Launch} {g c : Nat} (hb : L.block = 192) (hw : g % L.block < 128)
    (hc : c = g / L.block) : ∃ a, g = computeThread L c a :=
  ⟨⟨g % L.block, hw⟩, by subst hc; exact (thr_eq hb g).symm⟩

theorem computeThread_lt {L : Launch} {c : Nat} (hb : L.block = 192) (hc : c < L.grid)
    (a : Fin 128) : computeThread L c a < L.threads :=
  thr_lt hb hc (by have := a.isLt; omega)

theorem computeThread_div {L : Launch} {c : Nat} (hb : L.block = 192) (a : Fin 128) :
    computeThread L c a / L.block = c :=
  thr_div hb (by have := a.isLt; omega)

/-! ### The eleven mbarriers of a CTA -/

/-- The mbarriers of one CTA. -/
inductive Bar
  /-- Load pipeline, stage `s`: completed by the load leader's expect-tx arrival and the 70
  loads of a tile; polled by the 128 compute threads. -/
  | loadFull (s : Fin 3)
  /-- Load pipeline, stage `s`: completed by one arrival of each compute thread; polled by the
  load leader. -/
  | loadEmpty (s : Fin 3)
  /-- Store pipeline, stage `o`: completed by one arrival of each compute thread; polled by the
  store leader. -/
  | storeFull (o : Fin 2)
  /-- Store pipeline, stage `o`: completed by one arrival of the store leader; polled by the
  compute threads. -/
  | storeEmpty (o : Fin 2)
  /-- The barrier of the one-shot load of the initial state; polled by every thread. -/
  | state
  deriving DecidableEq

namespace Bar

/-- Offset of the barrier in the CTA's shared memory. -/
def off : Bar → Nat
  | loadFull s => 98304 + 8 * s.val
  | loadEmpty s => 98328 + 8 * s.val
  | storeFull o => 98352 + 8 * o.val
  | storeEmpty o => 98368 + 8 * o.val
  | state => 98384

/-- The arrival count of the barrier's initialization. -/
def count : Bar → Nat
  | loadFull _ => 1
  | loadEmpty _ => 128
  | storeFull _ => 128
  | storeEmpty _ => 1
  | state => 1

/-- How many `bar.sync 0` the initializing thread executed before it initializes the barrier:
the barrier is published to the other threads by the `bar.sync 0` with this ordinal. -/
def gen : Bar → Nat
  | loadFull _ | loadEmpty _ => 0
  | storeFull _ | storeEmpty _ => 1
  | state => 2

/-- Parity offset of the barrier's polls: a successful poll passes the parity of its thread's
earlier successful polls of the barrier plus this offset (CUTLASS starts a producer at phase 1,
so the first poll of an "empty" barrier passes on the fresh object). -/
def delta : Bar → Nat
  | loadEmpty _ | storeEmpty _ => 1
  | _ => 0

/-- The thread of CTA `c` that initializes the barrier. -/
def owner (L : Launch) (c : Nat) : Bar → Nat
  | state => loadLeader L c
  | _ => initLeader L c

/-- The barrier's location in CTA `c`. -/
def loc (L : Launch) (c : Nat) (b : Bar) : Loc := ⟨.shared, c, L.sharedBase + b.off⟩

theorem off_inj : ∀ {b b' : Bar}, b.off = b'.off → b = b' := by
  intro b b' h
  cases b <;> cases b' <;> simp only [off] at h <;>
    first
    | rfl
    | (congr 1; exact Fin.ext (by omega))
    | (exfalso; rename_i x y; have := x.isLt; have := y.isLt; omega)
    | (exfalso; rename_i x; have := x.isLt; omega)

theorem loc_inj {L : Launch} {c c' : Nat} {b b' : Bar} (h : b.loc L c = b'.loc L c') :
    b = b' ∧ c = c' := by
  simp only [loc, Loc.mk.injEq, true_and] at h
  exact ⟨off_inj (by omega), h.1⟩

theorem count_valid (b : Bar) : MBarrier.validCount b.count := by
  cases b <;> simp [count, MBarrier.validCount, MBarrier.limit]

theorem delta_le (b : Bar) : b.delta ≤ 1 := by cases b <;> simp [delta]

theorem owner_lt {L : Launch} {c : Nat} (hb : L.block = 192) (hc : c < L.grid) (b : Bar) :
    b.owner L c < L.threads := by
  cases b <;> exact thr_lt hb hc (by decide)

theorem owner_div {L : Launch} {c : Nat} (hb : L.block = 192) (b : Bar) :
    b.owner L c / L.block = c := by
  cases b <;> exact thr_div hb (by decide)

end Bar

/-! ### Regions of the CTA's shared memory -/

/-- Bytes `[lo, hi)` of the shared memory of CTA `c`, as offsets from the shared base. -/
def InShared (L : Launch) (c lo hi : Nat) (l : Loc) : Prop :=
  l.space = .shared ∧ l.cta = c ∧ L.sharedBase + lo ≤ l.addr ∧ l.addr < L.sharedBase + hi

/-- The bf16 state `state_acc`. -/
def InStateAcc (L : Launch) (c : Nat) : Loc → Prop := InShared L c 0 32768

/-- The union region: the FP32 state buffer, aliased by the input and output buffers. -/
def InUnion (L : Launch) (c : Nat) : Loc → Prop := InShared L c 32768 98304

/-- Input buffer of load stage `s`. -/
def InInput (L : Launch) (c s : Nat) : Loc → Prop :=
  InShared L c (32768 + 18048 * s) (32768 + 18048 * (s + 1))

/-- Output staging buffer of store stage `o`. -/
def InOutput (L : Launch) (c o : Nat) : Loc → Prop :=
  InShared L c (86912 + 4096 * o) (86912 + 4096 * (o + 1))

/-- The eleven mbarrier objects. -/
def InBars (L : Launch) (c : Nat) : Loc → Prop := InShared L c 98304 98392

theorem InInput.union {L : Launch} {c s : Nat} {l : Loc} (hs : s < 3) (h : InInput L c s l) :
    InUnion L c l := by
  simp only [InInput, InUnion, InShared] at h ⊢
  refine ⟨h.1, h.2.1, ?_, ?_⟩ <;> omega

theorem InOutput.union {L : Launch} {c o : Nat} {l : Loc} (ho : o < 2) (h : InOutput L c o l) :
    InUnion L c l := by
  simp only [InOutput, InUnion, InShared] at h ⊢
  refine ⟨h.1, h.2.1, ?_, ?_⟩ <;> omega

/-- An input buffer and an output buffer share no byte. -/
theorem input_output_apart {L : Launch} {c s o : Nat} {l : Loc} (hs : s < 3)
    (hi : InInput L c s l) (ho : InOutput L c o l) : False := by
  simp only [InInput, InOutput, InShared] at hi ho
  omega

/-! ### Tiles and uses -/

/-- The number of tiles `t < T` with `t % n = s`: how often stage `s` of an `n`-stage pipeline
is used by a CTA of `T` tiles. -/
def uses (n T s : Nat) : Nat := (T + n - 1 - s) / n

theorem uses_zero (n s : Nat) (hs : s < n) : uses n 0 s = 0 := by
  unfold uses
  exact Nat.div_eq_of_lt (by omega)

/-- Tile `t` is use `t / n` of stage `t % n`, and it is one of the stage's uses. -/
theorem div_lt_uses {n T t : Nat} (hn : 0 < n) (ht : t < T) : t / n < uses n T (t % n) := by
  unfold uses
  rw [Nat.lt_div_iff_mul_lt hn]
  have h1 := Nat.div_add_mod t n
  have h2 := Nat.mod_lt t hn
  have h3 : n * (t / n) = t / n * n := Nat.mul_comm _ _
  omega

/-! ### Counting `bar.sync 0` along a trace -/

/-- The `bar.sync 0` events of the thread of `e` before `e`. -/
def bar0Before (X : Execution) (e : EvId) : Nat :=
  ((X.tr e.1).take e.2).countP (Execution.isBarId 0)

/-- The `bar.sync 0` events of the thread of `e` up to and including `e`. -/
def bar0UpTo (X : Execution) (e : EvId) : Nat :=
  ((X.tr e.1).take (e.2 + 1)).countP (Execution.isBarId 0)

/-- The positions of the nine `bar.sync 0` instructions, in program order. -/
def bar0Pcs : List Nat := [85, 110, 379, 620, 621, 1402, 3113, 3775, 3834]

end PTX.Kernels.FlashKdaFwd.Protocol
