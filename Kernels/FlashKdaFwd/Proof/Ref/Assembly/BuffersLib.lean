-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.Tracked
public import Kernels.FlashKdaFwd.Proof.Ref.Startup.Contract
public import Kernels.FlashKdaFwd.Proof.Ref.Conversion.Exports
public import Kernels.FlashKdaFwd.Proof.Ref.CarryLoad.Exports
public import Kernels.FlashKdaFwd.Proof.Ref.Producer.Direct
public import Kernels.FlashKdaFwd.Proof.Ref.Compute.Reach
public import Kernels.FlashKdaFwd.Proof.Ref.Store.Exports
public import Kernels.FlashKdaFwd.Proof.Ref.Epilogue.Contract
public import Kernels.FlashKdaFwd.Proof.Protocol.StoreCover
public import Kernels.FlashKdaFwd.Proof.Protocol.ResultGlue

@[expose] public section

/-!
# The buffer region and the stores: owner functions and the tools of the assembly

`Buffers.lean` proves three contracts of the protocol layer for every consistent execution, by a
case split over the phase of the thread that makes an event (`Stage.lean`): the classification
of the accesses of the buffer region (`Protocol.UnionFacts`), the coverage of the source bytes of
the tensor stores (`Protocol.StoreCover`) and the shapes of the events that write global memory
(`Protocol.StoresIssued`). This file has what the three proofs share.

**Words.** A *block* is a thread block (a "CTA") of 192 threads; `tid g` is the index of thread
`g` in its block, `g / L.block` the block. A *compute thread* has `tid g < 128`; the *load
warp* is `warp g = 4`, the *store warp* `warp g = 5`; the *store leader* is thread 160 of its
block. The *buffer region* (the "union region" of the protocol layer, `InUnion L c`) is the
bytes at offsets 32768 to 98304 of a block's shared-memory window: the FP32 state buffer, whose
bytes are also the three input buffers and the two output buffers of the tile loop. A *followed
state* of thread `g` at position `k` is the state of the thread's machine before the thread's
`k`-th event (`At (code L) X g k s`). A *ledger* is a phase's count of the thread's earlier
events by class. An *mbarrier* is one of the eleven 8-byte synchronization objects of a block
(`Protocol.Bar`); a *poll* is an `mbarrier.try_wait`. *Undefined behaviour* is an event of kind
`.ub`.

## The owner functions

`owners P L : Protocol.Owners` names, for a byte, which of several concurrent writers writes it:

* `block l` (`Startup.stateBlock`): the index of the 4096-byte block of the FP32 state buffer
  that holds `l`: the one of the 16 tensor loads of the initial state that writes it;
* `piece l` (`Producer.pieceOf` of the offset of `l` in its input buffer): the position, among
  the 70 tensor loads of a tile, of the load that writes it;
* `out l` (`outOwner`): the compute thread that writes it in an output buffer: thread
  `32 * (x / 1024) + x % 512 / 16` for the byte at offset `x` of the buffer;
* `final l` (`Epilogue.finalOwner`): the compute thread that writes it in the final state.

## The share of the Compute phase

`Buffers.ComputeOwes P L X` states the four facts about the events of a compute thread in the
tile loop that the three contracts need (the classes `input` and `output` of an access, the
coverage of the output buffer at the arrival, the length and the frame of a row write). The
proofs of the contract fields take it as a hypothesis; `BuffersCompute.lean` proves it from the
Compute phase's invariant, so no hypothesis remains in `Buffers.lean`.

Everything here but `owners` is in the namespace `Assembly.Buffers`.

## The tools

* The history of a phase's entry (`left_startup`, …): a thread that has left the startup
  phase has polled the state mbarrier of its block (`polled_of_left`).
* `bars_*`: the number of `bar.sync 0` before a state of each phase (at most 3 in the startup,
  4 in the conversion loop, 5 at the carry loads, 6 in the tile loops).
* `fence_entry`, `event_entry`, `entry_bar_fence`: the sixth `bar.sync 0` (instruction 1402,
  the entry of the three tile loops) directly follows the proxy fence of instruction 1401.
* `kind_*`: the kinds of event of each phase, as a Boolean function of the kind (`convKind`,
  `carryKind`, `computeKind`, `prodKind`, `storeKind`, `epiKind`; the startup's is
  `Startup.phaseKind`), so that "this phase fires no such event" is `Bool.false_ne_true`.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Protocol (Owners Bar bar0Before bar0Pcs InUnion InInput InOutput
  InShared ThreadClass LoadClass StoreClass UnionFacts StoreCover StoresIssued storeLeader
  computeThread ctaTiles uses blockOf stageOf outByte outOff)

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-! ### The owner functions -/

namespace Buffers

/-- **The compute thread that writes a byte of an output buffer**: for the byte at offset `x`
of its 4096-byte buffer (the two buffers start at offset 86912 of the window), the thread with
index `32 * (x / 1024) + x % 512 / 16` in its block: warp `x / 1024`, lane `x % 512 / 16`. -/
def outOwner (P : Params) (l : Loc) : Nat :=
  32 * ((l.addr - (P.sharedBase + 86912)) % 4096 / 1024) +
    (l.addr - (P.sharedBase + 86912)) % 4096 % 512 / 16

end Buffers

/-- **The owner functions of the buffer region** (see the header). -/
def owners (P : Params) (L : Launch) : Owners where
  out := Buffers.outOwner P
  final := Epilogue.finalOwner P
  piece l := Producer.pieceOf ((l.addr - (L.sharedBase + 32768)) % 18048)
  block := Startup.stateBlock P

namespace Buffers

/-- The owner function `piece` in the form the Producer phase's export takes. -/
theorem owners_piece (P : Params) (L : Launch) (l : Loc) :
    (owners P L).piece l = Producer.pieceOf ((l.addr - (L.sharedBase + 32768)) % 18048) := by
  simp only [owners]

/-- The owner of a byte of an output buffer is one of the 128 compute threads. -/
theorem outOwner_lt (P : Params) (l : Loc) : outOwner P l < 128 := by
  unfold outOwner
  omega

/-! ### The share of the Compute phase, as a statement -/

/-- **The share of the Compute phase in the buffer contracts**: four facts about an event of a
compute thread `g` at a followed state `s` with the phase's invariant `Compute.Inv P L X g j0 k
s`, for a thread whose followed state `s0` at `j0` satisfied the entry condition `Compute.In`.
`BuffersCompute.lean` proves it (`computeOwes`). -/
structure ComputeOwes (P : Params) (L : Launch) (X : Execution) : Prop where
  /-- `UnionFacts.thread`, classes `input` and `output`: a thread access of a byte of the
  buffer region of a block `c` is of the thread's own block and is a read of the input buffer
  of its tile between the poll of `loadFull` and the arrival on `loadEmpty` of the stage, or
  a write of a byte the thread owns of the output buffer of its tile between the poll of
  `storeEmpty` and the arrival on `storeFull` of the stage; six `bar.sync 0` precede it. -/
  thread : ∀ {g j0 k c : Nat} {s0 s : D} {a : Acc} {w : Bool} {l : Loc} (O : Owners),
    O.out = outOwner P → g < L.threads → At (code L) X g j0 s0 → Compute.In P L X g j0 s0 →
    At (code L) X g k s → Compute.Inv P L X g j0 k s → X.Access (g, k) a w → a.Covers l →
    InUnion L c l → g / L.block = c ∧ ThreadClass L X O c g k w l
  /-- `StoreCover.out_cover`: at its arrival on `storeFull o` the thread has written, since its
  previous arrival on that mbarrier, every byte of output buffer `o` that it owns. -/
  out_cover : ∀ {g j0 k pc tx cnt : Nat} {s0 s : D} {rel : Bool} {sc : MbarScope} (o : Fin 2)
    {l : Loc}, g < L.threads → At (code L) X g j0 s0 → Compute.In P L X g j0 s0 →
    At (code L) X g k s → Compute.Inv P L X g j0 k s →
    X.get (g, k) = some ⟨pc, .arrive ((Bar.storeFull o).loc L (g / L.block)) tx cnt rel sc⟩ →
    InOutput L (g / L.block) o.val l → outOwner P l = g % L.block →
      ∃ i pcw aw bs, i < k ∧ X.get (g, i) = some ⟨pcw, .wr aw bs⟩ ∧ aw.Covers l ∧
        arrivals ((Bar.storeFull o).loc L (g / L.block)) ((X.tr g).take i) =
          arrivals ((Bar.storeFull o).loc L (g / L.block)) ((X.tr g).take k)
  /-- `StoreCover.matrix_len`: a write event of the phase (the second event of an `stmatrix`)
  carries as many bytes as its footprint. -/
  matrix_len : ∀ {g j0 k pc : Nat} {s0 s : D} {a : Acc} {bs : List Byte}, g < L.threads →
    At (code L) X g j0 s0 → Compute.In P L X g j0 s0 → At (code L) X g k s →
    Compute.Inv P L X g j0 k s → X.get (g, k) = some ⟨pc, .wr a bs⟩ → bs.length = a.size
  /-- The frame of the writes (`StoresIssued.elem`, `finalAsync`): a write event of the phase
  is in shared memory. -/
  wr_shared : ∀ {g j0 k pc : Nat} {s : D} {a : Acc} {bs : List Byte}, g < L.threads →
    At (code L) X g k s → Compute.Inv P L X g j0 k s → X.get (g, k) = some ⟨pc, .wr a bs⟩ →
      a.loc.space = .shared

/-! ### Counting `bar.sync 0` -/

/-- The number of `bar.sync 0` before a position does not decrease along the trace. -/
theorem bar0_mono (X : Execution) (g : Nat) {j k : Nat} (h : j ≤ k) :
    bar0Before X (g, j) ≤ bar0Before X (g, k) :=
  (List.take_sublist_take_left h).countP_le

/-! ### The history: the thread has left the startup phase -/

theorem left_startup {j k : Nat} {s : D} (h : StartupDone P L X g j s) (hjk : j ≤ k) :
    Startup.Left P L X g k := ⟨j, hjk, s, h.state, h.out.1⟩

theorem left_conversion {j k : Nat} {s : D} (h : ConversionDone P L X g j s)
    (hjk : j ≤ k) : Startup.Left P L X g k := by
  obtain ⟨j0, s0, h0, hlen, -⟩ := h.entry
  exact left_startup h0 (by omega)

theorem left_carry {j k : Nat} {s : D} (h : CarryLoadDone P L X g j s) (hjk : j ≤ k) :
    Startup.Left P L X g k := by
  obtain ⟨j0, s0, h0, hlen, -⟩ := h.entry
  exact left_conversion h0 (by omega)

theorem left_tile {j k : Nat} {s : D} (h : TileDone P L X g j s) (hjk : j ≤ k) :
    Startup.Left P L X g k := by
  obtain ⟨j0, s0, h0, hle, -⟩ := h.entry
  exact left_carry h0 (by omega)

/-- A thread that has left the startup phase has polled the state mbarrier of its block. -/
theorem polled_of_left (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hg : g < L.threads) {k : Nat} (h : Startup.Left P L X g k) :
    1 ≤ okPolls (Bar.state.loc L (g / L.block)) ((X.tr g).take k) :=
  Startup.Left.statePolled hpre hX hg h

/-! ### The number of `bar.sync 0` before a state of a phase -/

/-- At most three `bar.sync 0` precede a state of the startup phase. -/
theorem bars_startup {k : Nat} {s : D} (hI : Startup.InvE P X g k s) :
    bar0Before X (g, k) ≤ 3 := by
  obtain ⟨pos, -, hl, -⟩ := hI
  have h1 : bar0Before X (g, k) = (Startup.led g pos).bars := congrArg Startup.Led.bars hl
  rw [h1]
  by_contra h
  obtain rfl := Startup.led_bars3 (g := g) (pos := pos) (by omega)
  exact h (Nat.le_refl 3)

/-- At most four `bar.sync 0` precede a state of the Conversion phase. -/
theorem bars_conversion {j0 k : Nat} {s : D} (hI : Conversion.Inv P X g j0 k s) :
    bar0Before X (g, k) ≤ 4 := by
  obtain ⟨pos, -, hl, -⟩ := hI
  have h1 : bar0Before X (g, k) = (Conversion.led g pos).bars := congrArg Startup.Led.bars hl
  rw [h1]
  cases pos with
  | bar j =>
    have hj := j.isLt
    show 3 + j.val ≤ 4
    omega
  | _ => exact (by decide : (3 : Nat) ≤ 4)

/-- Five `bar.sync 0` precede a state of the CarryLoad phase. -/
theorem bars_carry {j0 k : Nat} {s : D} (hI : CarryLoad.Inv P X g j0 k s) :
    bar0Before X (g, k) = 5 := by
  obtain ⟨pos, -, hl, -⟩ := hI
  exact congrArg Startup.Led.bars hl

/-- Five `bar.sync 0` precede the exit of the CarryLoad phase (the entry of a tile loop). -/
theorem bars_entry {j : Nat} {s : D} (h : CarryLoadDone P L X g j s) :
    bar0Before X (g, j) = 5 := congrArg Startup.Led.bars h.out.2.1

/-- The event before the exit of the CarryLoad phase is the proxy fence of instruction 1401. -/
theorem fence_entry {j : Nat} {s : D} (h : CarryLoadDone P L X g j s) :
    0 < j ∧ X.get (g, j - 1) = some ⟨1401, .fenceProxy (.async (some (.shared .cta))) none⟩ :=
  h.out.2.2

/-- At most six `bar.sync 0` precede a state of the Compute phase. -/
theorem bars_compute {j0 k : Nat} {s : D} (hI : Compute.Inv P L X g j0 k s) :
    bar0Before X (g, k) ≤ 6 := by
  obtain ⟨pos, -, hl, -⟩ := hI
  have h1 : bar0Before X (g, k) = (Compute.led pos).bar0 := congrArg Compute.Led.bar0 hl
  rw [h1]
  cases pos with
  | entry => exact (by decide : (5 : Nat) ≤ 6)
  | tile t n => exact Nat.le_refl 6

/-- At most six `bar.sync 0` precede a state of the Producer phase. -/
theorem bars_producer {k : Nat} {s : D} (hI : Producer.Inv P L X g k s) :
    bar0Before X (g, k) ≤ 6 := by
  obtain ⟨pos, -, hl⟩ := hI
  have h1 : bar0Before X (g, k) = (Producer.led P g pos).bars := congrArg Producer.Led.bars hl
  rw [h1]
  cases pos with
  | entry => exact (by decide : (5 : Nat) ≤ 6)
  | _ => exact Nat.le_refl 6

/-- At most six `bar.sync 0` precede a state of the Store phase. -/
theorem bars_store {k : Nat} {s : D} (hI : Store.Inv P X g k s) : bar0Before X (g, k) ≤ 6 := by
  obtain ⟨pos, -, hl⟩ := hI
  have h1 : bar0Before X (g, k) = (Store.led (P.length (seqOf P g)) pos).bars :=
    congrArg Store.Led.bars hl
  rw [h1]
  by_cases hp : pos = .entry
  · subst hp
    exact (by decide : (5 : Nat) ≤ 6)
  · rw [Store.led_bars hp]

/-- Six `bar.sync 0` precede the entry of the epilogue. -/
theorem bars_tile {j : Nat} {s : D} (h : TileDone P L X g j s) : bar0Before X (g, j) = 6 :=
  h.into.2

/-- The thread entered the epilogue at the exit of its tile loop, in the form the epilogue's
exports take. -/
theorem entered_epilogue {j : Nat} {s : D} (h : TileDone P L X g j s) :
    Epilogue.Entered P L X g j := ⟨s, h.state, h.into⟩

/-! ### The entry of a tile loop: the sixth `bar.sync 0` -/

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
include hpre hX

/-- The event at the exit of the CarryLoad phase (the entry of a tile loop) is the `bar.sync 0`
of instruction 1402. -/
theorem event_entry {j : Nat} {s : D} (h : CarryLoadDone P L X g j s) {e : Event}
    (he : X.get (g, j) = some e) : e = ⟨1402, .bar 0 none .sync⟩ :=
  CarryLoad.exit_event hpre hX he h.state h.out.1

/-- Past the entry of a tile loop the thread has made its sixth `bar.sync 0`. -/
theorem bars_after {j k : Nat} {s : D} (h : CarryLoadDone P L X g j s)
    (hjk : j < k) (hk : k ≤ (X.tr g).length) : 6 ≤ bar0Before X (g, k) := by
  obtain ⟨e0, he0⟩ : ∃ e0, (X.tr g)[j]? = some e0 := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain rfl := event_entry hpre hX h he0
  have h1 : bar0Before X (g, j + 1) = bar0Before X (g, j) + 1 :=
    count_snoc (Execution.isBarId 0) he0
  have h2 := bar0_mono X g (show j + 1 ≤ k by omega)
  have h3 := bars_entry h
  omega

/-- **A `bar.sync 0` of a thread in a tile loop with five or seven earlier ones** is the one
at the loop's entry, and directly follows the proxy fence of instruction 1401: past the entry
the thread has made six, and (`hle`) a state of a tile loop has at most six before it. -/
theorem entry_bar_fence {j k : Nat} {s : D} (h : CarryLoadDone P L X g j s)
    (hjk : j ≤ k) (hk : k ≤ (X.tr g).length) (hle : bar0Before X (g, k) ≤ 6)
    (hb : bar0Before X (g, k) = 5 ∨ bar0Before X (g, k) = 7) :
    0 < k ∧ ∃ pcf, X.get (g, k - 1) =
      some ⟨pcf, .fenceProxy (.async (some (.shared .cta))) none⟩ := by
  rcases Nat.eq_or_lt_of_le hjk with rfl | hlt
  · exact ⟨(fence_entry h).1, _, (fence_entry h).2⟩
  · have := bars_after hpre hX h hlt hk
    omega

end

/-! ### The kinds of event of each phase -/

/-- The kinds of event of the Conversion phase: reads, writes, the proxy fence, `bar.sync`,
and undefined behaviour (a store whose register does not convert). -/
def convKind : Kind → Bool
  | .rd .. | .wr .. | .ub .. | .fenceProxy .. | .bar .. => true
  | _ => false

/-- The kinds of event of the CarryLoad phase: reads and the proxy fence. -/
def carryKind : Kind → Bool
  | .rd .. | .fenceProxy .. => true
  | _ => false

/-- The kinds of event of the Compute phase: `bar.sync`, polls, arrivals, the proxy fence,
reads, writes, warp matrix events, and undefined behaviour. -/
def computeKind : Kind → Bool
  | .bar .. | .wait .. | .arrive .. | .fenceProxy .. | .rd .. | .wr .. | .matrix .. | .ub .. =>
    true
  | _ => false

/-- The kinds of site of the Compute phase. -/
def computeSite : SiteKind → Bool
  | .mbarWait | .matrixLoad | .matrixLoadMx | .warpMma | .matrixMove | .matrixStore
  | .matrixStoreWr | .load | .bar | .fenceProxy | .mbarArrive => true
  | _ => false

/-- The kinds of event of the Producer phase: `bar.sync`, polls, arrivals, tensor loads. -/
def prodKind : Kind → Bool
  | .bar .. | .wait .. | .arrive .. | .tensorIssue .. => true
  | _ => false

/-- The kinds of event of the Store phase: `bar.sync`, polls, arrivals, tensor stores, group
commits and waits, reads, writes, and undefined behaviour (a global store whose register does
not convert). -/
def storeKind : Kind → Bool
  | .bar .. | .wait .. | .arrive .. | .tensorStore .. | .bulkCommit | .bulkWait .. | .rd ..
  | .wr .. | .ub .. => true
  | _ => false

/-- The kinds of event of the epilogue: `bar.sync`, the proxy fence, writes, tensor stores, a
group commit and wait, the exit, and undefined behaviour (a store whose register does not
convert). -/
def epiKind : Kind → Bool
  | .bar .. | .fenceProxy .. | .wr .. | .tensorStore .. | .bulkCommit | .bulkWait .. | .exit
  | .ub .. => true
  | _ => false

/-- An event fired at a site of the Compute phase is of a kind of the Compute phase. -/
theorem computeKind_of_fired {kd : Kind} {κ : SiteKind} (hκ : computeSite κ = true)
    (h : firedAt kd κ = true) : computeKind kd = true := by
  cases κ <;> first | (cases hκ; done) | (cases kd <;> first | rfl | cases h)

/-- A state of the Compute phase is at a site of one of the phase's kinds. -/
theorem computeSite_of {pos : Compute.Pos} {s : D} (h : Compute.RefAt P L g pos s) :
    computeSite s.site.kind = true := by
  cases pos with
  | entry =>
    have hs : s.site = .bar 5 := h.site
    rw [hs]
    rfl
  | tile t n =>
    have hs : (Compute.skOf n).At s.site := h.site
    generalize Compute.skOf n = sk at hs
    cases sk with
    | ldMx j =>
      obtain ⟨row, hs⟩ := hs
      rw [hs]
      rfl
    | stWr j =>
      obtain ⟨row, hs⟩ := hs
      rw [hs]
      rfl
    | _ =>
      have hs' : s.site = _ := hs
      rw [hs']
      rfl

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads) {k : Nat} {s : D} {e : Event} (he : X.get (g, k) = some e)
  (hσ : At (code L) X g k s)
include hpre hX hg he hσ

/-- **The event at a state of the startup phase**, in closed form, with the position and the
ledger. -/
theorem ev_startup (hI : Startup.InvE P X g k s) :
    ∃ pos, Startup.RefAt P g pos s ∧
      Startup.ledOf ((X.tr g).take k) = Startup.led g pos ∧ Startup.Ev P L g pos e := by
  rcases Startup.event_at hpre hX hg he hσ with h | h
  · exact h
  · exact absurd h hI.inv.not_left

/-- The kind of an event at a state of the startup phase. -/
theorem kind_startup (hI : Startup.InvE P X g k s) : Startup.phaseKind e.kind = true := by
  obtain ⟨pos, -, -, hev⟩ := ev_startup hpre hX hg he hσ hI
  exact hev.phaseKind

/-- The kind of an event at a state of the Conversion phase. -/
theorem kind_conversion {j0 : Nat} (hI : Conversion.Inv P X g j0 k s) :
    convKind e.kind = true := by
  obtain ⟨pos, -, -, -, hev⟩ := Conversion.event_at hpre hX hg he hσ hI
  rcases hev.phaseKind with ⟨a, bs, h⟩ | ⟨a, bs, h⟩ | ⟨f, h⟩ | h | h <;> rw [h] <;> rfl

/-- The kind of an event at a state of the CarryLoad phase. -/
theorem kind_carry {j0 : Nat} (hI : CarryLoad.Inv P X g j0 k s) : carryKind e.kind = true := by
  obtain ⟨pos, -, hev, -⟩ := CarryLoad.event_at hpre hX hg he hσ hI
  rcases hev.kind_cases with ⟨a, bs, h, -⟩ | ⟨px, sc, h⟩ <;> rw [h] <;> rfl

omit hg in
/-- The kind of an event at a state of the Compute phase. -/
theorem kind_compute {j0 : Nat} (hI : Compute.Inv P L X g j0 k s) :
    computeKind e.kind = true := by
  obtain ⟨pos, hr, -⟩ := hI
  exact computeKind_of_fired (computeSite_of hr) (site_fires (sounds hpre) hX he hσ)

/-- **The event at a state of the Producer phase**, in closed form, with the position and the
ledger. -/
theorem ev_producer (hw : warp g = 4) (hI : Producer.Inv P L X g k s) :
    ∃ pos, Producer.RefAt P g pos s ∧
      Producer.ledOf L (g / L.block) ((X.tr g).take k) = Producer.led P g pos ∧
      Producer.Ev P L g pos e := by
  obtain ⟨pos, w, p, x, rfl, hr, hl, hev, -⟩ := Producer.producer_good hpre hX hg hw he hσ hI
  exact ⟨pos, hr, hl, hev⟩

/-- The kind of an event at a state of the Producer phase. -/
theorem kind_producer (hw : warp g = 4) (hI : Producer.Inv P L X g k s) :
    prodKind e.kind = true := by
  obtain ⟨pos, -, -, hev⟩ := ev_producer hpre hX hg he hσ hw hI
  cases pos with
  | entry => rw [show e = _ from hev]; rfl
  | poll c u => obtain ⟨ok, rfl⟩ := hev; rfl
  | arrive c u => rw [show e = _ from hev]; rfl
  | load c u i => rw [show e = _ from hev]; rfl
  | tail j => obtain ⟨ok, rfl⟩ := hev; rfl

/-- The kind of an event at a state of the Store phase. -/
theorem kind_store (hI : Store.Inv P X g k s) : storeKind e.kind = true := by
  obtain ⟨pos, -, -, hev, -⟩ := Store.store_good hpre hX hg he hσ hI
  cases pos with
  | entry => rw [show e = _ from hev]; rfl
  | wait t => obtain ⟨ok, rfl⟩ := hev; rfl
  | ts t i => rw [show e = _ from hev]; rfl
  | commit t => rw [show e = _ from hev]; rfl
  | ld0 t row c => obtain ⟨bs, -, rfl⟩ := hev; rfl
  | ld1 t row c v0 => obtain ⟨bs, -, rfl⟩ := hev; rfl
  | ld2 t row c v0 v1 => obtain ⟨bs, -, rfl⟩ := hev; rfl
  | ld3 t row c v0 v1 v2 => obtain ⟨bs, -, rfl⟩ := hev; rfl
  | gst t row c j => rcases hev with ⟨v, -, rfl⟩ | ⟨f, -, rfl⟩ <;> rfl
  | bwait t => rw [show e = _ from hev]; rfl
  | arrive t => rw [show e = _ from hev]; rfl

omit hσ in
/-- The kind of an event of a thread in the epilogue. -/
theorem kind_epilogue {j0 : Nat} {s0 : D} (past : TileDone P L X g j0 s0) (hj : j0 ≤ k) :
    epiKind e.kind = true := by
  rcases Epilogue.kind_in hpre hX hg (entered_epilogue past) hj he with
    ⟨f, h⟩ | ⟨a, bs, h⟩ | h | h | ⟨al, sp, h⟩ | h | h | h <;> rw [h] <;> rfl

end

/-! ### Accesses, roles, and the two result arrays -/

/-- **The event of a thread access**: a read, a write (then the access writes), or an atomic
read-modify-write of the access's footprint. -/
theorem access_event {k : Nat} {a : Acc} {w : Bool} (h : X.Access (g, k) a w) :
    ∃ e, X.get (g, k) = some e ∧ ((∃ bs, e.kind = .rd a bs) ∨
      (∃ bs, e.kind = .wr a bs ∧ w = true) ∨ ∃ o n, e.kind = .rmw a o n) := by
  rcases h with ⟨bs, ⟨pc, he⟩, -⟩ | ⟨bs, ⟨pc, he⟩, rfl⟩ | ⟨o, n, pc, he⟩
  · exact ⟨_, he, .inl ⟨bs, rfl⟩⟩
  · exact ⟨_, he, .inr (.inl ⟨bs, rfl, rfl⟩)⟩
  · exact ⟨_, he, .inr (.inr ⟨o, n, rfl⟩)⟩

/-- An event of the class "`bar.sync 0`" is a barrier event with barrier 0. -/
theorem bar0_of_isBarId {e : Event} (h : Execution.isBarId 0 e = true) :
    ∃ pc cnt mode, e = ⟨pc, .bar 0 cnt mode⟩ := by
  obtain ⟨pc, kd⟩ := e
  cases kd with
  | bar id cnt mode =>
    obtain rfl : id = 0 := by simpa [Execution.isBarId] using h
    exact ⟨pc, cnt, mode, rfl⟩
  | _ => cases h

/-- Compute thread `a` of block `c`: its block and its index in the block. -/
theorem computeThread_role (hpre : Pre P L mem0) (c : Nat) (a : Fin 128) :
    computeThread L c a / L.block = c ∧ computeThread L c a % L.block = a.val ∧
      tid (computeThread L c a) = a.val := by
  have h1 : computeThread L c a % L.block = a.val :=
    Protocol.thr_mod hpre.block (by have := a.isLt; omega)
  exact ⟨Protocol.computeThread_div hpre.block a, h1, (block_mod hpre).symm.trans h1⟩

/-- A compute thread is in neither the load warp nor the store warp. -/
theorem not_warp45 (ht : tid g < 128) : warp g ≠ 4 ∧ warp g ≠ 5 := by
  unfold tid at ht
  unfold warp
  omega

/-- The store leader of the block of sequence `sq` and head `h`: its block, its index in the
block (160: lane 0 of the store warp), its sequence and its head. -/
theorem storeLeader_role (hpre : Pre P L mem0) {sq h : Nat} (hs : sq < P.sequences) :
    storeLeader L (blockOf P sq h) / L.block = blockOf P sq h ∧
      tid (storeLeader L (blockOf P sq h)) = 160 ∧ warp (storeLeader L (blockOf P sq h)) = 5 ∧
      lane (storeLeader L (blockOf P sq h)) = 0 ∧
      seqOf P (storeLeader L (blockOf P sq h)) = sq ∧
      headOf P (storeLeader L (blockOf P sq h)) = h := by
  have hd : storeLeader L (blockOf P sq h) / L.block = blockOf P sq h :=
    Protocol.thr_div hpre.block (by decide)
  have hm : storeLeader L (blockOf P sq h) % L.block = 160 :=
    Protocol.thr_mod hpre.block (by decide)
  rw [hpre.block] at hd hm
  refine ⟨by rw [hpre.block]; exact hd, hm, ?_, ?_, ?_, ?_⟩
  · unfold warp; omega
  · unfold lane; omega
  · unfold seqOf
    rw [hd]
    exact Protocol.blockOf_mod hs
  · unfold headOf
    rw [hd]
    exact Protocol.blockOf_div hs

/-- **No byte is both an output byte and a final-state byte**: the two arrays are apart
(`Pre.outputApartFinal`). -/
theorem out_ne_state (hpre : Pre P L mem0) {l : Loc} (ho : P.OutputByte l)
    (hs : P.StateByte l) : False := by
  obtain ⟨k1, hk1, rfl⟩ := Top.outputByte_range ho
  obtain ⟨k2, hk2, h⟩ := Top.stateByte_range hs
  have hap := hpre.outputApartFinal
  simp only [Loc.mk.injEq, true_and] at h
  unfold Apart at hap
  omega

/-! ### Phase by phase: what the three contracts need beyond the phases' exports -/

/-- The entry of the CarryLoad phase in the form its exports take, from the history. -/
theorem entered_carry {j : Nat} {s : D} (h : ConversionDone P L X g j s) :
    ∃ j0, CarryLoad.Entered P L X g j0 j := by
  obtain ⟨j0, s0, hs, hlen, -⟩ := h.entry
  exact ⟨j0, hs.firstOut, hlen, s, h.state, h.out⟩

/-- Among the barrier sites, only the one of instruction 2913 is a position of a tile of the
Compute phase. -/
theorem bar_idx : ∀ j : Fin 10, Compute.skTab.idxOf (.bar j) < 268 → j = 6 := by
  decide +kernel

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
include hpre hX

/-- **A barrier event at a state of the Compute phase** is the `bar.sync 0` of the entry (five
`bar.sync 0` before it) or the named barrier 8 of a tile (instruction 2913). -/
theorem bar_compute {j0 k pc id : Nat} {cnt : Option Nat} {mode : BarMode} {s : D}
    (he : X.get (g, k) = some ⟨pc, .bar id cnt mode⟩) (hσ : At (code L) X g k s)
    (hI : Compute.Inv P L X g j0 k s) : bar0Before X (g, k) = 5 ∨ id = 8 := by
  obtain ⟨pos, hr, hl, -⟩ := hI
  cases pos with
  | entry => exact .inl (congrArg Compute.Led.bar0 hl)
  | tile t n =>
    right
    have hn : n < 268 := hr.facts.pos
    obtain ⟨j, hs⟩ := bar_site (sounds hpre) hX he hσ rfl
    have hat : (Compute.skOf n).At s.site := hr.site
    have hn' : n = Compute.skTab.idxOf (.bar j) :=
      Compute.pos_of_site hn hat (by rw [hs]; rfl)
    obtain rfl : j = 6 := bar_idx j (by omega)
    obtain rfl : n = 264 := hn'.trans (by decide +kernel)
    obtain ⟨site, w, p, x⟩ := s
    obtain rfl : site = .bar 6 := hs
    obtain ⟨tt, ins, o, hat', -, hc, hf⟩ := Frame.fired_site (sounds hpre) hX he hσ
    have h8 := Compute.ev_bar8 hpre hr.facts hat' hc hf
    cases h8
    rfl

/-- **A state of the Producer phase is not past the phase**: a thread that has left the load
loop is in the epilogue, at an instruction from 3113 on. -/
theorem producer_not_left (hg : g < L.threads) (hr : warp g = 4) {k : Nat} {s : D}
    (hk : k ≤ (X.tr g).length) (hσ : At (code L) X g k s) (hI : Producer.Inv P L X g k s) :
    ¬ Producer.Left P L X g k := by
  rintro ⟨j, hj, s1, hσ1, ho⟩
  have hW := Epilogue.epilogue_weak hpre hX hg hσ1 (Epilogue.in_of_producer hr ho) hj hk hσ
  have h1 := pc_epilogue hW
  have h2 := pc_producer hI
  omega

/-- **An event with seven or more `bar.sync 0` before it is an event of the epilogue**: the
thread's seventh `bar.sync 0` (the one with six before it) is the epilogue's first event. The
event itself may be of any kind, also undefined behaviour. -/
theorem epi_of_bars {k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hb : 7 ≤ bar0Before X (g, k)) : ∃ j0 s0, TileDone P L X g j0 s0 ∧ j0 < k := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨j, ej, hjk, hej, hbar, hcnt⟩ := exists_nthEv (X := X) (p := Execution.isBarId 0)
    (g := g) (k := k) (n := 6) hb
  obtain ⟨pc, cnt, mode, rfl⟩ := bar0_of_isBarId hbar
  have hcnt' : bar0Before X (g, j) = 6 := hcnt
  obtain ⟨s, hσ, hst, hub⟩ := event_stage hpre hX hej (fun f h => by cases h)
  cases hst with
  | startup hI =>
    have := bars_startup hI
    omega
  | conversion past hj hI =>
    have := bars_conversion hI
    omega
  | carryLoad past hj hI =>
    have := bars_carry hI
    omega
  | compute hr past hj hin hI => rcases bar_compute hpre hX hej hσ hI with h | h <;> omega
  | producer hr past hj hen hI =>
    obtain ⟨pos, -, hl, hev⟩ := ev_producer hpre hX hg hej hσ hr hI
    have h5 : bar0Before X (g, j) = 5 := (Producer.bar_shape hl hev).2.2.2.2.2
    omega
  | store hr past hj hin hI hW =>
    have h5 := (Store.bar_store hpre hX hg hej hσ (hI hub)).2.2.2.2.2
    omega
  | epilogue past hj hW hI => exact ⟨_, _, past, by omega⟩

end

end Buffers

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
