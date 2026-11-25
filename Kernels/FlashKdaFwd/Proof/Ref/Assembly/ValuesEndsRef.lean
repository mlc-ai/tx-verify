-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Assembly.Tracked
public import Kernels.FlashKdaFwd.Proof.Ref.Conversion.Exports
public import Kernels.FlashKdaFwd.Proof.Ref.CarryLoad.CarryRef
public import Kernels.FlashKdaFwd.Proof.Ref.Epilogue.ValueEnds
public import Kernels.FlashKdaFwd.Proof.Ref.Store.Walk
public import Kernels.FlashKdaFwd.Proof.Ref.Source.Fit
public import Kernels.FlashKdaFwd.Proof.Values.Ends.Contract
public import Kernels.FlashKdaFwd.Proof.Protocol.ResultGuard

@[expose] public section

/-!
# The reference-layer contracts of the values at the ends of the tile loop, for a whole execution

The value layer of the four stretches around the tile loop (`Proof/Values/Ends/`: the conversion
loop, the carry loads, the final stores, the store path of a partial last tile) takes five
structures from the reference layer (`Values/Ends/Contract.lean`): `ConvRef`, `CarryRef`,
`FinalRef`, `StoreRef` and `StoreCtl`. Their fields speak about a followed state or an event of
ANY thread at ANY position. Each phase of the reference layer proved its share for a state that
carries the phase's invariant. This file joins the two with the case principle of the chain
(`Stage.lean`, `Sites.lean`, `Tracked.lean`): the instruction of a state, or the number of
`bar.sync 0` before an event, decides the phase the thread is in.

**Words.** A *followed state* of thread `g` at position `k` is the state `s` of the thread's
machine before the thread's `k`-th event (`Frame.stateAt (code L) X g k = some (some s)`);
`s.site` is the event instruction the machine is at and `s.site.pc` its index in the program.
A *compute thread* has index `tid g = g % L.block` below 128 in its thread block; the *store
warp* is the threads 160 to 191 of a block and its lane 0 the *store leader*. `bar0Before X
(g, k)` is the number of `bar.sync 0` events of thread `g` before position `k`. *Undefined
behaviour* is an event of kind `.ub`; `NoUb X g k` says that none of the first `k` events of
thread `g` is one.

## What is here

Helpers are in the namespace `Assembly.ValuesEnds`; the final theorems are in `Assembly`.

* `ValuesEnds.lt_threads_of_pc`: a followed state past the startup phase belongs to a launched
  thread.
* `ValuesEnds.wr_stage`, `wr_cases`: a write event fires from a followed state that is in a
  stage, at one of four families of sites (a conversion store, the row write of an `stmatrix`,
  an element store of a partial tile, a final store).
* `convRef`, `finalRef`, `carryRef`: no hypothesis besides the precondition and consistency.
  They use the exports of the Conversion phase (`Ref/Conversion/Exports.lean`), of the epilogue
  (`Ref/Epilogue/ValueEnds.lean`) and of the CarryLoad phase (`Ref/CarryLoad/CarryRef.lean`:
  `carry_load`, `carry_first`). That file's own `carryRef_of` is not used: its hypothesis
  `AtCarry` asks for the phase's invariant at every position `k` of a followed state at a carry
  site, and the invariant fixes `k` to the number of events since the entry, which fails for a
  position beyond the end of the trace of a thread that stopped at a carry site.
* `ValuesEnds.StoreOwes P L X`: what the Store phase has to prove for the store path of a
  partial last tile, in the phase's own vocabulary (one event or one followed state with the
  data of the constructor `Stage.store`). `ValuesEnds.ComputeOwes P L X`: the two facts of the
  Compute phase that this directory needs (a write of the tile loop is to shared memory; an
  access of the tile loop that covers a byte of the bfloat16 state copy is a 16-byte row).
* `ValuesEnds.storeRef_of`, `ValuesEnds.storeCtl_of`: `StoreRef` and `StoreCtl` from these two
  structures. The Store phase proves `StoreOwes` in `Ref/Store/ValuesOwes.lean`, which imports
  this file, and `ValuesEndsCompute.lean` proves `ComputeOwes`; so the final `storeRef` and
  `storeCtl` are in `ValuesEnds.lean`.
* `ValuesEnds.followed` (the thread layer's `Values.Followed`) and `ValuesEnds.earlyRead` (what
  a read of the FP32 buffer returns before the tile loop), from the protocol contracts.
-/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Protocol (bar0Before storeLeader Facts UnionFacts StoreCover Owners
  ctaTiles noEvents InStateAcc)
open PTX.Kernels.FlashKdaFwd.Proof.Values (Followed)
open PTX.Kernels.FlashKdaFwd.Proof.Values.Ends (ConvRef CarryRef FinalRef StoreRef StoreCtl
  EarlyRead finalSite carrySite convReg carryReg elemReg storeFullBar)

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

namespace ValuesEnds

/-! ### What two phases still owe -/

/-- **The index of an element read of the store leader's vector load** (instruction 3020, in
the store of a partial last tile): 0 at the machine's load site 177, and 1, 2, 3 at its three
continuation sites, which carry the values already read; none at every other site. -/
def readIdx : Site → Option Nat
  | .load j => if j.val = 177 then some 0 else none
  | .loadEl1 _ _ => some 1
  | .loadEl2 _ _ _ => some 2
  | .loadEl3 _ _ _ _ => some 3
  | _ => none

/-- **What the Compute phase owes to the values at the ends of the tile loop.** Both fields
are about an event of a launched thread `g` at a followed state `s` with the invariant of the
Compute phase (`Compute.Inv P L X g j0 k s`: the thread entered the tile loop before its event
`j0`). -/
structure ComputeOwes (P : Params) (L : Launch) (X : Execution) : Prop where
  /-- **A write of the tile loop is to shared memory** (it is the row write of an `stmatrix`).
  Used to tell the element stores of a partial tile, which write global memory, from the
  writes of the compute threads. -/
  wr_shared : ∀ g j0 k s pc a bs, g < L.threads →
    Frame.stateAt (code L) X g k = some (some s) → Compute.Inv P L X g j0 k s →
    X.get (g, k) = some ⟨pc, .wr a bs⟩ → a.loc.space = .shared
  /-- **An access of the tile loop that covers a byte of the bfloat16 state copy**
  (`state_acc`, window offsets 0 to 32767 of a block `c`) **is an access of a whole row**: 16
  bytes at a multiple of 16 from `shared_mem`. (The scalar loads and the other rows of the
  tile loop are in the buffer region, from offset 32768 on.) This is the hypothesis `hrow` of
  the protocol layer's read-back `StateAccFacts.acc_read`. -/
  acc_row : ∀ g j0 k s a w l c, g < L.threads →
    Frame.stateAt (code L) X g k = some (some s) → Compute.Inv P L X g j0 k s →
    X.Access (g, k) a w → a.Covers l → InStateAcc L c l →
    a.size = 16 ∧ ∃ r, a.loc.addr = L.sharedBase + 16 * r

/-- **What the Store phase owes to the values at the ends of the tile loop**, for the store
path of a partial last tile (per live row and chunk of eight value channels: the vector load
`ld.shared.v4.b32` at instruction 3020, four read events at the machine's sites `load 177`,
`loadEl1`, `loadEl2`, `loadEl3`; then eight `st.global.b16`, the sites `store 10` to
`store 17`). Every field is about a launched thread `g` and a followed state `s` at position
`k` with the invariant of the Store phase (`Store.Inv P X g k s`); where two positions are
related, the thread entered the phase before its event `k0 ≤ k` (`Store.Entered P L X g k0`).
The field `chunk` has no event at `k`, so it takes the data of the constructor `Stage.store`:
the weak invariant, and the invariant under the guard `NoUb X g k`. -/
structure StoreOwes (P : Params) (L : Launch) (X : Execution) : Prop where
  /-- **An element store** (`StoreCtl.elem`, and with it `StoreRef.elem`): a state at the
  `i`-th element store with an event is `4 + i` events after a followed state at the vector
  load; and if the register it stores converts to a 16-bit value, the event is the write of
  that value's bytes (the address does not fault). -/
  elem : ∀ g k0 k s e, ∀ i : Fin 8, g < L.threads → Store.Entered P L X g k0 → k0 ≤ k →
    Frame.stateAt (code L) X g k = some (some s) → Store.Inv P X g k s →
    s.site = .store ⟨10 + i.val, by omega⟩ → X.get (g, k) = some e →
    (∃ k1 d0, k = k1 + 4 + i.val ∧ Frame.stateAt (code L) X g k1 = some (some d0) ∧
      d0.site = .load 177) ∧
    ∀ v', storeValue 16 (s.x (elemReg i.val)) = .ok v' → ∃ a, e = ⟨s.site.pc, .wr a v'.toBytes⟩
  /-- **One chunk of a live row** (`StoreRef.chunk`, verbatim, for a state of the phase): at
  the vector load the thread is the store leader of its block, and there are a tile `t`, a
  row `row` of it that is a token of the sequence and a chunk `c` such that the next four
  events, where they are reads, are the four 4-byte elements of the 16 bytes at offset
  `16 row + 256 c` of the output stage of the tile, each after `t / 2 + 1` successful polls of
  the stage's "full" mbarrier, and the eight events after them, where they are writes, are the
  2-byte stores of the outputs of the channels `8 c` to `8 c + 7` of the token. -/
  chunk : ∀ g k0 k s, g < L.threads → Store.Entered P L X g k0 → k0 ≤ k →
    k ≤ (X.tr g).length → Frame.stateAt (code L) X g k = some (some s) → StoreWeak P g s →
    (NoUb X g k → Store.Inv P X g k s) → s.site = .load 177 →
    g = storeLeader L (g / L.block) ∧
    ∃ t row c, row < 16 ∧ c < 16 ∧ 16 * t + row < P.length (Values.seqOf P L g) ∧
      (∀ m < 4, ∀ pc a bs, X.get (g, k + m) = some ⟨pc, .rd a bs⟩ → a.size = 4 ∧
        a.loc = ⟨.shared, g / L.block,
          L.sharedBase + (86912 + 4096 * (t % 2) + (16 * row + 256 * c + 4 * m))⟩ ∧
        okPolls (storeFullBar L g t) ((X.tr g).take (k + m)) = t / 2 + 1) ∧
      ∀ i : Fin 8, ∀ pc a bs, X.get (g, k + 4 + i.val) = some ⟨pc, .wr a bs⟩ → a.size = 2 ∧
        ∃ v : Fin 128, v.val = 8 * c + i.val ∧
          a.loc = P.outLoc (Values.seqOf P L g) (Values.headOf P L g) (16 * t + row) v
  /-- **An element read**: a state at the `m`-th element read of the vector load (`readIdx`)
  with an event is `m` events after a followed state at the first one (the site `load 177`),
  and the events from there up to this one are reads (a load faults on its address only). -/
  reads : ∀ g k0 k s e m, g < L.threads → Store.Entered P L X g k0 → k0 ≤ k →
    Frame.stateAt (code L) X g k = some (some s) → Store.Inv P X g k s →
    readIdx s.site = some m → X.get (g, k) = some e →
    m ≤ k ∧ (∃ d0, Frame.stateAt (code L) X g (k - m) = some (some d0) ∧ d0.site = .load 177) ∧
      ∀ n ≤ m, ∃ pc a bs, X.get (g, k - m + n) = some ⟨pc, .rd a bs⟩
  /-- **No access of the phase covers a byte of the bfloat16 state copy** `state_acc` (the
  element reads are in the output buffers, the element stores in global memory). Used for the
  hypothesis `hrow` of the protocol layer's read-back `StateAccFacts.acc_read`. -/
  acc_free : ∀ g k s a w l c, g < L.threads →
    Frame.stateAt (code L) X g k = some (some s) → Store.Inv P X g k s →
    X.Access (g, k) a w → a.Covers l → ¬ InStateAcc L c l
  /-- **No tensor store of the phase writes a byte of the final state** (the stores of a full
  tile write the output array `out`, which `Pre.outputApartFinal` keeps apart from the final
  state). Used to tell the stores of the final state, which are the epilogue's. -/
  ts_out : ∀ g k s pc al sp x y z l, g < L.threads →
    Frame.stateAt (code L) X g k = some (some s) → Store.Inv P X g k s →
    X.get (g, k) = some ⟨pc, .tensorStore al sp⟩ → TensorStore.writeLoc sp x y z = some l →
    ¬ P.StateByte l

/-! ### Launched threads, and where a write is fired -/

/-- **A followed state past the startup phase belongs to a launched thread**: a thread outside
the launch has no events, so its only state is the initial one, at an instruction of the
startup phase (at most 384). -/
theorem lt_threads_of_pc (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) {k : Nat} {s : D}
    (hσ : At (code L) X g k s) (hpc : 384 < s.site.pc) : g < L.threads := by
  by_contra hn
  have h0 : (X.tr g).length = 0 := by rw [hX.outside g (by omega)]; rfl
  rw [At, Frame.stateAt_of_le (by omega), h0, Frame.stateAt_zero] at hσ
  obtain rfl : (code L g).init = s := Option.some.inj (Option.some.inj hσ)
  obtain ⟨pos, hr, -⟩ := Startup.st_init (L := L) (g := g) hpre
  have h1 := startup_pos_pc pos
  rw [← hr.site] at h1
  have h2 : (init L g).site.pc = (code L g).init.site.pc := rfl
  omega

/-- **The store sites by family**: the ten conversion stores are at instructions 388 to 620,
the eight element stores of a partial tile at 2945 to 3112, the 128 final stores after 3113. -/
theorem store_site_pc : ∀ j : Fin 146,
    (j.val < 10 ∧ 387 < (Site.store j).pc ∧ (Site.store j).pc ≤ 620) ∨
    (10 ≤ j.val ∧ j.val < 18 ∧ 2944 < (Site.store j).pc ∧ (Site.store j).pc ≤ 3112) ∨
    (18 ≤ j.val ∧ 3113 < (Site.store j).pc) := by decide +kernel

/-- The row writes of the `stmatrix` instructions are at instructions of the compute loop. -/
theorem stWr_site_pc (j : Fin 18) (row : List (Option Byte)) :
    2105 < (Site.matrixStoreWr j row).pc ∧ (Site.matrixStoreWr j row).pc ≤ 2944 := by
  have h : ∀ j : Fin 18,
      2105 < (Site.matrixStoreWr j []).pc ∧ (Site.matrixStoreWr j []).pc ≤ 2944 := by
    decide +kernel
  exact h j

/-- The vector load of the store path is at an instruction of the store leader's loop. -/
theorem load177_pc : 2944 < (Site.load 177).pc ∧ (Site.load 177).pc ≤ 3112 := by decide

/-- The register that the `j`-th conversion store writes, in the two layers' names. -/
theorem convReg_eq : ∀ j : Fin 10, convReg j.val = Conversion.nrReg j.val := by decide

/-- A followed state at a conversion load is at an instruction of the Conversion phase. -/
theorem conv_load_range {s : D} (j : Fin 10) (hs : s.site = .load ⟨21 + j.val, by omega⟩) :
    387 ≤ s.site.pc ∧ s.site.pc ≤ 621 := by
  have h := conv_load_pc j
  rw [← hs] at h
  omega

/-- A followed state at a conversion store is at an instruction of the Conversion phase. -/
theorem conv_store_range {s : D} (j : Fin 10) (hs : s.site = .store ⟨j.val, by omega⟩) :
    387 ≤ s.site.pc ∧ s.site.pc ≤ 621 := by
  have h := conv_store_pc j
  rw [← hs] at h
  omega

/-- A followed state at a carry load, or at the proxy fence after the carry loads, is at an
instruction of the CarryLoad phase. -/
theorem carry_range {s : D} {j : Nat} (hj : j ≤ 128) (hs : s.site = carrySite j) :
    621 < s.site.pc ∧ s.site.pc < 1402 := by
  rw [hs]
  rcases Nat.lt_or_ge j 128 with h | h
  · have h1 : 765 ≤ (carrySite j).pc ∧ (carrySite j).pc ≤ 1400 := carry_ld_pc ⟨j, h⟩
    omega
  · obtain rfl : j = 128 := by omega
    exact ⟨by decide, by decide⟩

/-- A followed state at a final store is at an instruction of the epilogue after its first
`bar.sync 0`. -/
theorem final_range {s : D} (j : Fin 128) (hs : s.site = finalSite j) :
    3113 < s.site.pc ∧ s.site.pc ≤ 3775 := by
  have h := epi_st_pc j
  rw [← show finalSite j = Site.store ⟨18 + j.val, by omega⟩ from rfl, ← hs] at h
  exact h

/-- A followed state at an element store of a partial tile is at an instruction of the store
leader's loop. -/
theorem elem_range {s : D} (i : Fin 8) (hs : s.site = .store ⟨10 + i.val, by omega⟩) :
    2944 < s.site.pc ∧ s.site.pc ≤ 3112 := by
  have h := store_gst_pc i
  rw [← hs] at h
  omega

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
include hpre hX

/-- **The site of a write event**, by family: a conversion store, the row write of an
`stmatrix`, an element store of a partial tile, or a final store (`Ref/Kinds`: a write is
fired at a store site or at the second event of an `stmatrix`). -/
theorem wr_cases {k pc : Nat} {a : Acc} {bs : List Byte} {s : D}
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) (hσ : At (code L) X g k s) :
    (∃ j : Fin 10, s.site = .store ⟨j.val, by omega⟩) ∨
    (∃ j row, s.site = .matrixStoreWr j row) ∨
    (∃ i : Fin 8, s.site = .store ⟨10 + i.val, by omega⟩) ∨
    ∃ j : Fin 128, s.site = finalSite j := by
  rcases wr_site (sounds hpre) hX he hσ rfl with ⟨j, hs⟩ | ⟨j, row, hs⟩
  · rcases Nat.lt_or_ge j.val 10 with h | h
    · exact .inl ⟨⟨j.val, h⟩, hs⟩
    · rcases Nat.lt_or_ge j.val 18 with h' | h'
      · refine .inr (.inr (.inl ⟨⟨j.val - 10, by omega⟩, ?_⟩))
        rw [hs]
        exact congrArg Site.store (Fin.ext (by simp only; omega))
      · refine .inr (.inr (.inr ⟨⟨j.val - 18, by omega⟩, ?_⟩))
        rw [hs]
        exact congrArg Site.store (Fin.ext (by simp only; omega))
  · exact .inr (.inl ⟨j, row, hs⟩)

/-- **A write event is fired at an instruction after 387.** -/
theorem wr_pc {k pc : Nat} {a : Acc} {bs : List Byte} {s : D}
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) (hσ : At (code L) X g k s) :
    387 < s.site.pc :=
  wr_site_ind (sounds hpre) hX he hσ rfl (P := fun t => 387 < t.pc)
    (fun j => by rcases store_site_pc j with h | h | h <;> omega)
    fun j row => by have := stWr_site_pc j row; omega

/-- **A write event fires from a followed state, which is in a stage**, at an instruction
after 387, and the number of `bar.sync 0` before it is the one of the instruction range of the
state: three up to instruction 620, four at 621, five up to 1402, six up to 3113, at least
seven after. -/
theorem wr_stage {k pc : Nat} {a : Acc} {bs : List Byte}
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) :
    ∃ s, At (code L) X g k s ∧ Stage P L X g k s ∧ NoUb X g k ∧ 387 < s.site.pc ∧
      (s.site.pc ≤ 620 → bar0Before X (g, k) = 3) ∧
      (s.site.pc = 621 → bar0Before X (g, k) = 4) ∧
      (621 < s.site.pc → s.site.pc ≤ 1402 → bar0Before X (g, k) = 5) ∧
      (1402 < s.site.pc → s.site.pc ≤ 3113 → bar0Before X (g, k) = 6) ∧
      (3113 < s.site.pc → 7 ≤ bar0Before X (g, k)) := by
  obtain ⟨s, hσ, hst, hub⟩ := event_stage hpre hX he (fun f h => by cases h)
  have hpc := wr_pc hpre hX he hσ
  obtain ⟨-, b2, b3, b4, b5, b6⟩ := hst.bar0_bounds hub
  exact ⟨s, hσ, hst, hub, hpc, fun h => b2 (by omega) h, b3, b4, b5, fun h => (b6 h).1⟩

/-- **A write event with three `bar.sync 0` before it is an event of the Conversion phase**:
it fires from a followed state with the phase's invariant, in a thread that entered the phase
at a followed state before its event `j0`. -/
theorem conv_of_wr3 {k pc : Nat} {a : Acc} {bs : List Byte}
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) (hbar : bar0Before X (g, k) = 3) :
    ∃ s j0 s0, At (code L) X g k s ∧ StartupDone P L X g j0 s0 ∧ j0 ≤ k ∧
      Conversion.Inv P X g j0 k s := by
  obtain ⟨s, hσ, hst, -, hpc, -, b3, b4, b5, b6⟩ := wr_stage hpre hX he
  have h621 : s.site.pc ≤ 621 := by
    by_contra hc
    rcases Nat.lt_or_ge 1402 s.site.pc with h | h
    · rcases Nat.lt_or_ge 3113 s.site.pc with h' | h'
      · have := b6 h'
        omega
      · have := b5 h h'
        omega
    · have := b4 (by omega) h
      omega
  obtain ⟨j0, s0, past, hj, hI⟩ := hst.of_pc_conversion (by omega) h621
  exact ⟨s, j0, s0, hσ, past, hj, hI⟩

/-- **A followed state at a final store is a state of the epilogue**, of a launched thread
that entered the epilogue at or before the position. -/
theorem final_entered {k : Nat} {s : D} (j : Fin 128) (hk : k ≤ (X.tr g).length)
    (hσ : At (code L) X g k s) (hs : s.site = finalSite j) :
    g < L.threads ∧ ∃ k0, Epilogue.Entered P L X g k0 ∧ k0 ≤ k := by
  obtain ⟨h1, h2⟩ := final_range j hs
  have hg := lt_threads_of_pc hpre hX hσ (by omega)
  obtain ⟨j0, s0, past, hj, -, -⟩ :=
    (stage hpre hX hg hk hσ).of_pc_epilogue (by omega) (.inr h1)
  exact ⟨hg, j0, ⟨s0, past.state, past.into⟩, hj⟩

/-- **A followed state at an instruction of the store leader's loop is a state of the Store
phase**, of a launched thread that entered the phase at or before the position; its invariant
is guarded, its weak invariant is not. -/
theorem store_entered {k : Nat} {s : D} (hk : k ≤ (X.tr g).length)
    (hσ : At (code L) X g k s) (h1 : 2944 < s.site.pc) (h2 : s.site.pc ≤ 3112) :
    g < L.threads ∧ ∃ k0, Store.Entered P L X g k0 ∧ k0 ≤ k ∧
      (NoUb X g k → Store.Inv P X g k s) ∧ StoreWeak P g s := by
  have hg := lt_threads_of_pc hpre hX hσ (by omega)
  obtain ⟨-, j0, s0, past, hj, hin, hI, hW⟩ := (stage hpre hX hg hk hσ).of_pc_store h1 h2
  exact ⟨hg, j0, ⟨s0, past.state, hin⟩, hj, hI, hW⟩

/-! ### The control half of the stores, field by field -/

/-- `StoreCtl.conv` for the whole execution. -/
theorem storeCtl_conv {k : Nat} {d : D} {e : Event} (j : Fin 10)
    (hσ : At (code L) X g k d) (hs : d.site = .store ⟨j.val, by omega⟩)
    (he : X.get (g, k) = some e) :
    (∃ k0 d0, k = k0 + 1 ∧ Frame.stateAt (code L) X g k0 = some (some d0) ∧
      d0.site = .load ⟨21 + j.val, by omega⟩) ∧
    ∀ v', storeValue 16 (d.x (convReg j.val)) = .ok v' →
      ∃ a, e = ⟨d.site.pc, .wr a v'.toBytes⟩ := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨h1, h2⟩ := conv_store_range j hs
  obtain ⟨j0, s0, past, -, hI⟩ := (stage_event hpre hX hg he hσ).1.of_pc_conversion h1 h2
  rw [convReg_eq j]
  exact Conversion.store_ctl hpre hX hg j past.state past.conversion_in hσ hI hs he

/-- `StoreCtl.final` for the whole execution. -/
theorem storeCtl_final {k : Nat} {d : D} {e : Event} (j : Fin 128)
    (hσ : At (code L) X g k d) (hs : d.site = finalSite j) (he : X.get (g, k) = some e)
    {v' : Value} (hv : storeValue 32 (d.x (carryReg j.val)) = .ok v') :
    ∃ a, e = ⟨d.site.pc, .wr a v'.toBytes⟩ := by
  have hk : k ≤ (X.tr g).length := Nat.le_of_lt (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨hg, k0, hE, hj⟩ := final_entered hpre hX j hk hσ hs
  exact Epilogue.final_ctl hpre hX hg hE hj hσ hs he hv

/-- `StoreCtl.elem` for the whole execution, from what the Store phase owes. -/
theorem storeCtl_elem (SO : StoreOwes P L X) {k : Nat} {d : D} {e : Event} (i : Fin 8)
    (hσ : At (code L) X g k d) (hs : d.site = .store ⟨10 + i.val, by omega⟩)
    (he : X.get (g, k) = some e) :
    (∃ k0 d0, k = k0 + 4 + i.val ∧ Frame.stateAt (code L) X g k0 = some (some d0) ∧
      d0.site = .load 177) ∧
    ∀ v', storeValue 16 (d.x (elemReg i.val)) = .ok v' →
      ∃ a, e = ⟨d.site.pc, .wr a v'.toBytes⟩ := by
  have hlt : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  obtain ⟨h1, h2⟩ := elem_range i hs
  obtain ⟨hg, k0, hen, hj, hI, -⟩ := store_entered hpre hX (Nat.le_of_lt hlt) hσ h1 h2
  exact SO.elem g k0 k d e i hg hen hj hσ (hI (noUb_of_lt hX hlt)) hs he

/-! ### The thread layer and the reads before the tile loop -/

/-- **The thread layer's contract** `Values.Followed`: the launch has thread blocks of whole
warps, the execution is consistent, every thread's machine is sound (`Thread.sound`) and no
machine gives up (`tracked`, `Tracked.lean`). -/
theorem followed : Followed L mem0 X :=
  ⟨by rw [hpre.block], hX, sounds hpre, tracked hpre hX⟩

/-- **What a read of the FP32 buffer returns before the tile loop** (`Values.Ends.EarlyRead`):
the bytes that the sixteen tensor loads of the initial state wrote. From the protocol
contracts and the content of those loads (`Ref/Source/Fit.lean: earlyRead_init`). The
hypotheses `StateIssues` and `WriteFrame` of the sources are discharged by the assembly of the
direct facts. -/
theorem earlyRead {O : Owners} (F : Facts P L X) (U : UnionFacts L X (ctaTiles P) O)
    (hSI : Source.StateIssues P L X) (hW : Source.WriteFrame P X) : EarlyRead P L X :=
  Source.earlyRead_init hpre hX hSI hW U F.life F.load F.store F.state F.init F.bars
    (noEvents hX) (F.syncGuarded hpre hX)

end

end ValuesEnds

open ValuesEnds

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
include hpre hX

/-! ### A. The conversion loop -/

/-- **`ConvRef` for the whole execution**: a conversion load reads the four bytes of an
element of the FP32 buffer, with three `bar.sync 0` before it, and the write that follows it is
the two bytes of the same element of the bfloat16 copy; a write with three `bar.sync 0` before
it is the event after a conversion load. -/
theorem convRef : ConvRef L X where
  load := by
    intro g k d e j hσ hs he
    have hg := Frame.lt_of_get hX he
    obtain ⟨h1, h2⟩ := conv_load_range j hs
    obtain ⟨j0, s0, -, -, hI⟩ := (stage_event hpre hX hg he hσ).1.of_pc_conversion h1 h2
    exact Conversion.conv_load hpre hX hg j he hσ hI hs
  store := by
    intro g k pc a bs he hbar
    have hg := Frame.lt_of_get hX he
    obtain ⟨s, j0, s0, hσ, past, -, hI⟩ := conv_of_wr3 hpre hX he hbar
    exact (Conversion.conv_store hpre hX hg past.state past.conversion_in hσ hI he).2

/-! ### B. The carry loads -/

/-- **`CarryRef` for the whole execution**: the `j`-th carry load of a compute thread reads
the four bytes at the swizzled address of the thread's base pointer plus the `j`-th constant,
with five `bar.sync 0` before it; a compute thread at the `j`-th carry site was at the first
one `j` positions earlier. -/
theorem carryRef : CarryRef L X where
  load := by
    intro g k d e j hc hσ hs he
    have hg := Frame.lt_of_get hX he
    obtain ⟨h1, h2⟩ := carry_range (Nat.le_of_lt j.isLt) hs
    obtain ⟨j0, s0, -, -, hI⟩ := (stage_event hpre hX hg he hσ).1.of_pc_carryLoad h1 h2
    exact CarryLoad.carry_load hpre hX hg j hσ hI hs he
  first := by
    intro g k d j hc hj hk hσ hs
    obtain ⟨h1, h2⟩ := carry_range hj hs
    have hg := lt_threads_of_pc hpre hX hσ (by omega)
    obtain ⟨j0, s0, past, -, hI⟩ := (stage hpre hX hg hk hσ).of_pc_carryLoad h1 h2
    exact CarryLoad.carry_first (by rw [← block_mod hpre]; exact hc) hj past.state
      past.carryLoad_in hI hs

/-! ### C. The final stores -/

/-- **`FinalRef` for the whole execution**: a write with seven `bar.sync 0` before it is a
final store of a compute thread; the `j`-th final store writes the four bytes at the address of
the `j`-th carry; the final stores are consecutive events. -/
theorem finalRef : FinalRef L X where
  site := by
    intro g k pc a bs he hbar
    have hg := Frame.lt_of_get hX he
    obtain ⟨s, hσ, hst, -, hpc, b1, b2, b3, b4, -⟩ := wr_stage hpre hX he
    have h3113 : 3113 < s.site.pc := by
      by_contra hc
      rcases Nat.lt_or_ge 1402 s.site.pc with h | h
      · have := b4 h (by omega)
        omega
      · rcases Nat.lt_or_ge 621 s.site.pc with h' | h'
        · have := b3 h' h
          omega
        · rcases Nat.lt_or_ge s.site.pc 621 with h'' | h''
          · have := b1 (by omega)
            omega
          · have := b2 (by omega)
            omega
    obtain ⟨j0, s0, past, hj, -, -⟩ := hst.of_pc_epilogue (by omega) (.inr h3113)
    exact (Epilogue.final_site hpre hX hg ⟨s0, past.state, past.into⟩ hj he).2
  store := by
    intro g k d pc a bs j _ hσ hs he
    have hk : k ≤ (X.tr g).length := Nat.le_of_lt (List.getElem?_eq_some_iff.mp he).1
    obtain ⟨hg, k0, hE, hj⟩ := final_entered hpre hX j hk hσ hs
    exact Epilogue.final_store hpre hX hg hE hj hσ hs he
  first := by
    intro g k d j hk hσ hs
    obtain ⟨hg, k0, hE, hj⟩ := final_entered hpre hX j hk hσ hs
    exact Epilogue.final_first hpre hX hg hE hj hk hσ hs

/-! ### D. The store path of a partial last tile -/

/-- **`StoreRef` for the whole execution**, from what the Store phase owes (`StoreOwes`, proved
in `Ref/Store/ValuesOwes.lean`, which imports this file; `ValuesEnds.lean: storeRef` is the
statement without it) and one fact of the Compute phase (`ComputeOwes.wr_shared`): a write to
global memory is the
`(4 + i)`-th event after a state at the vector load (the writes of the conversion loop, of the
tile loop of the compute threads and of the epilogue are to shared memory); and the twelve
events of a chunk at the vector load. -/
theorem ValuesEnds.storeRef_of (SO : StoreOwes P L X) (CO : ComputeOwes P L X) :
    StoreRef P L X where
  elem := by
    intro g k pc a bs he hglob
    have hg := Frame.lt_of_get hX he
    have hlt : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
    obtain ⟨s, hσ, hst, hub, -⟩ := wr_stage hpre hX he
    rcases wr_cases hpre hX he hσ with ⟨j, hs⟩ | ⟨j, row, hs⟩ | ⟨i, hs⟩ | ⟨j, hs⟩
    · -- a conversion store writes the bfloat16 copy, in shared memory
      exfalso
      obtain ⟨h1, h2⟩ := conv_store_range j hs
      obtain ⟨j0, s0, -, -, hI⟩ := hst.of_pc_conversion h1 h2
      obtain ⟨pos, -, -, -, hev⟩ := Conversion.event_at hpre hX hg he hσ hI
      obtain ⟨j', u, -, rfl⟩ := hev.wr
      cases hglob
    · -- the row write of an `stmatrix`
      exfalso
      have h := stWr_site_pc j row
      rw [← hs] at h
      obtain ⟨-, j0, s0, -, -, -, hI⟩ := hst.of_pc_compute h.1 h.2
      rw [CO.wr_shared g j0 k s pc a bs hg hσ hI he] at hglob
      cases hglob
    · obtain ⟨h1, h2⟩ := elem_range i hs
      obtain ⟨-, k0, hen, hj, hI, -⟩ := store_entered hpre hX (Nat.le_of_lt hlt) hσ h1 h2
      obtain ⟨⟨k1, d0, e1, e2, e3⟩, -⟩ := SO.elem g k0 k s _ i hg hen hj hσ (hI hub) hs he
      exact ⟨k1, d0, i, e1, e2, e3⟩
    · -- a final store writes the FP32 buffer, in shared memory
      exfalso
      obtain ⟨-, k0, hE, hj⟩ := final_entered hpre hX j (Nat.le_of_lt hlt) hσ hs
      obtain ⟨-, hloc⟩ := Epilogue.final_store hpre hX hg hE hj hσ hs he
      rw [hloc] at hglob
      cases hglob
  chunk := by
    intro g k d hσ hs
    have hpc := load177_pc
    rw [← hs] at hpc
    rcases Nat.le_total k (X.tr g).length with hk | hk
    · obtain ⟨hg, k0, hen, hj, hI, hW⟩ := store_entered hpre hX hk hσ hpc.1 hpc.2
      exact SO.chunk g k0 k d hg hen hj hk hσ hW hI hs
    · -- a position beyond the trace has the state after the last event, and no event
      have hσ' : At (code L) X g (X.tr g).length d := by
        rw [At, ← Frame.stateAt_of_le hk]
        exact hσ
      obtain ⟨hg, k0, hen, hj, hI, hW⟩ := store_entered hpre hX le_rfl hσ' hpc.1 hpc.2
      obtain ⟨hl, t, row, c, h1, h2, h3, -, -⟩ :=
        SO.chunk g k0 _ d hg hen hj le_rfl hσ' hW hI hs
      refine ⟨hl, t, row, c, h1, h2, h3, fun m _ pc a bs he => ?_, fun i pc a bs he => ?_⟩
      · have h : k + m < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
        omega
      · have h : k + 4 + i.val < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
        omega

/-- **`StoreCtl` for the whole execution**: the control half of the three families of stores
of data registers ("if the source converts to the store's width, the event is the write of its
bytes"), and where a conversion store and an element store come from. The field for the
element stores is what the Store phase owes (`ValuesEnds.lean: storeCtl` is the statement
without that hypothesis). -/
theorem ValuesEnds.storeCtl_of (SO : StoreOwes P L X) : StoreCtl L X where
  conv := fun _ _ _ _ j hσ hs he => storeCtl_conv hpre hX j hσ hs he
  final := fun _ _ _ _ j _ hσ hs he _ hv => storeCtl_final hpre hX j hσ hs he hv
  elem := fun _ _ _ _ i hσ hs he => storeCtl_elem hpre hX SO i hσ hs he

end

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Assembly
