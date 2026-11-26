-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Store.Family
public import Kernels.FlashKdaFwd.Proof.Ref.TensorStore
public import Kernels.FlashKdaFwd.Proof.Ref.ParamBridge
public import Kernels.FlashKdaFwd.Flow.Code
public import Lemmas.Flow.TcTmpl
public import Lemmas.Flow.Step.ShapeClasses

@[expose] public section

/-! # Store phase: the events, in closed form

What a thread of the store warp fires at each position of the phase, from the reference
invariant at the position (`RefAt`), the concrete state (`Code.AtD`: the registers hold the
values of the machine's file) and the firing fact of the site's instruction (`Fires`). These
three are what `Frame.fired_site` gives for an event at a followed state.

* `Ev P g pos e`: **the closed-form event of a position**; no alternative of it is an
  undefined-behaviour event.

  | position | instruction | event |
  |---|---|---|
  | `entry` | 1402 `bar.sync 0` | `.bar 0 none .sync` |
  | `wait t` | 2987 `mbarrier.try_wait.parity` | a poll of `fullBar P g (t % 2)` |
  | `ts t i` | `3052 + 2 i` tensor store | the issue of `tileSpec P g t i` through object 10 |
  | `commit t` | 3083 | `.bulkCommit` |
  | `ld0` to `ld3` | 3020 `ld.shared.v4.b32` | the read of element `m` of the chunk (`rdAcc`) |
  | `gst t row c j` | `3025 + j` `st.global.b16` | a write of the two bytes at `wrAcc` |
  | `bwait t` | 3093 | `.bulkWait .read 0` |
  | `arrive t` | 3101 `mbarrier.arrive` | one release arrival on `emptyBar P g (t % 2)` |

* `EvX P g pos x e`: **the exact event** for a state with the opaque slots `x`. It is `Ev`
  at every position but a global store, and none of those events has a data operand: the
  barrier, the poll, the tensor store (`Ref/TensorStore.lean: tensorStore_event`: the map is the
  launch's output map, the source address a multiple of 128, the box aligned and inside the
  tensor), the commit, the four element reads (the address is a multiple of 16 inside the
  thread's own window), the group wait and the arrival (the pointer that `mapa` returned names
  an mbarrier of the thread's own block) are never undefined behaviour. At global store `j` it
  says what is written: with `v = x (gstSrc j)` the value of the 16-bit source register, the
  event is the write of the two bytes of `storeValue 16 v` at `wrAcc`, or the
  undefined-behaviour event with the fault of `storeValue 16 v` when the value cannot be stored
  in 16 bits. This is the only data condition on an event of the phase; the value layer
  discharges it (the source registers hold bfloat16 payloads).
* `ev_at`: **the exact event at every position**, with no premise "the event is not undefined
  behaviour".
* `EvX.ev`, `Ev.noUb`, `EvX.noUb`: an exact event that is not undefined behaviour is the
  closed-form event; a closed-form event is not undefined behaviour; an exact event is not
  undefined behaviour when the stored value is storable.
* `ledEv_ev`: **the ledger of a closed-form event** is what its position counts (`evDelta`).

The address of a global store: the register `%rd1168` holds the address of feature `8 c + 4` of
the output row of token `16 t + row` (`Row`), and store `j` has the displacement `2 j - 8`, so
it writes feature `8 c + j`: the two bytes of `P.outLoc seq head (16 t + row) ⟨8 c + j, _⟩`
(`wrAcc_loc`). -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Store
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! ### The closed forms -/

/-- **The tensor store of block `i` of 8 features of the full tile `t`** by a thread `g`:
through the map of parameter object 10 (`tma_store_out`) at the coordinates (feature `8 i`,
token `16 t` of the sequence, head), from byte `86912 + 4096 (t % 2) + 256 i` of the shared
window of the thread's block (the `i`-th 256-byte box of output stage `t % 2`). -/
def tileSpec (P : Params) (g t i : Nat) : TensorStore.Spec :=
  storeSpec P (cta g) 10 [8 * i, 16 * t + firstToken P.length (seqOf P g), headOf P g]
    (P.sharedBase + 4096 * (t % 2) + 86912 + 256 * i)

/-- **The footprint of element `m` of the vector load of a chunk**: the four bytes at offset
`4 m` of the 16 bytes of row `row`, features `8 c` to `8 c + 7`, of output stage `t % 2` in the
shared window of the thread's block. -/
def rdAcc (P : Params) (g t row c m : Nat) : Acc :=
  { loc := ⟨.shared, cta g, P.sharedBase + 4096 * (t % 2) + 16 * row + 86912 + 256 * c + 4 * m⟩,
    size := 4, elem := m }

/-- **The footprint of global store `j` of a chunk**: the two bytes of feature `8 c + j` of the
output row of token `16 t + row` of the thread's sequence and head. -/
def wrAcc (P : Params) (g t row c j : Nat) : Acc :=
  { loc := ⟨.global, 0, P.outputBase + 256 * ((firstToken P.length (seqOf P g) + (16 * t + row)) *
      P.heads + headOf P g) + 2 * (8 * c + j)⟩, size := 2, elem := 0 }

/-- The 16-bit source register of global store `j` (`%rs23`, `%rs24`, `%rs21`, `%rs22`,
`%rs19`, `%rs20`, `%rs17`, `%rs18`): store `j` writes half `j % 2` of element `j / 2` of the
vector load. -/
def gstSrc (j : Nat) : Nat := [112, 113, 110, 111, 108, 109, 106, 107].getD j 0

/-- The footprint of a global store is the output location of its token and feature. -/
theorem wrAcc_loc (P : Params) (g t row : Nat) {c j : Nat} (hc : c < 16) (hj : j < 8) :
    (wrAcc P g t row c j).loc =
      P.outLoc (seqOf P g) (headOf P g) (16 * t + row) ⟨8 * c + j, by omega⟩ := rfl

/-- **The event of a position**, in closed form. -/
def Ev (P : Params) (g : Nat) : Pos → Event → Prop
  | .entry, e => e = ⟨1402, .bar 0 none .sync⟩
  | .wait t, e => ∃ ok, e = ⟨2987, .wait (fullBar P g (t % 2)) (t / 2 % 2) ok true .cta⟩
  | .ts t i, e =>
    e = ⟨(Pos.ts t i).site.pc, .tensorStore (P.objectBase 10) (tileSpec P g t i.val)⟩
  | .commit _, e => e = ⟨3083, .bulkCommit⟩
  | .ld0 t row c, e => ∃ bs, bs.length = 4 ∧ e = ⟨3020, .rd (rdAcc P g t row c 0) bs⟩
  | .ld1 t row c _, e => ∃ bs, bs.length = 4 ∧ e = ⟨3020, .rd (rdAcc P g t row c 1) bs⟩
  | .ld2 t row c _ _, e => ∃ bs, bs.length = 4 ∧ e = ⟨3020, .rd (rdAcc P g t row c 2) bs⟩
  | .ld3 t row c _ _ _, e => ∃ bs, bs.length = 4 ∧ e = ⟨3020, .rd (rdAcc P g t row c 3) bs⟩
  | .gst t row c j, e => ∃ bs, e = ⟨3025 + j.val, .wr (wrAcc P g t row c j.val) bs⟩
  | .bwait _, e => e = ⟨3093, .bulkWait .read 0⟩
  | .arrive t, e => e = ⟨3101, .arrive (emptyBar P g (t % 2)) 0 1 true .cta⟩

/-- **The exact event of a position**, given the opaque slots of the state: at a global store
the write of the stored form of the source register, or the undefined behaviour of a source
that cannot be stored in 16 bits; the closed-form event everywhere else. -/
def EvX (P : Params) (g : Nat) (pos : Pos) (x : Nat → Value) (e : Event) : Prop :=
  match pos with
  | .gst t row c j =>
    (∃ v, storeValue 16 (x (gstSrc j.val)) = .ok v ∧
      e = ⟨3025 + j.val, .wr (wrAcc P g t row c j.val) v.toBytes⟩) ∨
    ∃ f, storeValue 16 (x (gstSrc j.val)) = .error f ∧ e = ⟨3025 + j.val, .ub f⟩
  | pos => Ev P g pos e

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {site : Site}
  {w : Nat → BitVec 64} {p : Nat → Bool} {x : Nat → Value}
  {t : TState} {ins : Instr} {e : Event} {o : Option TState}

/-- An exact event that is not undefined behaviour is the closed-form event. -/
theorem EvX.ev {pos : Pos} (h : EvX P g pos x e) (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩) :
    Ev P g pos e := by
  cases pos with
  | gst t row c j =>
    rcases h with ⟨v, -, rfl⟩ | ⟨f, -, rfl⟩
    · exact ⟨_, rfl⟩
    · exact absurd rfl (hub _ f)
  | _ => exact h

/-- **No closed-form event of the phase is undefined behaviour.** -/
theorem Ev.noUb {pos : Pos} (h : Ev P g pos e) : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
  rintro pc f rfl
  cases pos <;>
    simp only [Ev, Event.mk.injEq, reduceCtorEq, and_false, exists_false, exists_const,
      false_and] at h

/-- **The event of a position is not undefined behaviour** when, at a global store, the source
register holds a value that a 16-bit store can write. -/
theorem EvX.noUb {pos : Pos} (h : EvX P g pos x e)
    (hv : ∀ t row c j, pos = .gst t row c j → ∃ v, storeValue 16 (x (gstSrc j.val)) = .ok v) :
    ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
  cases pos with
  | gst t row c j =>
    obtain ⟨v, hv⟩ := hv t row c j rfl
    rcases h with ⟨v', -, rfl⟩ | ⟨f, hf, -⟩
    · intro pc f h'
      cases h'
    · rw [hv] at hf
      cases hf
  | _ =>
    simp only [EvX] at h
    exact Ev.noUb h

/-! ### The mbarriers -/

/-- No assumption of the kernel widens the scope of an mbarrier instruction. -/
theorem noWiden (pc : Nat) : Assumptions.all.any (·.clusterScopeMbar pc) = false := rfl

/-- The parity a poll reads from a register that holds 0 or 1. -/
theorem par_toNat {n : Nat} (h : n < 2) : (W n).toNat % 2 = n := by
  rw [toNat_W (by omega)]
  omega

/-- **A poll** whose address register holds the "store full" mbarrier of stage `tt % 2` and
whose parity register holds `tt / 2 % 2`. -/
theorem ev_poll (hpre : Pre P L mem0) {pc pr r q tt : Nat}
    (hf : Fires pc (eventTmpl Assumptions.all L g t (.mbarWait pr r 0 (.reg q) true .cta)) e o)
    (hr : t.regs r = some (.bits 32 (W (P.sharedBase + 8 * (tt % 2) + 98352))))
    (hq : t.regs q = some (.bits 32 (W (tt / 2 % 2)))) :
    ∃ ok, e = ⟨pc, .wait (fullBar P g (tt % 2)) (tt / 2 % 2) ok true .cta⟩ := by
  have hs := shared_lt hpre
  have ha := hpre.sharedAlignment
  have h2 : tt % 2 < 2 := Nat.mod_lt _ (by decide)
  have h3 : tt / 2 % 2 < 2 := Nat.mod_lt _ (by decide)
  have hm := mbarLoc_b32 (L := L) (g := g) hr (by omega) (by omega)
  have hl : (⟨.shared, g / L.block, P.sharedBase + 8 * (tt % 2) + 98352⟩ : Loc) =
      fullBar P g (tt % 2) := by
    simp only [fullBar, block_div hpre, Loc.mk.injEq, true_and]
    omega
  rw [hl] at hm
  exact shape_wait (P := fun e' => ∃ ok, e' =
      ⟨pc, .wait (fullBar P g (tt % 2)) (tt / 2 % 2) ok true .cta⟩) hf (noWiden _)
    (readBits_b32 hq (by omega)) hm (fun ok => ⟨ok, by rw [par_toNat h3]⟩)

/-- An arrival through a `shared::cluster` address (the form of instruction 3101), at a site
where no assumption widens its scope: the object the address names, with the instruction's byte
count, arrival count, release flag and scope. -/
theorem fires_arrive_cluster {base pc : Nat} {off : Int} {tx count : Opnd} {rel : Bool}
    {sc : MbarScope} {st : Option Nat} {m : Loc} {b n : BitVec 64}
    (hm : mbarClusterLoc L g t base off = .ok m) (hb : readBits L g t 32 tx = .ok b)
    (hn : readBits L g t 32 count = .ok n)
    (hf : Fires pc (eventTmpl Assumptions.all L g t
      (.mbarArrive base off tx count true rel sc st)) e o) :
    e = ⟨pc, .arrive m b.toNat n.toNat rel sc⟩ := by
  simp only [eventTmpl, widenMbarScope, noWiden, Bool.false_eq_true, ↓reduceIte, tmaTmpl, hm, hb,
    hn, bind, Except.bind, pure, Except.pure, ofExec] at hf
  simp only [Fires] at hf
  exact hf.1

/-- An opaque register that is live at a state's site holds the file's slot. -/
theorem reg_x {d : D} (hat : (code L g).AtD d t) {r : Nat} (hr : r ∈ Flow.live d.site.pc)
    (hk : isOpaque r = true) : t.regs r = some (d.x r) := by
  have h := regs_of_factsFrom hat.2.2.2.2 hr
  rw [h, valueOf_opaque hk]

/-- **The arrival** through the pointer that `mapa` returned for the "store empty" mbarrier of
stage `tt % 2`. -/
theorem ev_arrive (hpre : Pre P L mem0) (hg : g < L.threads) {pc r tt : Nat}
    (hf : Fires pc (eventTmpl Assumptions.all L g t
      (.mbarArrive r 0 (.imm 0) (.imm 1) true true .cta none)) e o)
    (hr : t.regs r = some (.ptr 32 false (.shared (cta g) (cta g))
      (W (P.sharedBase + 8 * (tt % 2) + 98368)))) :
    e = ⟨pc, .arrive (emptyBar P g (tt % 2)) 0 1 true .cta⟩ := by
  have hs := shared_lt hpre
  have ha := hpre.sharedAlignment
  have h2 : tt % 2 < 2 := Nat.mod_lt _ (by decide)
  have hcta : g / L.block < L.grid := by
    rw [block_div hpre, hpre.grid]
    exact cta_lt hpre hg
  rw [← block_div hpre (L := L) (g := g)] at hr
  have hm := mbarClusterLoc_ptr (L := L) (g := g) (t := t) (base := r) (cta := g / L.block)
    (a := P.sharedBase + 8 * (tt % 2) + 98368) hr hg hcta rfl (by omega) (by omega)
  have hl : (⟨.shared, g / L.block, P.sharedBase + 8 * (tt % 2) + 98368⟩ : Loc) =
      emptyBar P g (tt % 2) := by
    simp only [emptyBar, block_div hpre, Loc.mk.injEq, true_and]
    omega
  rw [hl] at hm
  exact fires_arrive_cluster (b := truncBits 32 (BitVec.ofInt 64 0))
    (n := truncBits 32 (BitVec.ofInt 64 1)) hm rfl rfl hf

/-! ### A tensor store of a full tile -/

/-- **The event of tensor store `i` of tile `tt`**, from its registers: `src` holds the shared
source address, `rc` the feature coordinate, `%r777` (1083) the token and `%r780` (1086) the
head; the map register `%rd636` (2882) has the static kind "generic address of parameter object
10". It is the issue of `tileSpec`, never undefined behaviour. -/
theorem ev_ts (hpre : Pre P L mem0) (hg : g < L.threads) {i tt pc src rc : Nat} (hi : i < 16)
    (hfull : 16 * tt + 16 ≤ P.length (seqOf P g))
    (hf : Fires pc (eventTmpl Assumptions.all L g t
      (.cpTensorStore (.reg 2882) [.reg rc, .reg 1083, .reg 1086] src 0 none .tile none)) e o)
    (hat : (code L g).AtD ⟨site, w, p, x⟩ t) (h2882 : 2882 ∈ Flow.live site.pc)
    (hsrc : t.regs src = some (.bits 32 (W (P.sharedBase + 4096 * (tt % 2) + 86912 + 256 * i))))
    (hc0 : t.regs rc = some (.bits 32 (W (8 * i))))
    (hc1 : t.regs 1083 = some (.bits 32 (W (16 * tt + firstToken P.length (seqOf P g)))))
    (hc2 : t.regs 1086 = some (.bits 32 (W (headOf P g)))) :
    e = ⟨pc, .tensorStore (P.objectBase 10) (tileSpec P g tt i)⟩ := by
  have hs := shared_lt hpre
  have ha := hpre.sharedAlignment
  have h2 : tt % 2 < 2 := Nat.mod_lt _ (by decide)
  have h1 := tok_le hpre g
  have h3 := Startup.total_lt hpre
  have hh := headOf_lt hpre hg
  have hH := hpre.headsLt
  have hrm := reg_g hat (r := 2882) h2882 (i := 10) rfl
  rw [tileSpec, ← block_div hpre (L := L) (g := g)]
  exact (tensorStore_event hpre (i := 10) Thread.paramName_10 (rs := [rc, 1083, 1086])
    (vs := [8 * i, 16 * tt + firstToken P.length (seqOf P g), headOf P g]) hf hrm hsrc
    (by omega) (by omega)
    (.cons ⟨hc0, by omega⟩ (.cons ⟨hc1, by omega⟩ (.cons ⟨hc2, by omega⟩ .nil))) rfl
    (show 8 * i * 2 % 16 = 0 by omega)).1

/-! ### The vector load and the global stores of a chunk -/

/-- **An element of the vector load of a chunk**: sub-step `m` of `ld.shared.v4.b32` through
the 32-bit register `r` that holds the chunk's address reads the four bytes of `rdAcc`; the
address is a multiple of 16, so the load is not undefined behaviour. -/
theorem ev_rd (hpre : Pre P L mem0) {pc r tt row c m : Nat} {ds : List Nat}
    (hf : Fires pc (loadTmpl Assumptions.all L g t .shared false 32 ds r 0) e o)
    (hr : t.regs r = some (.bits 32
      (W (P.sharedBase + 4096 * (tt % 2) + 16 * row + 86912 + 256 * c))))
    (hrow : row < 16) (hc : c < 16) (hs : t.sub = m) (hds : ds.length = 4) :
    ∃ bs, bs.length = 4 ∧ e = ⟨pc, .rd (rdAcc P g tt row c m) bs⟩ := by
  have hsh := shared_lt hpre
  have ha := hpre.sharedAlignment
  have h2 : tt % 2 < 2 := Nat.mod_lt _ (by decide)
  refine shape_ldM (P := fun e' => ∃ bs, bs.length = 4 ∧
      e' = ⟨pc, .rd (rdAcc P g tt row c m) bs⟩) hf (effAddr_b32 hr (by omega)) hs
    (fun bs hbs => ⟨bs, hbs, ?_⟩) (fun hm => ?_)
  · simp only [rdAcc, Loc.at, block_div hpre, Nat.reduceDiv]
  · exfalso
    simp only [hds, Nat.reduceDiv, Nat.reduceMul] at hm
    omega

/-- **A global store of a chunk**: `st.global.b16` through the 64-bit register `r` that holds
the address of feature `8 c + 4` of the output row, with the displacement `2 j - 8`, of the
value `v` of its source register: the write of the two bytes of the value as a 16-bit store
writes it, or undefined behaviour when the value cannot be stored in 16 bits. The address is
even, so the store is not undefined behaviour because of its address. -/
theorem ev_gst (hpre : Pre P L mem0) (hg : g < L.threads) {pc r src tt row c j : Nat}
    {off : Int} {v : Value}
    (hf : Fires pc (storeTmpl L g t .global 16 r off [.reg src]) e o)
    (hr : t.regs r = some (.bits 64 (W (P.outputBase + 256 *
      ((firstToken P.length (seqOf P g) + (16 * tt + row)) * P.heads + headOf P g) +
      16 * c + 8))))
    (hv : t.regs src = some v) (hrow : 16 * tt + row < P.length (seqOf P g)) (hc : c < 16)
    (hj : j < 8) (hoff : off = (2 * j : Nat) - 8) (hs : t.sub = 0) :
    (∃ v', storeValue 16 v = .ok v' ∧ e = ⟨pc, .wr (wrAcc P g tt row c j) v'.toBytes⟩) ∨
    ∃ f, storeValue 16 v = .error f ∧ e = ⟨pc, .ub f⟩ := by
  have h1 := tok_le hpre g
  have ho := out_le hpre (tok := firstToken P.length (seqOf P g) + (16 * tt + row))
    (h := headOf P g) (by omega) (headOf_lt hpre hg)
  have hal := hpre.outputAlign
  subst hoff
  have hl : (truncBits 64 (W (P.outputBase + 256 *
      ((firstToken P.length (seqOf P g) + (16 * tt + row)) * P.heads + headOf P g) +
      16 * c + 8)) + BitVec.ofInt 64 ((2 * j : Nat) - 8)).toNat =
      P.outputBase + 256 * ((firstToken P.length (seqOf P g) + (16 * tt + row)) * P.heads +
        headOf P g) + 2 * (8 * c + j) := by
    simp only [truncBits, W, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
    omega
  have hrv : readValue L g t 16 (.reg src) = .ok v := by
    simp [readValue, readReg, hv, pure, Except.pure]
  refine shape_stM (P := fun e' => (∃ v', storeValue 16 v = .ok v' ∧
      e' = ⟨pc, .wr (wrAcc P g tt row c j) v'.toBytes⟩) ∨
      ∃ f, storeValue 16 v = .error f ∧ e' = ⟨pc, .ub f⟩) hf (effAddr_global_bits hr) hs rfl hrv
    (fun v' hv' => .inl ⟨v', hv', ?_⟩) (fun hm => ?_) (fun f hf' => .inr ⟨f, hf', rfl⟩)
  · simp only [wrAcc, Loc.at, hl, Nat.reduceDiv, Nat.mul_zero, Nat.add_zero]
  · exfalso
    simp only [hl, List.length_singleton, Nat.reduceDiv, Nat.mul_one] at hm
    omega

/-! ### The event at every position -/

/-- `ts_ev i src rc`: the event of tensor store `i` of the current case, whose source register is
`src` and whose feature-coordinate register is `rc`. -/
syntax "ts_ev " num num num : tactic
set_option hygiene false in
macro_rules
  | `(tactic| ts_ev $i $src $rc) => `(tactic| (
      have r1 := reg_w hat (r := $src) (by lit_mem) (n := 32) rfl
      have r2 := reg_w hat (r := $rc) (by lit_mem) (n := 32) rfl
      have r3 := reg_w hat (r := 1083) (by lit_mem) (n := 32) rfl
      have r4 := reg_w hat (r := 1086) (by lit_mem) (n := 32) rfl
      dsimp only at r1 r2 r3 r4
      rw [hsrc] at r1
      rw [hco] at r2
      rw [h1083] at r3
      rw [h1086] at r4
      exact ev_ts hpre hg (i := $i) (by decide) hfull hf hat (by lit_mem) r1 r2 r3 r4))

/-- `gst_ev j src`: the event of global store `j` of the current case, whose source register is
`src`. -/
syntax "gst_ev " num num : tactic
set_option hygiene false in
macro_rules
  | `(tactic| gst_ev $j $src) => `(tactic| (
      have r1 := reg_w hat (r := 3414) (by lit_mem) (n := 64) rfl
      have r2 := reg_x hat (r := $src) (by lit_mem) rfl
      dsimp only at r1 r2
      rw [k3414] at r1
      tmpl_unfold hf PTX.storeTmpl
      dsimp only [PTX.DType.width] at hf
      exact ev_gst hpre hg (j := $j) hf r1 r2 (by omega) hc' (by decide) (by decide) hat.2.1))

/-- **The exact event at a position**: from the invariant at the position, the concrete state
and the firing fact of the site's instruction. There is no premise "the event is not undefined
behaviour". -/
theorem ev_at (hpre : Pre P L mem0) (hg : g < L.threads) (pos : Pos)
    (h : RefAt P g pos ⟨pos.site, w, p, x⟩)
    (hat : (code L g).AtD ⟨pos.site, w, p, x⟩ t) (hc : kernel.code[pos.site.pc]? = some ins)
    (hf : Fires pos.site.pc (eventTmpl Assumptions.all L g t ins.op) e o) :
    EvX P g pos x e := by
  obtain ⟨-, hk, h⟩ := h
  cases pos with
  | entry =>
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    exact shape_barSync (P := fun e => e = ⟨_, .bar 0 none .sync⟩) hf (by decide) rfl
  | wait tt =>
    simp only [AtPos, Tile, Mult] at h
    obtain ⟨⟨-, -, -, -, -, k2113, -, -⟩, k1074, -⟩ := h
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    have r1 := reg_w hat (r := 1074) (by lit_mem) (n := 32) rfl
    have r2 := reg_w hat (r := 2113) (by lit_mem) (n := 32) rfl
    dsimp only at r1 r2
    rw [k1074] at r1
    rw [k2113] at r2
    exact ev_poll hpre hf r1 r2
  | ts tt i =>
    obtain ⟨hT, hfull, h1083, h1086, -, h1082, hsrc⟩ := h
    have hM := hT.2.2.2.2.2.2.2
    simp only [Mult] at hM
    obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15⟩ := hM
    dsimp only at h1083 h1086 h1082 hsrc
    fin_cases i <;> obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup)) <;>
      simp only [finVal, tsSrc, getLit] at hsrc
    · have hco := h1082
      ts_ev 0 1081 1082
    · have hco := m1
      ts_ev 1 1084 1085
    · have hco := m2
      ts_ev 2 1087 1088
    · have hco := m3
      ts_ev 3 1089 1090
    · have hco := m4
      ts_ev 4 1091 1092
    · have hco := m5
      ts_ev 5 1093 1094
    · have hco := m6
      ts_ev 6 1095 1096
    · have hco := m7
      ts_ev 7 1097 1098
    · have hco := m8
      ts_ev 8 1099 1100
    · have hco := m9
      ts_ev 9 1101 1102
    · have hco := m10
      ts_ev 10 1103 1104
    · have hco := m11
      ts_ev 11 1105 1106
    · have hco := m12
      ts_ev 12 1107 1108
    · have hco := m13
      ts_ev 13 1109 1110
    · have hco := m14
      ts_ev 14 1111 1112
    · have hco := m15
      ts_ev 15 1113 1114
  | commit tt =>
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    exact shape_bulkCommit (L := L) (g := g) (P := fun e => e = ⟨_, .bulkCommit⟩) hf rfl
  | ld0 tt row c =>
    simp only [AtPos, Row] at h
    obtain ⟨-, hpart, hrow, hc', -, k2116, -, -⟩ := h
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    have r1 := reg_w hat (r := 2116) (by lit_mem) (n := 32) rfl
    dsimp only at r1
    rw [k2116] at r1
    tmpl_unfold hf PTX.loadTmpl
    dsimp only [PTX.DType.width] at hf
    exact ev_rd hpre hf r1 (by omega) hc' hat.2.1 rfl
  | ld1 tt row c v0 =>
    simp only [AtPos, Row] at h
    obtain ⟨-, hpart, hrow, hc', -, k2116, -, -⟩ := h
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    have r1 := reg_w hat (r := 2116) (by lit_mem) (n := 32) rfl
    dsimp only at r1
    rw [k2116] at r1
    tmpl_unfold hf PTX.loadTmpl
    dsimp only [PTX.DType.width] at hf
    exact ev_rd hpre hf r1 (by omega) hc' hat.2.1 rfl
  | ld2 tt row c v0 v1 =>
    simp only [AtPos, Row] at h
    obtain ⟨-, hpart, hrow, hc', -, k2116, -, -⟩ := h
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    have r1 := reg_w hat (r := 2116) (by lit_mem) (n := 32) rfl
    dsimp only at r1
    rw [k2116] at r1
    tmpl_unfold hf PTX.loadTmpl
    dsimp only [PTX.DType.width] at hf
    exact ev_rd hpre hf r1 (by omega) hc' hat.2.1 rfl
  | ld3 tt row c v0 v1 v2 =>
    simp only [AtPos, Row] at h
    obtain ⟨-, hpart, hrow, hc', -, k2116, -, -⟩ := h
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    have r1 := reg_w hat (r := 2116) (by lit_mem) (n := 32) rfl
    dsimp only at r1
    rw [k2116] at r1
    tmpl_unfold hf PTX.loadTmpl
    dsimp only [PTX.DType.width] at hf
    exact ev_rd hpre hf r1 (by omega) hc' hat.2.1 rfl
  | gst tt row c j =>
    simp only [AtPos, Row] at h
    obtain ⟨-, hpart, hrow, hc', -, -, -, k3414⟩ := h
    fin_cases j <;> obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    · gst_ev 0 112
    · gst_ev 1 113
    · gst_ev 2 110
    · gst_ev 3 111
    · gst_ev 4 108
    · gst_ev 5 109
    · gst_ev 6 106
    · gst_ev 7 107
  | bwait tt =>
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    exact shape_bulkWait (L := L) (g := g) (P := fun e => e = ⟨_, .bulkWait .read 0⟩) hf rfl
  | arrive tt =>
    simp only [AtPos] at h
    obtain ⟨-, k3436⟩ := h
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    have r1 := reg_x hat (r := 3436) (by lit_mem) rfl
    dsimp only at r1
    rw [k3436] at r1
    exact ev_arrive hpre hg hf r1

/-! ### The ledger of an event -/

/-- **What the event of a position adds to the ledger**: the sixth `bar.sync 0` at the entry, a
successful poll of the stage's "store full" mbarrier, a tensor store, a commit, a global write,
a bulk-group wait, an arrival on the stage's "store empty" mbarrier; a failed poll and an
element read count nothing. -/
def evDelta : Pos → Event → Led
  | .entry, _ => dBar
  | .wait t, e =>
    match e.kind with
    | .wait _ _ true _ _ => dPoll (t % 2)
    | _ => dZero
  | .ts .., _ => dTs
  | .commit _, _ => dCommit
  | .ld0 .., _ => dZero
  | .ld1 .., _ => dZero
  | .ld2 .., _ => dZero
  | .ld3 .., _ => dZero
  | .gst .., _ => dGst
  | .bwait _, _ => dWait
  | .arrive t, _ => dArr (t % 2)

/-- **The ledger of a closed-form event is what its position counts.** The three mbarriers of
the ledger are distinct objects (offsets 98384, 98352 + 8 o and 98368 + 8 o of the window), so
a poll of "store full" of stage `t % 2` counts for that stage only, and likewise an arrival. -/
theorem ledEv_ev {pos : Pos} (h : Ev P g pos e) : ledEv P g e = evDelta pos e := by
  cases pos with
  | entry => rw [show e = _ from h]; rfl
  | wait tt =>
    obtain ⟨ok, rfl⟩ := h
    cases ok
    · rfl
    · rcases Nat.mod_two_eq_zero_or_one tt with h2 | h2 <;>
        simp [ledEv, evDelta, dPoll, okPoll, sourceWaitSuccess, arrivesOn, sourceArrive,
          Execution.isBarId, isTStore, isCommit, isBWait, isGWrite, fullBar, stateBar, h2]
  | ts tt i => rw [show e = _ from h]; rfl
  | commit tt => rw [show e = _ from h]; rfl
  | ld0 tt row c => obtain ⟨bs, -, rfl⟩ := h; rfl
  | ld1 tt row c v0 => obtain ⟨bs, -, rfl⟩ := h; rfl
  | ld2 tt row c v0 v1 => obtain ⟨bs, -, rfl⟩ := h; rfl
  | ld3 tt row c v0 v1 v2 => obtain ⟨bs, -, rfl⟩ := h; rfl
  | gst tt row c j =>
    obtain ⟨bs, rfl⟩ := h
    simp [ledEv, evDelta, dGst, okPoll, sourceWaitSuccess, arrivesOn, sourceArrive,
      Execution.isBarId, isTStore, isCommit, isBWait, isGWrite, wrAcc]
  | bwait tt => rw [show e = _ from h]; rfl
  | arrive tt =>
    rw [show e = _ from h]
    rcases Nat.mod_two_eq_zero_or_one tt with h2 | h2 <;>
      simp [ledEv, evDelta, dArr, okPoll, sourceWaitSuccess, arrivesOn, sourceArrive,
        Execution.isBarId, isTStore, isCommit, isBWait, isGWrite, emptyBar, h2]

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Store
