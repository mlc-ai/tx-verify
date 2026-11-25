-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Store.Walk
public import Kernels.FlashKdaFwd.Proof.Protocol.ResultGlue
public import Kernels.FlashKdaFwd.Proof.Protocol.StoreCover
public import Lemmas.Async.BulkCommitted

@[expose] public section

/-! # Exports of the Store phase: the protocol layer's contracts

The shares of the Store phase (a thread of the store warp between its `bar.sync 0` at
instruction 1402 and the one at 3113) of the contracts of the protocol layer. Every theorem is
about an event of a thread `g` **at a followed state that satisfies the phase invariant**
(`he : X.get (g, k) = some …`, `hσ : Frame.stateAt (code L) X g k = some (some s)`,
`hI : Inv P X g k s`); the assembly supplies `Inv` from the chain of phases and joins the
shares of the phases by the site of the event. Hypotheses besides these: the precondition,
consistency and `g < L.threads`; the theorems that relate two trace positions also take
`Entered P L X g k0` (`Walk.lean`: the entry condition held at `k0`).

**Position level.** `ev_*_inv`: an exact event (`EvX`) of a given kind determines its position
and operands. `fullBar_eq`, `emptyBar_eq`, `stateBar_eq`: the three mbarriers of the ledger are
the protocol layer's `Bar.storeFull`, `Bar.storeEmpty`, `Bar.state` of the thread's block.
`counts_at`: the ledger in the protocol's terms, at a position other than the entry: six
`bar.sync 0`, one successful poll of the state mbarrier, `uses 2 (tile + polled) o` successful
polls of `storeFull o` and `uses 2 tile o` arrivals on `storeEmpty o` (`Pos.polled`: 0 at the
poll, 1 after it).

**Trace level**, by contract field (`Proof/Protocol/`):

| theorem | field |
|---|---|
| `full_poll_store` | `StoreFacts.full_poll`; progress `poll`, `pollStage` |
| `empty_arrive_store` | `StoreFacts.empty_arrive` |
| `no_issue_store` | `StoreFacts.no_tensor`, `LoadFacts.no_tensor_empty` (no tensor load here) |
| `store_wait_store` | `StoreFacts.store_wait` (from `store_covered`) |
| `store_wait_left`, `store_wait_after` | `LifeFacts.store_wait`, `UnionFacts.store_bar_wait` |
| `use_ev_store` | `InitFacts.use_ev`; `SafetyFacts.mbarFrame` |
| `bar_store` | `BarFacts` (the sixth `bar.sync 0`), `UnionFacts.bar_fence` (count 5) |
| `thread_store` | `UnionFacts.thread` (class `leader o`) |
| `store_store` | `UnionFacts.store` (class `tile o`), `StoreCover.store_in` |
| `tile_store` | `StoresIssued.tile` |
| `elem_store` | `StoresIssued.elem` |
| `outIssued_store` | `StoresIssued.outIssued` |

`phaseKind`, `ev_kind`: the nine kinds of events of the phase (a barrier arrival, a poll, a
tensor store, a group commit, a read, a write, a group wait, an mbarrier arrival, undefined
behaviour at a global store). `out_link`: the exit condition gives the entry condition of the
epilogue; `out_counts`: the counts on the mbarriers at the exit, in the protocol's terms.

A full tile is stored by sixteen tensor stores; store `i` copies the 256 bytes at offset
`256 i` of the output buffer (16 rows of 8 features) to the features `8 i` to `8 i + 7` of the
16 tokens of the tile (`tileSpec_writeLoc`, `tileSpec_readLoc`: slot `(x, y, z)` is byte `z` of
feature `8 i + x` of row `y`). A partial tile is stored by element stores (`wrAcc`). -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Store
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Protocol (Bar uses storeLeader bar0Before stageOf blockOf outByte
  outOff InUnion InOutput ThreadClass StoreClass Owners)

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-! ### An exact event of a given kind -/

section
variable {pos : Pos} {x : Nat → Value} {pc : Nat}

/-- A barrier event of the phase is the `bar.sync 0` of the entry. -/
theorem ev_bar_inv {id : Nat} {cnt : Option Nat} {mode : BarMode}
    (h : EvX P g pos x ⟨pc, .bar id cnt mode⟩) :
    pos = .entry ∧ pc = 1402 ∧ id = 0 ∧ cnt = none ∧ mode = .sync := by
  cases pos <;> simp only [EvX, Ev, Event.mk.injEq, Kind.bar.injEq, reduceCtorEq, and_false,
    false_and, exists_false, exists_const, or_false, false_or] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A poll of the phase is the poll of a tile. -/
theorem ev_wait_inv {m : Loc} {q : Nat} {ok acq : Bool} {sc : MbarScope}
    (h : EvX P g pos x ⟨pc, .wait m q ok acq sc⟩) :
    ∃ t, pos = .wait t ∧ pc = 2987 ∧ m = fullBar P g (t % 2) ∧ q = t / 2 % 2 ∧ acq = true ∧
      sc = .cta := by
  cases pos <;> simp only [EvX, Ev, Event.mk.injEq, Kind.wait.injEq, reduceCtorEq, and_false,
    false_and, exists_false, exists_const, or_false, false_or] at h
  rename_i t
  obtain ⟨ok', rfl, rfl, rfl, -, rfl, rfl⟩ := h
  exact ⟨t, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- An arrival of the phase is the arrival of a tile. -/
theorem ev_arrive_inv {m : Loc} {tx cnt : Nat} {rel : Bool} {sc : MbarScope}
    (h : EvX P g pos x ⟨pc, .arrive m tx cnt rel sc⟩) :
    ∃ t, pos = .arrive t ∧ pc = 3101 ∧ m = emptyBar P g (t % 2) ∧ tx = 0 ∧ cnt = 1 ∧
      rel = true ∧ sc = .cta := by
  cases pos <;> simp only [EvX, Ev, Event.mk.injEq, Kind.arrive.injEq, reduceCtorEq, and_false,
    false_and, exists_false, exists_const, or_false, false_or] at h
  rename_i t
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  exact ⟨t, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A tensor store of the phase is one of the sixteen stores of a full tile. -/
theorem ev_ts_inv {al : Nat} {sp : TensorStore.Spec}
    (h : EvX P g pos x ⟨pc, .tensorStore al sp⟩) :
    ∃ t i, pos = .ts t i ∧ al = P.objectBase 10 ∧ sp = tileSpec P g t i.val := by
  cases pos <;> simp only [EvX, Ev, Event.mk.injEq, Kind.tensorStore.injEq, reduceCtorEq,
    and_false, false_and, exists_false, exists_const, or_false, false_or] at h
  rename_i t i
  obtain ⟨-, rfl, rfl⟩ := h
  exact ⟨t, i, rfl, rfl, rfl⟩

/-- A group commit of the phase. -/
theorem ev_commit_inv (h : EvX P g pos x ⟨pc, .bulkCommit⟩) : ∃ t, pos = .commit t := by
  cases pos <;> simp only [EvX, Ev, Event.mk.injEq, reduceCtorEq, and_false,
    false_and, exists_false, exists_const, or_false, false_or] at h
  exact ⟨_, rfl⟩

/-- A group wait of the phase is `wait_group.read 0`. -/
theorem ev_bwait_inv {md : BulkGroup.WaitMode} {n : Nat}
    (h : EvX P g pos x ⟨pc, .bulkWait md n⟩) : ∃ t, pos = .bwait t ∧ md = .read ∧ n = 0 := by
  cases pos <;> simp only [EvX, Ev, Event.mk.injEq, Kind.bulkWait.injEq, reduceCtorEq,
    and_false, false_and, exists_false, exists_const, or_false, false_or] at h
  obtain ⟨-, rfl, rfl⟩ := h
  exact ⟨_, rfl, rfl, rfl⟩

/-- A read of the phase is an element read of the vector load of a chunk. -/
theorem ev_rd_inv {a : Acc} {bs : List (Option Byte)} (h : EvX P g pos x ⟨pc, .rd a bs⟩) :
    ∃ t row c m, m < 4 ∧ InChunk t row c m pos ∧ pc = 3020 ∧ a = rdAcc P g t row c m ∧
      bs.length = 4 := by
  cases pos <;> simp only [EvX, Ev, Event.mk.injEq, Kind.rd.injEq, reduceCtorEq, and_false,
    false_and, exists_false, exists_const, or_false, false_or] at h
  all_goals obtain ⟨bs', hlen, rfl, rfl, rfl⟩ := h
  · exact ⟨_, _, _, 0, by decide, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, hlen⟩
  · exact ⟨_, _, _, 1, by decide, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, hlen⟩
  · exact ⟨_, _, _, 2, by decide, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, hlen⟩
  · exact ⟨_, _, _, 3, by decide, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, hlen⟩

/-- A write of the phase is a global store of a chunk, of the stored form of its source
register. -/
theorem ev_wr_inv {a : Acc} {bs : List Byte} (h : EvX P g pos x ⟨pc, .wr a bs⟩) :
    ∃ t row c j, pos = .gst t row c j ∧ pc = 3025 + j.val ∧ a = wrAcc P g t row c j.val ∧
      ∃ v, storeValue 16 (x (gstSrc j.val)) = .ok v ∧ bs = v.toBytes := by
  cases pos <;> simp only [EvX, Ev, Event.mk.injEq, Kind.wr.injEq, reduceCtorEq, and_false,
    false_and, exists_false, exists_const, or_false, false_or] at h
  rename_i t row c j
  obtain ⟨v, hv, rfl, rfl, rfl⟩ := h
  exact ⟨t, row, c, j, rfl, rfl, rfl, v, hv, rfl⟩

/-- **An undefined-behaviour event of the phase** is at a global store whose source register
does not convert to 16 bits: the only data condition on an event of the phase. -/
theorem ev_ub_inv {f : Fault} (h : EvX P g pos x ⟨pc, .ub f⟩) :
    ∃ t row c j, pos = .gst t row c j ∧ pc = 3025 + j.val ∧
      storeValue 16 (x (gstSrc j.val)) = .error f := by
  cases pos <;> simp only [EvX, Ev, Event.mk.injEq, Kind.ub.injEq, reduceCtorEq, and_false,
    false_and, exists_false, exists_const, or_false, false_or] at h
  rename_i t row c j
  obtain ⟨f', hf, rfl, rfl⟩ := h
  exact ⟨t, row, c, j, rfl, rfl, hf⟩

end

/-- The kinds of the events of the phase. -/
def phaseKind : Kind → Prop
  | .bar .. | .wait .. | .tensorStore .. | .bulkCommit | .rd .. | .wr .. | .bulkWait ..
  | .arrive .. | .ub _ => True
  | _ => False

/-- An exact event of the phase is a barrier arrival, a poll, a tensor store, a group commit,
a read, a write, a group wait, an mbarrier arrival or undefined behaviour. -/
theorem ev_kind {pos : Pos} {x : Nat → Value} {e : Event} (h : EvX P g pos x e) :
    phaseKind e.kind := by
  cases pos with
  | entry => cases h; trivial
  | wait t => obtain ⟨ok, rfl⟩ := h; trivial
  | ts t i => cases h; trivial
  | commit t => cases h; trivial
  | ld0 t row c => obtain ⟨bs, -, rfl⟩ := h; trivial
  | ld1 t row c v0 => obtain ⟨bs, -, rfl⟩ := h; trivial
  | ld2 t row c v0 v1 => obtain ⟨bs, -, rfl⟩ := h; trivial
  | ld3 t row c v0 v1 v2 => obtain ⟨bs, -, rfl⟩ := h; trivial
  | gst t row c j => rcases h with ⟨v, -, rfl⟩ | ⟨f, -, rfl⟩ <;> trivial
  | bwait t => cases h; trivial
  | arrive t => cases h; trivial

/-! ### The mbarriers and the ledger in the protocol layer's terms -/

/-- 0 at the entry and at the poll of a tile, 1 after the poll: whether the tile's poll of its
"store full" mbarrier has succeeded. -/
def Pos.polled : Pos → Nat
  | .entry | .wait _ => 0
  | _ => 1

theorem fullBar_eq (hpre : Pre P L mem0) (g : Nat) (o : Fin 2) :
    fullBar P g o.val = (Bar.storeFull o).loc L (g / L.block) := by
  simp only [fullBar, Bar.loc, Bar.off, hpre.sharedBase, block_div hpre, Nat.add_assoc]

theorem emptyBar_eq (hpre : Pre P L mem0) (g : Nat) (o : Fin 2) :
    emptyBar P g o.val = (Bar.storeEmpty o).loc L (g / L.block) := by
  simp only [emptyBar, Bar.loc, Bar.off, hpre.sharedBase, block_div hpre, Nat.add_assoc]

theorem stateBar_eq (hpre : Pre P L mem0) (g : Nat) :
    stateBar P g = Bar.state.loc L (g / L.block) := by
  simp only [stateBar, Bar.loc, Bar.off, hpre.sharedBase, block_div hpre]

/-- The successful polls of "store full" of the two stages before a position. -/
theorem led_pollF {len : Nat} {pos : Pos} (hp : pos ≠ .entry) :
    (led len pos).pollF0 = (pos.tile + pos.polled + 1) / 2 ∧
      (led len pos).pollF1 = (pos.tile + pos.polled) / 2 := by
  cases pos <;> first
    | exact absurd rfl hp
    | exact ⟨rfl, rfl⟩
    | (simp only [led]; split_ifs <;> exact ⟨rfl, rfl⟩)

/-- **The ledger of a position other than the entry, in the protocol layer's terms**: six
`bar.sync 0`; one successful poll of the state mbarrier; for each output stage `o`, one
successful poll of `storeFull o` per tile of the stage up to the current one (included once its
poll has succeeded) and one arrival on `storeEmpty o` per earlier tile of the stage. -/
theorem counts_at (hpre : Pre P L mem0) {es : List Event} {pos : Pos} (hp : pos ≠ .entry)
    (hl : ledOf P g es = led (P.length (seqOf P g)) pos) :
    es.countP (Execution.isBarId 0) = 6 ∧ okPolls (Bar.state.loc L (g / L.block)) es = 1 ∧
      ∀ o : Fin 2,
        okPolls ((Bar.storeFull o).loc L (g / L.block)) es =
          uses 2 (pos.tile + pos.polled) o.val ∧
        arrivals ((Bar.storeEmpty o).loc L (g / L.block)) es = uses 2 pos.tile o.val := by
  refine ⟨(congrArg Led.bars hl).trans (led_bars hp), ?_, fun o => ?_⟩
  · rw [← stateBar_eq hpre]
    exact (congrArg Led.pollS hl).trans (led_pollS _ _)
  · rw [← fullBar_eq hpre, ← emptyBar_eq hpre]
    have hf := led_pollF (len := P.length (seqOf P g)) hp
    have ha := led_arr (len := P.length (seqOf P g)) hp
    fin_cases o
    · have h1 : okPolls (fullBar P g 0) es = _ := (congrArg Led.pollF0 hl).trans hf.1
      have h2 : arrivals (emptyBar P g 0) es = _ := (congrArg Led.arrE0 hl).trans ha.1
      refine ⟨h1.trans ?_, h2.trans ?_⟩ <;> (simp only [uses]; omega)
    · have h1 : okPolls (fullBar P g 1) es = _ := (congrArg Led.pollF1 hl).trans hf.2
      have h2 : arrivals (emptyBar P g 1) es = _ := (congrArg Led.arrE1 hl).trans ha.2
      refine ⟨h1.trans ?_, h2.trans ?_⟩ <;> (simp only [uses]; omega)

/-- The thread of a position other than the entry is the store leader of its block. -/
theorem leader_at (hpre : Pre P L mem0) {pos : Pos} {d : D} (hr : RefAt P g pos d)
    (hp : pos ≠ .entry) : g = storeLeader L (g / L.block) := by
  have hw := hr.keep.store
  have hl := (lead_of hr hp).1
  simp only [storeLeader, Protocol.thr, hpre.block]
  unfold warp at hw
  unfold lane at hl
  omega

/-- The stage of a tile as a number. -/
theorem stageOf_val (t : Nat) : (stageOf t).val = t % 2 := rfl

/-- A state at a position of a chunk has the registers of the chunk's row. -/
theorem row_of {pos : Pos} {d : D} {t row c n : Nat} (hr : RefAt P g pos d)
    (hc : InChunk t row c n pos) : Row P g t row c d := by
  have h := hr.pos
  cases pos <;> first
    | exact False.elim hc
    | (obtain ⟨rfl, rfl, rfl, -⟩ := hc; exact h.2)

/-- The tile register of a state at a position other than the entry. -/
theorem tile_reg (hpre : Pre P L mem0) {pos : Pos} {d : D} (hr : RefAt P g pos d)
    (hp : pos ≠ .entry) : (d.w 2112).toNat = pos.tile := by
  have hT := tile_of hr hp
  obtain ⟨b1, b2, b3⟩ := len_facts hpre g
  rw [hT.2.2.2.2.1, toNat_W (by have := hT.2.1; omega)]

/-! ### Along the trace: the events of the phase, by contract field -/

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads)
include hpre hX hg

/-- **`BarFacts`, `UnionFacts.bar_fence`**: a barrier event at a state of the phase is the
`bar.sync 0` at instruction 1402, the thread's sixth (five before it), at the entry. -/
theorem bar_store {k pc id : Nat} {cnt : Option Nat} {mode : BarMode} {s : D}
    (he : X.get (g, k) = some ⟨pc, .bar id cnt mode⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k s) :
    s.site = .bar 5 ∧ pc = 1402 ∧ id = 0 ∧ cnt = none ∧ mode = .sync ∧
      bar0Before X (g, k) = 5 := by
  obtain ⟨pos, hr, hl, hev, -⟩ := store_good hpre hX hg he hσ hI
  obtain ⟨rfl, h1, h2, h3, h4⟩ := ev_bar_inv hev
  exact ⟨hr.site, h1, h2, h3, h4, congrArg Led.bars hl⟩

/-- **`StoreFacts.full_poll`** (and the progress fields `poll`, `pollStage`): a poll at a state
of the phase is the store leader's poll of `storeFull` of the stage of a tile `t` of its
sequence, at instruction 2987, acquiring, with the parity `t / 2 % 2`, which is the parity of
its `t / 2` earlier successful polls of that mbarrier (one per earlier tile of the stage). -/
theorem full_poll_store {k pc q : Nat} {m : Loc} {ok acq : Bool} {sc : MbarScope} {s : D}
    (he : X.get (g, k) = some ⟨pc, .wait m q ok acq sc⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k s) :
    ∃ t, RefAt P g (.wait t) s ∧ t < tiles (P.length (seqOf P g)) ∧ pc = 2987 ∧
      m = (Bar.storeFull (stageOf t)).loc L (g / L.block) ∧ g = storeLeader L (g / L.block) ∧
      acq = true ∧ sc = .cta ∧ q = t / 2 % 2 ∧
      okPolls m ((X.tr g).take k) = uses 2 t (t % 2) ∧
      q % 2 = okPolls m ((X.tr g).take k) % 2 ∧ bar0Before X (g, k) = 6 := by
  obtain ⟨pos, hr, hl, hev, -⟩ := store_good hpre hX hg he hσ hI
  obtain ⟨t, rfl, h1, rfl, rfl, h4, h5⟩ := ev_wait_inv hev
  have hp : Pos.wait t ≠ .entry := by intro h; cases h
  obtain ⟨hb, -, hc⟩ := counts_at hpre (L := L) hp hl
  have hpoll := (hc (stageOf t)).1
  simp only [Pos.tile, Pos.polled, Nat.add_zero, stageOf_val] at hpoll
  have hm : fullBar P g (t % 2) = (Bar.storeFull (stageOf t)).loc L (g / L.block) :=
    fullBar_eq hpre g (stageOf t)
  rw [hm]
  refine ⟨t, hr, (lead_of hr hp).2, h1, rfl, leader_at hpre hr hp, h4, h5, rfl, hpoll, ?_, hb⟩
  rw [hpoll]
  simp only [uses]
  omega

/-- **`StoreFacts.empty_arrive`**: an arrival at a state of the phase is the store leader's one
release arrival, without transaction bytes, on `storeEmpty` of the stage of a tile `t` of its
sequence, at instruction 3101; before it the leader has arrived `t / 2` times on that mbarrier
and polled `storeFull` of the stage successfully `t / 2 + 1` times. -/
theorem empty_arrive_store {k pc tx cnt : Nat} {m : Loc} {rel : Bool} {sc : MbarScope} {s : D}
    (he : X.get (g, k) = some ⟨pc, .arrive m tx cnt rel sc⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k s) :
    ∃ t, RefAt P g (.arrive t) s ∧ t < tiles (P.length (seqOf P g)) ∧ pc = 3101 ∧
      m = (Bar.storeEmpty (stageOf t)).loc L (g / L.block) ∧ g = storeLeader L (g / L.block) ∧
      tx = 0 ∧ cnt = 1 ∧ rel = true ∧ sc = .cta ∧
      arrivals m ((X.tr g).take k) = uses 2 t (t % 2) ∧
      arrivals m ((X.tr g).take k) + 1 ≤
        okPolls ((Bar.storeFull (stageOf t)).loc L (g / L.block)) ((X.tr g).take k) ∧
      bar0Before X (g, k) = 6 := by
  obtain ⟨pos, hr, hl, hev, -⟩ := store_good hpre hX hg he hσ hI
  obtain ⟨t, rfl, h1, rfl, h3, h4, h5, h6⟩ := ev_arrive_inv hev
  have hp : Pos.arrive t ≠ .entry := by intro h; cases h
  obtain ⟨hb, -, hc⟩ := counts_at hpre (L := L) hp hl
  obtain ⟨hpoll, harr⟩ := hc (stageOf t)
  simp only [Pos.tile, Pos.polled, stageOf_val] at hpoll harr
  have hm : emptyBar P g (t % 2) = (Bar.storeEmpty (stageOf t)).loc L (g / L.block) :=
    emptyBar_eq hpre g (stageOf t)
  rw [hm]
  refine ⟨t, hr, (lead_of hr hp).2, h1, rfl, leader_at hpre hr hp, h3, h4, h5, h6, harr, ?_, hb⟩
  rw [harr, hpoll]
  simp only [uses]
  omega

/-- **`StoreFacts.no_tensor`**: no event at a state of the phase is the issue of a tensor
load. -/
theorem no_issue_store {k pc al : Nat} {sp : TensorCopy.Spec} {s : D}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue al sp⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k s) : False := by
  obtain ⟨pos, hr, hl, hev, -⟩ := store_good hpre hX hg he hσ hI
  cases pos <;> simp only [EvX, Ev, Event.mk.injEq, reduceCtorEq, and_false,
    false_and, exists_false, exists_const, or_false, false_or] at hev

/-- **`InitFacts.use_ev`** (and `SafetyFacts.mbarFrame`): an event at a state of the phase that
names an mbarrier names `storeFull` or `storeEmpty` of a stage, of the thread's own block,
after the `bar.sync 0` that publishes it (the second; the thread has made six). -/
theorem use_ev_store {k : Nat} {e : Event} {m : Loc} {s : D} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k s)
    (hm : Frame.MbarOf e m) :
    ∃ b : Bar, m = b.loc L (g / L.block) ∧ b.gen + 1 ≤ bar0Before X (g, k) := by
  obtain ⟨pos, hr, hl, hev, -⟩ := store_good hpre hX hg he hσ hI
  cases pos with
  | entry => cases hev; exact hm.elim
  | wait t =>
    obtain ⟨ok, rfl⟩ := hev
    obtain rfl : m = fullBar P g (t % 2) := hm
    obtain ⟨hb, -, -⟩ := counts_at hpre (L := L) (pos := .wait t) (by intro h; cases h) hl
    exact ⟨.storeFull (stageOf t), fullBar_eq hpre g (stageOf t), by
      rw [show bar0Before X (g, k) = 6 from hb]; exact (by decide : 1 + 1 ≤ 6)⟩
  | ts t i => cases hev; exact hm.elim
  | commit t => cases hev; exact hm.elim
  | ld0 t row c => obtain ⟨bs, -, rfl⟩ := hev; exact hm.elim
  | ld1 t row c v0 => obtain ⟨bs, -, rfl⟩ := hev; exact hm.elim
  | ld2 t row c v0 v1 => obtain ⟨bs, -, rfl⟩ := hev; exact hm.elim
  | ld3 t row c v0 v1 v2 => obtain ⟨bs, -, rfl⟩ := hev; exact hm.elim
  | gst t row c j => rcases hev with ⟨v, -, rfl⟩ | ⟨f, -, rfl⟩ <;> exact hm.elim
  | bwait t => cases hev; exact hm.elim
  | arrive t =>
    cases hev
    obtain rfl : m = emptyBar P g (t % 2) := hm
    obtain ⟨hb, -, -⟩ := counts_at hpre (L := L) (pos := .arrive t) (by intro h; cases h) hl
    exact ⟨.storeEmpty (stageOf t), emptyBar_eq hpre g (stageOf t), by
      rw [show bar0Before X (g, k) = 6 from hb]; exact (by decide : 1 + 1 ≤ 6)⟩

/-- **`UnionFacts.thread`**: a thread access at a state of the phase of a byte of the union
region of a block `c` is the store leader's read of output buffer `t % 2` of its own block in
a (partial) tile `t` (class `leader`): six `bar.sync 0` and the poll of the state mbarrier
before it, between its poll of `storeFull` and its arrival on `storeEmpty` of the stage. -/
theorem thread_store {O : Owners} {k c : Nat} {a : Acc} {w : Bool} {l : Loc} {s : D}
    (hacc : X.Access (g, k) a w) (hcov : a.Covers l) (hin : InUnion L c l)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k s) :
    g / L.block = c ∧ 1 ≤ okPolls (Bar.state.loc L c) ((X.tr g).take k) ∧
      ThreadClass L X O c g k w l := by
  rcases hacc with ⟨bs, ⟨pc, he⟩, rfl⟩ | ⟨bs, ⟨pc, he⟩, rfl⟩ | ⟨old, new, pc, he⟩
  · obtain ⟨pos, hr, hl, hev, -⟩ := store_good hpre hX hg he hσ hI
    obtain ⟨t, row, cc, m, hm, hch, -, rfl, -⟩ := ev_rd_inv hev
    have hp := hch.ne_entry
    obtain ⟨hb, hps, hc⟩ := counts_at hpre (L := L) hp hl
    obtain ⟨hpoll, harr⟩ := hc (stageOf t)
    have htile : pos.tile = t := by
      cases pos <;> first | exact False.elim hch | exact hch.1
    have hpd : pos.polled = 1 := by
      cases pos <;> first | exact False.elim hch | rfl
    rw [htile, hpd] at hpoll
    rw [htile] at harr
    obtain ⟨hpart, hrow, hcc, -⟩ := row_of hr hch
    obtain ⟨h1, h2, h3, h4⟩ := hcov
    simp only [rdAcc] at h1 h2 h3 h4
    have hsb := hpre.sharedBase
    have h2' : t % 2 < 2 := Nat.mod_lt _ (by decide)
    obtain rfl : g / L.block = c := by
      rw [block_div hpre, ← h2]
      exact hin.2.1
    refine ⟨rfl, by rw [hps], .leader (stageOf t) (leader_at hpre hr hp) rfl hb ?_ ?_⟩
    · refine ⟨h1, by rw [h2, block_div hpre], ?_, ?_⟩ <;> (simp only [stageOf_val]; omega)
    · rw [harr, hpoll]
      simp only [uses, stageOf_val]
      omega
  · obtain ⟨pos, hr, hl, hev, -⟩ := store_good hpre hX hg he hσ hI
    obtain ⟨t, row, cc, j, -, -, rfl, -⟩ := ev_wr_inv hev
    have h1 : l.space = .global := hcov.1
    rw [hin.1] at h1
    cases h1
  · obtain ⟨pos, hr, hl, hev, -⟩ := store_good hpre hX hg he hσ hI
    cases pos <;> simp only [EvX, Ev, Event.mk.injEq, reduceCtorEq, and_false,
      false_and, exists_false, exists_const, or_false, false_or] at hev

/-- **`UnionFacts.store`, `StoreCover.store_in`**: a tensor store at a state of the phase is
the store leader's store `i` of a full tile `t` of its sequence; every byte it reads is one of
the 256 bytes at offset `256 i` of output buffer `t % 2` of its own block (so a byte of the
union region), with six `bar.sync 0` and the poll of the state mbarrier before it, between the
poll of `storeFull` and the arrival on `storeEmpty` of the stage (class `tile`). -/
theorem store_store {k pc al x y z : Nat} {sp : TensorStore.Spec} {l : Loc} {s : D}
    (he : X.get (g, k) = some ⟨pc, .tensorStore al sp⟩)
    (hrl : TensorStore.readLoc sp x y z = some l)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k s) :
    InUnion L (g / L.block) l ∧ g = storeLeader L (g / L.block) ∧
      1 ≤ okPolls (Bar.state.loc L (g / L.block)) ((X.tr g).take k) ∧
      StoreClass L X (g / L.block) g k l := by
  obtain ⟨pos, hr, hl, hev, -⟩ := store_good hpre hX hg he hσ hI
  obtain ⟨t, i, rfl, -, rfl⟩ := ev_ts_inv hev
  have hp : Pos.ts t i ≠ .entry := by intro h; cases h
  obtain ⟨hb, hps, hc⟩ := counts_at hpre (L := L) hp hl
  obtain ⟨hpoll, harr⟩ := hc (stageOf t)
  simp only [Pos.tile, Pos.polled] at hpoll harr
  obtain ⟨h1, h2, h3, h4⟩ := readLoc_range hrl
  have h256 : mapBytes 10 = 256 := rfl
  rw [h256] at h4
  have hsb := hpre.sharedBase
  have h2' : t % 2 < 2 := Nat.mod_lt _ (by decide)
  have hi := i.isLt
  have hout : InOutput L (g / L.block) (stageOf t).val l := by
    refine ⟨h1, by rw [h2, block_div hpre], ?_, ?_⟩ <;> (simp only [stageOf_val]; omega)
  refine ⟨Protocol.InOutput.union (stageOf t).isLt hout, leader_at hpre hr hp, by rw [hps],
    .tile (stageOf t) hb hout ?_⟩
  rw [harr, hpoll]
  simp only [uses, stageOf_val]
  omega

end

/-! ### A tensor store is covered by the group wait of its tile -/

/-- The ledger of a position, projected: tensor stores, commits, group waits. -/
theorem led_ts (len t : Nat) (i : Fin 16) :
    (led len (.ts t i)).tstores = 16 * t + i.val ∧ (led len (.ts t i)).commits = t ∧
      (led len (.ts t i)).waits = t := ⟨rfl, rfl, rfl⟩

theorem led_bwait (len t : Nat) :
    (led len (.bwait t)).waits = t ∧
      (16 * t + 16 ≤ len → (led len (.bwait t)).commits = t + 1) := by
  simp only [led]
  split_ifs with h
  · exact ⟨rfl, fun _ => rfl⟩
  · exact ⟨rfl, fun h' => absurd h' h⟩

theorem led_arrive (len t : Nat) :
    (led len (.arrive t)).waits = t + 1 ∧
      (led len (.arrive t)).tstores = (if 16 * t + 16 ≤ len then 16 * t + 16 else 16 * t) := by
  simp only [led]
  split_ifs <;> exact ⟨rfl, rfl⟩

/-- An event with one more earlier event of a class than a prefix has is not in the prefix. -/
theorem lt_of_count {c : Event → Bool} {k w n : Nat} {ew : Event}
    (hk : ((X.tr g).take k).countP c = n) (hew : X.get (g, w) = some ew) (hc : c ew = true)
    (hw : ((X.tr g).take w).countP c = n) : k ≤ w := by
  by_contra hlt
  have h1 := Frame.countP_take_succ_ite c (l := X.tr g) hew
  rw [hc] at h1
  have h2 := take_count_le (X := X) (g := g) c (show w + 1 ≤ k by omega)
  simp only [↓reduceIte] at h1
  omega

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads)
include hpre hX hg

/-- **A tensor store of the phase is covered by the `.read` group wait of its tile.** For a
tensor store at a state of the phase (trace position `k`) and a later followed state (position
`m`) before which the thread has made a group wait that the store did not have before it:
between them the thread executes a `cp.async.bulk.wait_group.read 0` that covers the store (the
commit of the tile lies between the store and that wait). -/
theorem store_covered {k0 k m pc al : Nat} {sp : TensorStore.Spec} {s sm : D}
    (hen : Entered P L X g k0) (hk0 : k0 ≤ k)
    (he : X.get (g, k) = some ⟨pc, .tensorStore al sp⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k s) (hkm : k < m)
    (hσm : Frame.stateAt (code L) X g m = some (some sm))
    (hw : ((X.tr g).take k).countP isBWait + 1 ≤ ((X.tr g).take m).countP isBWait) :
    ∃ w, k < w ∧ w < m ∧ BulkWaitsFor X .read (g, k) (g, w) := by
  obtain ⟨pos, hr, hl, hev, -⟩ := store_good hpre hX hg he hσ hI
  obtain ⟨t, i, rfl, -, rfl⟩ := ev_ts_inv hev
  have hp : Pos.ts t i ≠ .entry := by intro h; cases h
  obtain ⟨hl0, ht⟩ := lead_of hr hp
  have hfull : 16 * t + 16 ≤ P.length (seqOf P g) := hr.pos.2.1
  have hwk : ((X.tr g).take k).countP isBWait = t := congrArg Led.waits hl
  have hck : ((X.tr g).take k).countP Store.isCommit = t := congrArg Led.commits hl
  -- the group wait with `t` earlier ones
  obtain ⟨w, ew, hwm, hew, hpw, hcw⟩ := exists_nthEv (X := X) (p := isBWait) (g := g) (k := m)
    (n := t) (by omega)
  have hkw : k < w := by
    have h1 := lt_of_count hwk hew hpw hcw
    rcases Nat.eq_or_lt_of_le h1 with rfl | h
    · rw [he] at hew
      cases hew
      cases hpw
    · exact h
  have hwlen : w < (X.tr g).length := (List.getElem?_eq_some_iff.mp hew).1
  obtain ⟨sw, hσw⟩ := followed_of_le hσm (Nat.le_of_lt hwm)
  have hIw : Inv P X g w sw := by
    rcases inv_at hpre hX hg hen (by omega) hwlen hσw with h | ⟨j, s1, -, hj, -, ho⟩
    · exact h
    · exfalso
      have hlen : 1 ≤ P.length (seqOf P g) := by omega
      have h1 := congrArg Led.waits ho.2
      rw [ledExit_lead hl0 hlen] at h1
      have h2 := take_count_le (X := X) (g := g) isBWait hj
      have h3 : ((X.tr g).take j).countP isBWait = tiles (P.length (seqOf P g)) := h1
      simp only [Pos.tile] at ht
      omega
  obtain ⟨posw, hrw, hlw, hevw, -⟩ := store_good hpre hX hg hew hσw hIw
  obtain ⟨pcw, kdw⟩ := ew
  cases kdw <;> (try (simp [isBWait] at hpw; done))
  rename_i md nn
  obtain ⟨t', rfl, rfl, rfl⟩ := ev_bwait_inv hevw
  obtain rfl : t = t' :=
    (((led_bwait _ t').1.symm.trans (congrArg Led.waits hlw).symm).trans hcw).symm
  have hcw' : ((X.tr g).take w).countP Store.isCommit = t + 1 :=
    (congrArg Led.commits hlw).trans ((led_bwait _ t).2 hfull)
  -- the commit with `t` earlier ones
  obtain ⟨c, ec, hcw2, hec, hpc, hcc⟩ := exists_nthEv (X := X) (p := Store.isCommit) (g := g)
    (k := w) (n := t) (by omega)
  have hkc : k < c := by
    have h1 := lt_of_count hck hec hpc hcc
    rcases Nat.eq_or_lt_of_le h1 with rfl | h
    · rw [he] at hec
      cases hec
      cases hpc
    · exact h
  obtain ⟨pcc, kdc⟩ := ec
  cases kdc <;> (try (simp [Store.isCommit] at hpc; done))
  exact ⟨w, hkw, hwm, bulkWaitsFor_of_commit he hec hew hkc hcw2⟩

/-- **`StoreFacts.store_wait`**: between a tensor store at a state of the phase and a later
arrival at a state of the phase, the store leader executes a `.read` bulk-group wait that
covers the store. -/
theorem store_wait_store {k0 k e pc al pce tx cnt : Nat} {sp : TensorStore.Spec} {m : Loc}
    {rel : Bool} {sc : MbarScope} {s se : D} (hen : Entered P L X g k0) (hk0 : k0 ≤ k)
    (he : X.get (g, k) = some ⟨pc, .tensorStore al sp⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k s) (hke : k < e)
    (hee : X.get (g, e) = some ⟨pce, .arrive m tx cnt rel sc⟩)
    (hσe : Frame.stateAt (code L) X g e = some (some se)) (hIe : Inv P X g e se) :
    ∃ w, k < w ∧ w < e ∧ BulkWaitsFor X .read (g, k) (g, w) := by
  refine store_covered hpre hX hg hen hk0 he hσ hI hke hσe ?_
  obtain ⟨pos, hr, hl, hev, -⟩ := store_good hpre hX hg he hσ hI
  obtain ⟨t, i, rfl, -, rfl⟩ := ev_ts_inv hev
  obtain ⟨pose, hre, hle, heve, -⟩ := store_good hpre hX hg hee hσe hIe
  obtain ⟨t', rfl, -⟩ := ev_arrive_inv heve
  have hwk : ((X.tr g).take k).countP isBWait = t := congrArg Led.waits hl
  have hwe : ((X.tr g).take e).countP isBWait = t' + 1 :=
    (congrArg Led.waits hle).trans (led_arrive _ t').1
  have hsk : ((X.tr g).take k).countP isTStore = 16 * t + i.val := congrArg Led.tstores hl
  have hse : ((X.tr g).take e).countP isTStore = _ :=
    (congrArg Led.tstores hle).trans (led_arrive _ t').2
  have h1 := Frame.countP_take_succ_ite isTStore (l := X.tr g) he
  have h2 := take_count_le (X := X) (g := g) isTStore (show k + 1 ≤ e by omega)
  have h3 : isTStore ⟨pc, .tensorStore al (tileSpec P g t i.val)⟩ = true := rfl
  rw [h3] at h1
  simp only [↓reduceIte] at h1
  have hi := i.isLt
  split_ifs at hse <;> omega

/-- **`LifeFacts.store_wait`, `UnionFacts.store_bar_wait`**: a tensor store at a state of the
phase precedes every position at which the thread has left the phase, and between the two the
thread executes a `.read` bulk-group wait that covers the store. -/
theorem store_wait_left {k0 k j pc al : Nat} {sp : TensorStore.Spec} {s sj : D}
    (hen : Entered P L X g k0) (hk0 : k0 ≤ k)
    (he : X.get (g, k) = some ⟨pc, .tensorStore al sp⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k s)
    (hσj : Frame.stateAt (code L) X g j = some (some sj)) (ho : Out P X g j sj) :
    k < j ∧ ∃ w, k < w ∧ w < j ∧ BulkWaitsFor X .read (g, k) (g, w) := by
  obtain ⟨pos, hr, hl, hev, -⟩ := store_good hpre hX hg he hσ hI
  have hkj : k < j := by
    by_contra h
    exact not_out hr hl ho (by omega)
  refine ⟨hkj, store_covered hpre hX hg hen hk0 he hσ hI hkj hσj ?_⟩
  obtain ⟨t, i, rfl, -, rfl⟩ := ev_ts_inv hev
  have hp : Pos.ts t i ≠ .entry := by intro h; cases h
  obtain ⟨hl0, ht⟩ := lead_of hr hp
  have hfull : 16 * t + 16 ≤ P.length (seqOf P g) := hr.pos.2.1
  have hwk : ((X.tr g).take k).countP isBWait = t := congrArg Led.waits hl
  have h1 := congrArg Led.waits ho.2
  rw [ledExit_lead hl0 (by omega)] at h1
  have h3 : ((X.tr g).take j).countP isBWait = tiles (P.length (seqOf P g)) := h1
  simp only [Pos.tile] at ht
  omega

/-- **`LifeFacts.store_wait`, `UnionFacts.store_bar_wait`, in their own shape**: between a
tensor store at a state of the phase and a later `bar.sync` or exit of the thread (at a followed
state), the thread executes a `.read` bulk-group wait that covers the store. -/
theorem store_wait_after {k0 k j pc al : Nat} {sp : TensorStore.Spec} {s sj : D} {ej : Event}
    (hen : Entered P L X g k0) (hk0 : k0 ≤ k)
    (he : X.get (g, k) = some ⟨pc, .tensorStore al sp⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k s) (hkj : k < j)
    (hej : X.get (g, j) = some ej)
    (hσj : Frame.stateAt (code L) X g j = some (some sj))
    (hkind : (∃ id cnt mode, ej.kind = .bar id cnt mode) ∨ ej.kind = .exit) :
    ∃ w, k < w ∧ w < j ∧ BulkWaitsFor X .read (g, k) (g, w) := by
  have hjlen : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp hej).1
  rcases inv_at hpre hX hg hen (by omega) hjlen hσj with hIj | ⟨j0, s0, -, hj0, hσ0, ho⟩
  · exfalso
    obtain ⟨posj, hrj, hlj, hevj, -⟩ := store_good hpre hX hg hej hσj hIj
    obtain ⟨pcj, kdj⟩ := ej
    rcases hkind with ⟨id, cnt, mode, hk⟩ | hk
    · dsimp only at hk
      subst hk
      obtain ⟨rfl, -⟩ := ev_bar_inv hevj
      obtain ⟨pos, hr, hl, hev, -⟩ := store_good hpre hX hg he hσ hI
      obtain ⟨t, i, rfl, -, rfl⟩ := ev_ts_inv hev
      have h1 : ((X.tr g).take k).countP (Execution.isBarId 0) = 6 := congrArg Led.bars hl
      have h2 : ((X.tr g).take j).countP (Execution.isBarId 0) = 5 := congrArg Led.bars hlj
      have h3 := take_count_le (X := X) (g := g) (Execution.isBarId 0) (Nat.le_of_lt hkj)
      omega
    · dsimp only at hk
      subst hk
      cases posj <;> simp only [EvX, Ev, Event.mk.injEq, reduceCtorEq, and_false,
        false_and, exists_false, exists_const, or_false, false_or] at hevj
  · obtain ⟨-, w, h1, h2, h3⟩ := store_wait_left hpre hX hg hen hk0 he hσ hI hσ0 ho
    exact ⟨w, h1, by omega, h3⟩

end

/-! ### The global bytes of the stores -/

/-- The block of a thread is the block of its sequence and head. -/
theorem blockOf_cta (hpre : Pre P L mem0) (g : Nat) :
    blockOf P (seqOf P g) (headOf P g) = g / L.block := by
  rw [block_div hpre]
  exact Protocol.blockOf_eq (cta g)

/-- **The bytes of a slot of a tensor store of a full tile**: slot `(x, y, z)` of store `i` of
tile `t` has `x < 8`, `y < 16`, `z < 2`; it writes byte `z` of the output of token
`16 t + y` and feature `8 i + x` of the thread's sequence and head, and reads the byte at
offset `256 i + 16 y + 2 x + z` of output buffer `t % 2` of the thread's block. -/
theorem tileSpec_slot (hpre : Pre P L mem0) (hg : g < L.threads) {t i x y z : Nat}
    (hi : i < 16) (hfull : 16 * t + 16 ≤ P.length (seqOf P g)) (hx : x < 8) (hy : y < 16)
    (hz : z < 2) :
    TensorStore.writeLoc (tileSpec P g t i) x y z =
        some ((P.outLoc (seqOf P g) (headOf P g) (16 * t + y) ⟨8 * i + x, by omega⟩).at z) ∧
      TensorStore.readLoc (tileSpec P g t i) x y z =
        some (outByte L (g / L.block) (t % 2) (256 * i + 16 * y + 2 * x + z)) := by
  have h1 := tok_le hpre g
  have hh := headOf_lt hpre hg
  refine ⟨?_, ?_⟩
  · rw [tileSpec, storeOut_writeLoc hx hy hz (by omega) (by omega) hh]
    simp only [Params.outLoc, Loc.at, Option.some.injEq, Loc.mk.injEq, true_and]
    rw [show 16 * t + firstToken P.length (seqOf P g) + y =
      firstToken P.length (seqOf P g) + (16 * t + y) by omega]
  · rw [tileSpec, storeOut_readLoc hx hy hz]
    simp only [outByte, hpre.sharedBase, block_div hpre, Option.some.injEq, Loc.mk.injEq,
      true_and]
    omega

/-- A byte that a tensor store of a full tile writes or reads belongs to a slot of its box. -/
theorem tileSpec_lt {t i x y z : Nat} {l : Loc}
    (h : TensorStore.writeLoc (tileSpec P g t i) x y z = some l ∨
      TensorStore.readLoc (tileSpec P g t i) x y z = some l) : x < 8 ∧ y < 16 ∧ z < 2 := by
  rcases h with h | h
  · exact storeOut_writeLoc_lt h
  · exact storeOut_readLoc_lt h

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads)
include hpre hX hg

/-- **`StoresIssued.tile`**: a tensor store at a state of the phase whose slot `(x, y, z)`
writes byte `k` of the output of token `t` and value channel `v` of `(sq, h)` is a store of
the store leader of the block of `(sq, h)`, with six `bar.sync 0` before it, after
`t / 16 / 2 + 1` successful polls of `storeFull` of the stage of tile `t / 16`, and the slot
reads the byte at offset `outOff (t % 16) v k` of that stage's output buffer. -/
theorem tile_store {i pc al x y z sq h t k : Nat} {sp : TensorStore.Spec} {v : Fin 128} {s : D}
    (hsq : sq < P.sequences) (hh : h < P.heads) (ht : t < P.length sq) (hk : k < 2)
    (he : X.get (g, i) = some ⟨pc, .tensorStore al sp⟩)
    (hwl : TensorStore.writeLoc sp x y z = some ((P.outLoc sq h t v).at k))
    (hσ : Frame.stateAt (code L) X g i = some (some s)) (hI : Inv P X g i s) :
    g = storeLeader L (blockOf P sq h) ∧ bar0Before X (g, i) = 6 ∧
      okPolls ((Bar.storeFull (stageOf (t / 16))).loc L (blockOf P sq h)) ((X.tr g).take i) =
        t / 16 / 2 + 1 ∧
      TensorStore.readLoc sp x y z =
        some (outByte L (blockOf P sq h) (stageOf (t / 16)).val (outOff (t % 16) v k)) := by
  obtain ⟨pos, hr, hl, hev, -⟩ := store_good hpre hX hg he hσ hI
  obtain ⟨tt, j, rfl, -, rfl⟩ := ev_ts_inv hev
  have hp : Pos.ts tt j ≠ .entry := by intro h'; cases h'
  have hfull : 16 * tt + 16 ≤ P.length (seqOf P g) := hr.pos.2.1
  obtain ⟨hx, hy, hz⟩ := tileSpec_lt (.inl hwl)
  obtain ⟨hw, hrd⟩ := tileSpec_slot hpre hg j.isLt hfull hx hy hz
  rw [hw] at hwl
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := Protocol.outLoc_at_inj (headOf_lt hpre hg) hh
    (show 16 * tt + y < P.length (seqOf P g) by omega) ht hz hk (Option.some.inj hwl)
  obtain ⟨hb, -, hc⟩ := counts_at hpre (L := L) hp hl
  have hpoll := (hc (stageOf tt)).1
  simp only [Pos.tile, Pos.polled] at hpoll
  have e1 : (16 * tt + y) / 16 = tt := by omega
  have e2 : (16 * tt + y) % 16 = y := by omega
  rw [blockOf_cta hpre, e1, e2]
  refine ⟨leader_at hpre hr hp, hb, ?_, ?_⟩
  · rw [hpoll]
    simp only [uses, stageOf_val]
    omega
  · rw [hrd]
    simp only [outByte, outOff, stageOf_val, Option.some.injEq, Loc.mk.injEq, true_and]
    have hj := j.isLt
    omega

/-- **`StoresIssued.elem`**: a write event at a state of the phase that covers a byte of the
output of a token of `(sq, h)` is an event of the store leader of the block of `(sq, h)`. -/
theorem elem_store {i pc sq h t k : Nat} {a : Acc} {bs : List Byte} {v : Fin 128} {s : D}
    (hsq : sq < P.sequences) (hh : h < P.heads) (ht : t < P.length sq) (hk : k < 2)
    (he : X.get (g, i) = some ⟨pc, .wr a bs⟩) (hcov : a.Covers ((P.outLoc sq h t v).at k))
    (hσ : Frame.stateAt (code L) X g i = some (some s)) (hI : Inv P X g i s) :
    g = storeLeader L (blockOf P sq h) := by
  obtain ⟨pos, hr, hl, hev, -⟩ := store_good hpre hX hg he hσ hI
  obtain ⟨tt, row, c, j, rfl, -, rfl, -⟩ := ev_wr_inv hev
  have hp : Pos.gst tt row c j ≠ .entry := by intro h'; cases h'
  obtain ⟨hpart, hrow, hc, -⟩ := hr.pos.2
  have hj := j.isLt
  obtain ⟨-, -, h3, h4⟩ := hcov
  simp only [wrAcc, Params.outLoc, Loc.at] at h3 h4
  obtain ⟨z, hz, heq⟩ : ∃ z, z < 2 ∧
      (P.outLoc (seqOf P g) (headOf P g) (16 * tt + row) ⟨8 * c + j.val, by omega⟩).at z =
        (P.outLoc sq h t v).at k := by
    refine ⟨(P.outputBase + 256 * ((firstToken P.length sq + t) * P.heads + h) + 2 * v.val + k) -
      (P.outputBase + 256 * ((firstToken P.length (seqOf P g) + (16 * tt + row)) * P.heads +
        headOf P g) + 2 * (8 * c + j.val)), ?_, ?_⟩
    · omega
    · simp only [Params.outLoc, Loc.at, Loc.mk.injEq, true_and]
      omega
  obtain ⟨rfl, rfl, -⟩ := Protocol.outLoc_at_inj (headOf_lt hpre hg) hh
    (show 16 * tt + row < P.length (seqOf P g) by omega) ht hz hk heq
  rw [blockOf_cta hpre]
  exact leader_at hpre hr hp

end

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads)
include hpre hX hg

/-- **An event of a class with fewer earlier ones than the exit ledger has is an event of the
phase**: a class that has no event before the entry and more than `n` events at every exit has
its event with `n` earlier ones at a followed state with the invariant. -/
theorem inv_of_nth {k0 i0 n : Nat} {c : Event → Bool} {e0 : Event} (hen : Entered P L X g k0)
    {j : Nat} {sj : D} (hi0 : i0 < j) (hσj : Frame.stateAt (code L) X g j = some (some sj))
    (he0 : X.get (g, i0) = some e0) (hc0 : c e0 = true)
    (hcnt : ((X.tr g).take i0).countP c = n) (hentry : ((X.tr g).take k0).countP c = 0)
    (hexit : ∀ j' s', Out P X g j' s' → n < ((X.tr g).take j').countP c) :
    k0 ≤ i0 ∧ ∃ s0, Frame.stateAt (code L) X g i0 = some (some s0) ∧ Inv P X g i0 s0 := by
  have h1 := Frame.countP_take_succ_ite c (l := X.tr g) he0
  rw [hc0] at h1
  simp only [↓reduceIte] at h1
  have hk0 : k0 ≤ i0 := by
    by_contra hlt
    have h2 := take_count_le (X := X) (g := g) c (show i0 + 1 ≤ k0 by omega)
    omega
  obtain ⟨s0, hσ0⟩ := followed_of_le hσj (Nat.le_of_lt hi0)
  have hlen : i0 < (X.tr g).length := (List.getElem?_eq_some_iff.mp he0).1
  rcases inv_at hpre hX hg hen hk0 hlen hσ0 with h | ⟨j', s', -, hj', -, ho'⟩
  · exact ⟨hk0, s0, hσ0, h⟩
  · have h2 := hexit j' s' ho'
    have h3 := take_count_le (X := X) (g := g) c hj'
    omega

/-- **`StoresIssued.outIssued`**: when the store leader has left the phase (the exit condition
at a followed state at position `j`), it has an event before `j` for every byte of the output
of every token of its sequence: a tensor store with a slot that writes the byte (a token of a
full tile) or a write event that covers it (a token of the partial last tile). -/
theorem outIssued_store {k0 j : Nat} {sj : D} (hen : Entered P L X g k0)
    (hσj : Frame.stateAt (code L) X g j = some (some sj)) (ho : Out P X g j sj)
    (hl0 : lane g = 0) {t : Nat} (ht : t < P.length (seqOf P g)) (v : Fin 128) {k : Nat}
    (hk : k < 2) :
    (∃ i pc al sp x y z, i < j ∧ X.get (g, i) = some ⟨pc, .tensorStore al sp⟩ ∧
      TensorStore.writeLoc sp x y z =
        some ((P.outLoc (seqOf P g) (headOf P g) t v).at k)) ∨
    (∃ i pc a bs, i < j ∧ X.get (g, i) = some ⟨pc, .wr a bs⟩ ∧
      a.Covers ((P.outLoc (seqOf P g) (headOf P g) t v).at k)) := by
  have hlen : 1 ≤ P.length (seqOf P g) := by omega
  have hex := ho.2
  rw [ledExit_lead hl0 hlen] at hex
  have hin := hen
  obtain ⟨s0, -, -, hle⟩ := hin
  have hv := v.isLt
  by_cases hfull : t / 16 < P.length (seqOf P g) / 16
  · -- a token of a full tile: tensor store `v / 8` of tile `t / 16`
    left
    have hts : ((X.tr g).take j).countP isTStore = 16 * (P.length (seqOf P g) / 16) :=
      congrArg Led.tstores hex
    obtain ⟨i0, e0, hi0, he0, hc0, hcnt⟩ := exists_nthEv (X := X) (p := isTStore) (g := g)
      (k := j) (n := 16 * (t / 16) + v.val / 8) (by omega)
    obtain ⟨-, s1, hσ1, hI1⟩ := inv_of_nth hpre hX hg hen hi0 hσj he0 hc0 hcnt
      (congrArg Led.tstores hle) (fun j' s' ho' => by
        have h := ho'.2
        rw [ledExit_lead hl0 hlen] at h
        have h' : ((X.tr g).take j').countP isTStore = 16 * (P.length (seqOf P g) / 16) :=
          congrArg Led.tstores h
        omega)
    obtain ⟨pos, hr, hl, hev, -⟩ := store_good hpre hX hg he0 hσ1 hI1
    obtain ⟨pc0, kd0⟩ := e0
    cases kd0 <;> (try (simp [isTStore] at hc0; done))
    rename_i al sp
    obtain ⟨t', i', rfl, -, rfl⟩ := ev_ts_inv hev
    have hcnt' : ((X.tr g).take i0).countP isTStore = 16 * t' + i'.val := congrArg Led.tstores hl
    have hi' := i'.isLt
    obtain ⟨rfl, hiv⟩ : t' = t / 16 ∧ i'.val = v.val / 8 := by constructor <;> omega
    have hfull' : 16 * (t / 16) + 16 ≤ P.length (seqOf P g) := hr.pos.2.1
    obtain ⟨hw, -⟩ := tileSpec_slot hpre hg (x := v.val % 8) (y := t % 16) (z := k) hi' hfull'
      (by omega) (by omega) hk
    refine ⟨i0, pc0, _, _, v.val % 8, t % 16, k, hi0, he0, ?_⟩
    rw [hw]
    simp only [Params.outLoc, Loc.at, Option.some.injEq, Loc.mk.injEq, true_and]
    rw [show 16 * (t / 16) + t % 16 = t by omega]
    omega
  · -- a token of the partial last tile: global store `v % 8` of chunk `v / 8` of its row
    right
    have hgs : ((X.tr g).take j).countP isGWrite = 128 * (P.length (seqOf P g) % 16) :=
      congrArg Led.gstores hex
    obtain ⟨i0, e0, hi0, he0, hc0, hcnt⟩ := exists_nthEv (X := X) (p := isGWrite) (g := g)
      (k := j) (n := 8 * (16 * (t - 16 * (P.length (seqOf P g) / 16)) + v.val / 8) + v.val % 8)
      (by omega)
    obtain ⟨-, s1, hσ1, hI1⟩ := inv_of_nth hpre hX hg hen hi0 hσj he0 hc0 hcnt
      (congrArg Led.gstores hle) (fun j' s' ho' => by
        have h := ho'.2
        rw [ledExit_lead hl0 hlen] at h
        have h' : ((X.tr g).take j').countP isGWrite = 128 * (P.length (seqOf P g) % 16) :=
          congrArg Led.gstores h
        omega)
    obtain ⟨pos, hr, hl, hev, -⟩ := store_good hpre hX hg he0 hσ1 hI1
    obtain ⟨pc0, kd0⟩ := e0
    cases kd0 <;> (try (simp [isGWrite] at hc0; done))
    rename_i a bs
    obtain ⟨t', r', c', j', rfl, -, rfl, -⟩ := ev_wr_inv hev
    have hcnt' : ((X.tr g).take i0).countP isGWrite = 8 * (16 * r' + c') + j'.val :=
      congrArg Led.gstores hl
    obtain ⟨hpart, hrow, hc', -⟩ := hr.pos.2
    have hj' := j'.isLt
    obtain rfl : t = 16 * t' + r' := by omega
    have hv' : v.val = 8 * c' + j'.val := by omega
    refine ⟨i0, pc0, _, bs, hi0, he0, rfl, rfl, ?_, ?_⟩ <;>
      (simp only [wrAcc, Params.outLoc, Loc.at]; omega)

end

/-! ### The exit -/

/-- **The exit condition gives the entry condition of the epilogue**
(`Ref/Epilogue/Interface.lean: In`, through its `entry_of_store`): the thread is of the store
warp, at the site `bar_7` (instruction 3113), `%r1736` holds its index, `%p77` is true, `%r180`
is the election flag of its lane, and it has made six `bar.sync 0`. -/
theorem out_link {k : Nat} {d : D} (ho : Out P X g k d) :
    warp g = 5 ∧ d.site = .bar 7 ∧ d.w 2042 = W (tid g) ∧ d.p 77 = true ∧
      d.w 486 = W (if lane g = 0 then 1 else 0) ∧
      ((X.tr g).take k).countP (Execution.isBarId 0) = 6 :=
  ⟨ho.1.keep.store, ho.1.site, ho.1.tid', ho.1.role, ho.1.keep.elected,
    (congrArg Led.bars ho.2).trans (ledExit_bars P g)⟩

/-- **The counts at the exit, in the protocol layer's terms**: one successful poll of the state
mbarrier; and for the store leader (lane 0), per output stage `o`, one successful poll of
`storeFull o` and one arrival on `storeEmpty o` for each tile of the stage; for another lane
none. -/
theorem out_counts (hpre : Pre P L mem0) {k : Nat} {d : D} (ho : Out P X g k d) :
    okPolls (Bar.state.loc L (g / L.block)) ((X.tr g).take k) = 1 ∧
      ∀ o : Fin 2,
        okPolls ((Bar.storeFull o).loc L (g / L.block)) ((X.tr g).take k) =
          (if lane g = 0 then uses 2 (tiles (P.length (seqOf P g))) o.val else 0) ∧
        arrivals ((Bar.storeEmpty o).loc L (g / L.block)) ((X.tr g).take k) =
          (if lane g = 0 then uses 2 (tiles (P.length (seqOf P g))) o.val else 0) := by
  have hl := ho.2
  have hS : okPolls (stateBar P g) ((X.tr g).take k) = (ledExit P g).pollS :=
    congrArg Led.pollS hl
  have hF0 : okPolls (fullBar P g 0) ((X.tr g).take k) = (ledExit P g).pollF0 :=
    congrArg Led.pollF0 hl
  have hF1 : okPolls (fullBar P g 1) ((X.tr g).take k) = (ledExit P g).pollF1 :=
    congrArg Led.pollF1 hl
  have hE0 : arrivals (emptyBar P g 0) ((X.tr g).take k) = (ledExit P g).arrE0 :=
    congrArg Led.arrE0 hl
  have hE1 : arrivals (emptyBar P g 1) ((X.tr g).take k) = (ledExit P g).arrE1 :=
    congrArg Led.arrE1 hl
  have ht0 : tiles 0 = 0 := rfl
  refine ⟨?_, fun o => ?_⟩
  · rw [← stateBar_eq hpre, hS]
    unfold ledExit
    split_ifs <;> rfl
  · rw [← fullBar_eq hpre, ← emptyBar_eq hpre]
    fin_cases o
    · show okPolls (fullBar P g 0) _ = (if lane g = 0 then uses 2 _ 0 else 0) ∧
        arrivals (emptyBar P g 0) _ = (if lane g = 0 then uses 2 _ 0 else 0)
      rw [hF0, hE0]
      by_cases hlead : lane g = 0 ∧ 1 ≤ P.length (seqOf P g)
      · rw [ledExit_lead hlead.1 hlead.2]
        simp only [hlead.1, ↓reduceIte, uses]
        constructor <;> omega
      · have he : ledExit P g = ⟨6, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩ := by
          simp only [ledExit, hlead, ↓reduceIte]
        rw [he]
        by_cases h0 : lane g = 0
        · have h2 : P.length (seqOf P g) = 0 := by
            have : ¬ 1 ≤ P.length (seqOf P g) := fun h => hlead ⟨h0, h⟩
            omega
          simp only [h0, ↓reduceIte, uses, h2, ht0]
          first | trivial | exact ⟨rfl, rfl⟩ | (constructor <;> first | rfl | trivial)
        · simp only [h0, ↓reduceIte]
          first | trivial | exact ⟨rfl, rfl⟩ | (constructor <;> first | rfl | trivial)
    · show okPolls (fullBar P g 1) _ = (if lane g = 0 then uses 2 _ 1 else 0) ∧
        arrivals (emptyBar P g 1) _ = (if lane g = 0 then uses 2 _ 1 else 0)
      rw [hF1, hE1]
      by_cases hlead : lane g = 0 ∧ 1 ≤ P.length (seqOf P g)
      · rw [ledExit_lead hlead.1 hlead.2]
        simp only [hlead.1, ↓reduceIte, uses]
        constructor <;> omega
      · have he : ledExit P g = ⟨6, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩ := by
          simp only [ledExit, hlead, ↓reduceIte]
        rw [he]
        by_cases h0 : lane g = 0
        · have h2 : P.length (seqOf P g) = 0 := by
            have : ¬ 1 ≤ P.length (seqOf P g) := fun h => hlead ⟨h0, h⟩
            omega
          simp only [h0, ↓reduceIte, uses, h2, ht0]
          first | trivial | exact ⟨rfl, rfl⟩ | (constructor <;> first | rfl | trivial)
        · simp only [h0, ↓reduceIte]
          first | trivial | exact ⟨rfl, rfl⟩ | (constructor <;> first | rfl | trivial)

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Store
