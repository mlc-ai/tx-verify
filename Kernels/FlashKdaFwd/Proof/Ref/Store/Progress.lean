-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Store.Exports

@[expose] public section

/-! # The Store share of the progress contract

`Proof/Schedule/Contract.lean: RefProgress` is what the progress instance and the termination
bound need from the reference layer about a followed state `d` of a thread and the counts over
its earlier events. This file proves the share of the Store phase (a thread of the store warp
between its `bar.sync 0` at instruction 1402 and the one at 3113), in the pattern of
`Ref/Startup/Progress.lean` and `Ref/Producer/Progress.lean`: the statements do not import the
progress files; each is in the terms the field unfolds to (the field is named in the
docstring), for a state that satisfies the phase invariant `Inv`.

* `site_pc`, `region_store`: field `region` (a state of the phase is at instruction 1402 or at
  an instruction from 2945 to 3112, and the thread is of the store warp: `160 ≤ g % L.block`).
  A state of the phase is at the site of a position (`Pos.site`: a barrier, a poll, a tensor
  copy, a commit, a load, a store, a group wait, an arrival): never at an election, a shuffle, a
  matrix instruction or the exit (the vacuous cases of `collAt`, `tile_matrix`, `exitAt`).
* `tileOf`, `leftOf`: **the tile index and the counted events left as functions of the STATE**
  (its site and the registers `%r1806`, `%r1809`, `%r1811`), for the contract's `Nums.tile` and
  `Nums.left`; `tileOf_eq`, `leftOf_eq`: they are the position's `Pos.tile` and `leftAt`.
  `tilesOf_cta`: the tile count is the protocol layer's `ctaTiles P (g / L.block)`.
* `tileIdx_store`: fields `tile_le`, `tile_start`, `arrStoreEmpty`.
* `bar0_store`, `bar0_out`: field `bar0` (`bar0Of d.site.pc` unfolded).
* `poll_store`: fields `poll` and `pollStage` at the poll site 2987: the polled mbarrier is
  `Bar.storeFull` of the stage `tile % 2`, the thread is the store leader, `tile < tiles`, its
  successful polls of it are `uses 2 tile (tile % 2)` (= `roundOf (.storeFull o)` of the tile
  index), the instruction is past 1402, and every wait event the state can fire is on that
  mbarrier with the parity of those polls (`Bar.delta = 0`).
* `barStep_store`: field `barStep` for the one barrier of the phase (1402), by role: sub-step
  0, a later instruction; the successor is the poll of tile 0 (the store leader of a nonempty
  sequence: tile index 0) or the exit state at 3113 (the 31 other lanes and the leader of an
  empty sequence: there the tile index is the tile count, the field's "not smaller").
* `left_step`, `leftOf_dec`: field `left_dec`: a step of the machine from a state of the phase
  lowers `leftOf` by one, except a failed poll, which keeps it; at the exit nothing of the
  phase is left (`leftOf = 1` before the last event). The counted events of the phase: the
  barrier at 1402; per full tile 20 (the poll, 16 tensor stores, the commit, the group wait,
  the arrival); for a partial last tile with `R` live rows `3 + 192 R` (the poll, per row 16
  chunks of 4 reads and 8 stores, the group wait, the arrival).
* `inv_range`, `frame_store`: every class of events that no event of the phase belongs to keeps
  its count from the entry to every state of the phase (`quiet_of_kind`: a class that is false
  on the nine kinds of events of the phase): the fields `coll` (no warp collective) and the
  counts of the other roles' mbarriers. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Store
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Protocol (Bar uses storeLeader bar0Before bar0Pcs stageOf)

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-! ### Where the states of the phase are -/

/-- The sixteen tensor stores of a full tile are at the instructions 3052 to 3082. -/
theorem ts_pc (i : Fin 16) :
    (Site.tensorCopy ⟨226 + i.val, by have := i.isLt; omega⟩).pc = 3052 + 2 * i.val := by
  fin_cases i <;> rfl

/-- The eight global stores of a chunk are at the instructions 3025 to 3032. -/
theorem gst_pc (j : Fin 8) :
    (Site.store ⟨10 + j.val, by have := j.isLt; omega⟩).pc = 3025 + j.val := by
  fin_cases j <;> rfl

/-- **The instruction of a position**: 1402 at the entry, an instruction of the store leader's
loop (2945 to 3112) elsewhere. -/
theorem site_pc (pos : Pos) :
    (pos = .entry ∧ pos.site.pc = 1402) ∨ (pos ≠ .entry ∧ 2944 < pos.site.pc ∧
      pos.site.pc ≤ 3112) := by
  cases pos with
  | entry => exact .inl ⟨rfl, rfl⟩
  | ts t i =>
    refine .inr ⟨(by intro h; cases h), ?_⟩
    have := i.isLt
    rw [show (Pos.ts t i).site.pc = 3052 + 2 * i.val from ts_pc i]
    omega
  | gst t row c j =>
    refine .inr ⟨(by intro h; cases h), ?_⟩
    have := j.isLt
    rw [show (Pos.gst t row c j).site.pc = 3025 + j.val from gst_pc j]
    omega
  | wait t =>
    refine .inr ⟨(by intro h; cases h), ?_⟩
    rw [show (Pos.wait t).site.pc = 2987 from rfl]
    omega
  | commit t =>
    refine .inr ⟨(by intro h; cases h), ?_⟩
    rw [show (Pos.commit t).site.pc = 3083 from rfl]
    omega
  | ld0 t row c =>
    refine .inr ⟨(by intro h; cases h), ?_⟩
    rw [show (Pos.ld0 t row c).site.pc = 3020 from rfl]
    omega
  | ld1 t row c v0 =>
    refine .inr ⟨(by intro h; cases h), ?_⟩
    rw [show (Pos.ld1 t row c v0).site.pc = 3020 from rfl]
    omega
  | ld2 t row c v0 v1 =>
    refine .inr ⟨(by intro h; cases h), ?_⟩
    rw [show (Pos.ld2 t row c v0 v1).site.pc = 3020 from rfl]
    omega
  | ld3 t row c v0 v1 v2 =>
    refine .inr ⟨(by intro h; cases h), ?_⟩
    rw [show (Pos.ld3 t row c v0 v1 v2).site.pc = 3020 from rfl]
    omega
  | bwait t =>
    refine .inr ⟨(by intro h; cases h), ?_⟩
    rw [show (Pos.bwait t).site.pc = 3093 from rfl]
    omega
  | arrive t =>
    refine .inr ⟨(by intro h; cases h), ?_⟩
    rw [show (Pos.arrive t).site.pc = 3101 from rfl]
    omega

/-- The sub-step of the entry site. -/
theorem entry_sub : (Pos.entry).site.sub = 0 := rfl

/-- **Field `region`**: a state of the phase is at instruction 1402 or at an instruction of
the store leader's loop (2945 to 3112), and its thread is of the store warp. -/
theorem region_store (hpre : Pre P L mem0) {k : Nat} {s : D} (hI : Inv P X g k s) :
    (s.site.pc = 1402 ∨ (2944 < s.site.pc ∧ s.site.pc ≤ 3112)) ∧ 160 ≤ g % L.block := by
  obtain ⟨pos, hr, -⟩ := hI
  refine ⟨?_, ?_⟩
  · rw [hr.site]
    rcases site_pc pos with ⟨-, h⟩ | ⟨-, h⟩
    · exact .inl h
    · exact .inr h
  · rw [block_mod hpre]
    exact (warp_eq5_iff g).mp hr.keep.store

/-! ### The tile index and the counted events left, as functions of the state -/

/-- The tile count of the thread's block, in the protocol layer's form (`ctaTiles`). -/
theorem tilesOf_cta (hpre : Pre P L mem0) (g : Nat) :
    tiles (P.length (seqOf P g)) = tiles (P.length (g / L.block % P.sequences)) := by
  simp only [seqOf, hpre.block]

/-- **The tile index of a state of the phase, read off the state**: 0 at the barrier 1402, the
register `%r1806` (the tile counter of the store leader's loop) elsewhere. -/
def tileOf (d : D) : Nat :=
  match d.site with
  | .bar _ => 0
  | _ => (d.w 2112).toNat

/-- The counted events of a partial last tile of a sequence of `len` tokens: none when the
length is a multiple of 16, else the poll, 192 per live row, the group wait and the arrival. -/
def partEv (len : Nat) : Nat := if len % 16 = 0 then 0 else 3 + 192 * (len % 16)

/-- **The counted events left in the phase at a position** (`len` the length of the thread's
sequence, `lead` whether the thread is the store leader of a nonempty sequence). -/
def leftAt (len : Nat) (lead : Prop) [Decidable lead] : Pos → Nat
  | .entry => if lead then 1 + 20 * (len / 16) + partEv len else 1
  | .wait t => 20 * (len / 16 - t) + partEv len
  | .ts t i => 20 * (len / 16 - t) + partEv len - 1 - i.val
  | .commit t => 20 * (len / 16 - t) + partEv len - 17
  | .ld0 _ row c => 2 + 192 * (len % 16 - row) - 12 * c
  | .ld1 _ row c _ => 2 + 192 * (len % 16 - row) - 12 * c - 1
  | .ld2 _ row c _ _ => 2 + 192 * (len % 16 - row) - 12 * c - 2
  | .ld3 _ row c _ _ _ => 2 + 192 * (len % 16 - row) - 12 * c - 3
  | .gst _ row c j => 2 + 192 * (len % 16 - row) - 12 * c - 4 - j.val
  | .bwait t => if t < len / 16 then 20 * (len / 16 - t) + partEv len - 18 else 2
  | .arrive t => if t < len / 16 then 20 * (len / 16 - t) + partEv len - 19 else 1

/-- **The counted events left in the phase, read off the state**: the site gives the kind of
position and the index of a tensor store or of a global store; `%r1806` the tile, `%r1809` the
row and `%r1811` (8 times the chunk) the place in a partial tile. -/
def leftOf (P : Params) (g : Nat) (d : D) : Nat :=
  let len := P.length (seqOf P g)
  let t := (d.w 2112).toNat
  let row := (d.w 2115).toNat
  let c := (d.w 2117).toNat / 8
  match d.site with
  | .bar _ => if lane g = 0 ∧ 1 ≤ len then 1 + 20 * (len / 16) + partEv len else 1
  | .mbarWait _ => 20 * (len / 16 - t) + partEv len
  | .tensorCopy i => 20 * (len / 16 - t) + partEv len - 1 - (i.val - 226)
  | .bulkCommit _ => 20 * (len / 16 - t) + partEv len - 17
  | .load _ => 2 + 192 * (len % 16 - row) - 12 * c
  | .loadEl1 _ _ => 2 + 192 * (len % 16 - row) - 12 * c - 1
  | .loadEl2 _ _ _ => 2 + 192 * (len % 16 - row) - 12 * c - 2
  | .loadEl3 _ _ _ _ => 2 + 192 * (len % 16 - row) - 12 * c - 3
  | .store j => 2 + 192 * (len % 16 - row) - 12 * c - 4 - (j.val - 10)
  | .bulkWait _ => if t < len / 16 then 20 * (len / 16 - t) + partEv len - 18 else 2
  | .mbarArrive _ => if t < len / 16 then 20 * (len / 16 - t) + partEv len - 19 else 1
  | _ => 0

/-- **The tile index read off a state is the tile of its position.** -/
theorem tileOf_eq (hpre : Pre P L mem0) {pos : Pos} {d : D} (hr : RefAt P g pos d) :
    tileOf d = pos.tile := by
  obtain ⟨site, w, p, x⟩ := d
  have hs : site = pos.site := hr.site
  by_cases hp : pos = .entry
  · subst hp
    subst hs
    rfl
  · have h := tile_reg hpre hr hp
    subst hs
    cases pos <;> first | exact absurd rfl hp | exact h

/-- **The counted events left read off a state are those of its position.** -/
theorem leftOf_eq (hpre : Pre P L mem0) {pos : Pos} {d : D} (hr : RefAt P g pos d) :
    leftOf P g d = leftAt (P.length (seqOf P g)) (lane g = 0 ∧ 1 ≤ P.length (seqOf P g)) pos := by
  obtain ⟨site, w, p, x⟩ := d
  have hs : site = pos.site := hr.site
  by_cases hp : pos = .entry
  · subst hp
    subst hs
    rfl
  · have h := tile_reg hpre hr hp
    have hrow : ∀ {t row c n : Nat}, InChunk t row c n pos →
        (w 2115).toNat = row ∧ (w 2117).toNat / 8 = c := by
      intro t row c n hc
      obtain ⟨hpart, hrw, hcc, k2115, -, k2117, -⟩ := row_of hr hc
      dsimp only at k2115 k2117
      rw [k2115, k2117, toNat_W (by omega), toNat_W (by omega)]
      exact ⟨rfl, by omega⟩
    subst hs
    cases pos with
    | entry => exact absurd rfl hp
    | wait t => simp only [leftOf, leftAt, Pos.site, Pos.tile] at h ⊢; rw [h]
    | ts t i =>
      simp only [leftOf, leftAt, Pos.site, Pos.tile] at h ⊢
      rw [h, Nat.add_sub_cancel_left]
    | commit t => simp only [leftOf, leftAt, Pos.site, Pos.tile] at h ⊢; rw [h]
    | ld0 t row c =>
      obtain ⟨h1, h2⟩ := hrow (t := t) (row := row) (c := c) (n := 0) ⟨rfl, rfl, rfl, rfl⟩
      simp only [leftOf, leftAt, Pos.site] at h1 h2 ⊢
      rw [h1, h2]
    | ld1 t row c v0 =>
      obtain ⟨h1, h2⟩ := hrow (t := t) (row := row) (c := c) (n := 1) ⟨rfl, rfl, rfl, rfl⟩
      simp only [leftOf, leftAt, Pos.site] at h1 h2 ⊢
      rw [h1, h2]
    | ld2 t row c v0 v1 =>
      obtain ⟨h1, h2⟩ := hrow (t := t) (row := row) (c := c) (n := 2) ⟨rfl, rfl, rfl, rfl⟩
      simp only [leftOf, leftAt, Pos.site] at h1 h2 ⊢
      rw [h1, h2]
    | ld3 t row c v0 v1 v2 =>
      obtain ⟨h1, h2⟩ := hrow (t := t) (row := row) (c := c) (n := 3) ⟨rfl, rfl, rfl, rfl⟩
      simp only [leftOf, leftAt, Pos.site] at h1 h2 ⊢
      rw [h1, h2]
    | gst t row c j =>
      obtain ⟨h1, h2⟩ := hrow (t := t) (row := row) (c := c) (n := 4 + j.val)
        ⟨rfl, rfl, rfl, rfl⟩
      simp only [leftOf, leftAt, Pos.site] at h1 h2 ⊢
      rw [h1, h2, Nat.add_sub_cancel_left]
    | bwait t => simp only [leftOf, leftAt, Pos.site, Pos.tile] at h ⊢; rw [h]
    | arrive t => simp only [leftOf, leftAt, Pos.site, Pos.tile] at h ⊢; rw [h]

/-- **A step of the positions lowers the counted events left by one**, except the repetition of
a poll, which keeps them. -/
theorem left_step (hpre : Pre P L mem0) {pos pos' : Pos} {d d' : D}
    (hr : RefAt P g pos d) (hr' : RefAt P g pos' d')
    (hs : Step (P.length (seqOf P g)) pos pos') :
    leftAt (P.length (seqOf P g)) (lane g = 0 ∧ 1 ≤ P.length (seqOf P g)) pos' + 1 =
        leftAt (P.length (seqOf P g)) (lane g = 0 ∧ 1 ≤ P.length (seqOf P g)) pos ∨
      (pos' = pos ∧ ∃ t, pos = .wait t) := by
  obtain ⟨b1, b2, b3⟩ := len_facts hpre g
  have hp' : ∀ {t : Nat}, pos'.tile = t → pos' ≠ .entry → t < tiles (P.length (seqOf P g)) :=
    fun ht hne => ht ▸ (lead_of hr' hne).2
  cases hs with
  | entry =>
    left
    obtain ⟨hl, ht⟩ := lead_of hr' (by intro h; cases h)
    have hlen : 1 ≤ P.length (seqOf P g) := by
      simp only [Pos.tile] at ht
      omega
    simp only [leftAt, hl, hlen, and_self, ↓reduceIte]
    omega
  | retry t => exact .inr ⟨rfl, t, rfl⟩
  | full t h =>
    left
    simp only [leftAt, partEv, finVal]
    split_ifs <;> omega
  | part t h =>
    left
    have ht := (lead_of hr (by intro h; cases h)).2
    simp only [Pos.tile] at ht
    simp only [leftAt, partEv]
    split_ifs <;> omega
  | ts t i i' h =>
    left
    have hfull : 16 * t + 16 ≤ P.length (seqOf P g) := hr.pos.2.1
    have hi := i'.isLt
    simp only [leftAt, partEv]
    split_ifs <;> omega
  | commit t =>
    left
    have hfull : 16 * t + 16 ≤ P.length (seqOf P g) := hr.pos.2.1
    simp only [leftAt, partEv, finVal]
    split_ifs <;> omega
  | cwait t h =>
    left
    simp only [leftAt, partEv]
    split_ifs <;> omega
  | ld0 t row c v =>
    left
    obtain ⟨hpart, hrow, hc, -⟩ := hr.pos.2
    simp only [leftAt]
    omega
  | ld1 t row c v0 v =>
    left
    obtain ⟨hpart, hrow, hc, -⟩ := hr.pos.2
    simp only [leftAt]
    omega
  | ld2 t row c v0 v1 v =>
    left
    obtain ⟨hpart, hrow, hc, -⟩ := hr.pos.2
    simp only [leftAt]
    omega
  | ld3 t row c v0 v1 v2 =>
    left
    obtain ⟨hpart, hrow, hc, -⟩ := hr.pos.2
    simp only [leftAt, finVal]
    omega
  | gst t row c j j' h =>
    left
    obtain ⟨hpart, hrow, hc, -⟩ := hr.pos.2
    have hj := j'.isLt
    simp only [leftAt]
    omega
  | chunk t row c h =>
    left
    obtain ⟨hpart, hrow, hc, -⟩ := hr.pos.2
    simp only [leftAt, finVal]
    omega
  | row t row c hc h =>
    left
    obtain ⟨hpart, hrow, -, -⟩ := hr.pos.2
    simp only [leftAt, finVal]
    omega
  | last t row c hc h hp =>
    left
    simp only [leftAt, finVal]
    split_ifs <;> omega
  | bwait t =>
    left
    have ht := (lead_of hr (by intro h; cases h)).2
    simp only [Pos.tile] at ht
    simp only [leftAt, partEv]
    split_ifs <;> omega
  | next t h =>
    left
    simp only [leftAt, partEv]
    split_ifs <;> omega

/-- **At the exit nothing of the phase is left**: a position from which the phase is left has
one counted event left, its own. -/
theorem left_done {pos : Pos} {d d' : D} {δ : Led} (hr : RefAt P g pos d)
    (hx : pos.canExit) (hd : Done P g pos δ d')
    (hδ : δ = dBar ∨ ∃ o, δ = dArr o) :
    leftAt (P.length (seqOf P g)) (lane g = 0 ∧ 1 ≤ P.length (seqOf P g)) pos = 1 := by
  obtain ⟨-, hl⟩ := hd
  cases pos with
  | entry =>
    by_cases hlead : lane g = 0 ∧ 1 ≤ P.length (seqOf P g)
    · exfalso
      rw [ledExit_lead hlead.1 hlead.2] at hl
      have h0 := congrArg Led.pollF0 hl
      have hlen := hlead.2
      rcases hδ with rfl | ⟨o, rfl⟩ <;>
        simp only [led, ledEntry, dBar, dArr, Led.add_def, tiles] at h0 <;> omega
    · simp only [leftAt, hlead, ↓reduceIte]
  | arrive t =>
    have hp : Pos.arrive t ≠ .entry := by intro h; cases h
    obtain ⟨hl0, ht⟩ := lead_of hr hp
    simp only [Pos.tile] at ht
    have hlen : 1 ≤ P.length (seqOf P g) := by
      unfold tiles at ht
      omega
    rw [ledExit_lead hl0 hlen] at hl
    have h0 := congrArg Led.arrE0 hl
    have h1 := congrArg Led.arrE1 hl
    have ha := led_arr (len := P.length (seqOf P g)) hp
    simp only [Led.add_def, ha.1, ha.2, Pos.tile] at h0 h1
    have hsum : tiles (P.length (seqOf P g)) = t + 1 := by
      rcases hδ with rfl | ⟨o, rfl⟩
      · simp only [dBar] at h0 h1
        omega
      · simp only [dArr] at h0 h1
        split_ifs at h0 h1 <;> omega
    unfold tiles at hsum
    simp only [leftAt, partEv]
    split_ifs <;> omega
  | _ => exact hx.elim

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads)
include hpre hX hg

omit hX hg in
/-- **Fields `tile_le`, `tile_start`, `arrStoreEmpty`** at a state of the phase: the tile index
is at most the tile count, it is 0 at instruction 1402, and for each output stage the thread
has arrived on `storeEmpty` once per tile of the stage below the tile index. -/
theorem tileIdx_store {k : Nat} {s : D} (hI : Inv P X g k s) :
    tileOf s ≤ tiles (P.length (seqOf P g)) ∧ (s.site.pc ≤ 1402 → tileOf s = 0) ∧
      ∀ o : Fin 2, uses 2 (tileOf s) o.val ≤
        arrivals ((Bar.storeEmpty o).loc L (g / L.block)) ((X.tr g).take k) := by
  obtain ⟨pos, hr, hl⟩ := hI
  rw [tileOf_eq hpre hr]
  by_cases hp : pos = .entry
  · subst hp
    refine ⟨Nat.zero_le _, fun _ => rfl, fun o => ?_⟩
    have := o.isLt
    simp only [Pos.tile, uses]
    omega
  · refine ⟨Nat.le_of_lt (lead_of hr hp).2, fun h => ?_, fun o => ?_⟩
    · rw [hr.site] at h
      rcases site_pc pos with ⟨h1, -⟩ | ⟨-, h1, -⟩
      · exact absurd h1 hp
      · omega
    · rw [((counts_at hpre (L := L) hp hl).2.2 o).2]

omit hpre hX hg in
/-- **Field `bar0`** at a state of the phase: the thread's `bar.sync 0` so far are the
`bar.sync 0` instructions below its instruction (five at 1402, six in the loop). -/
theorem bar0_store {k : Nat} {s : D} (hI : Inv P X g k s) :
    ((X.tr g).take k).countP (Execution.isBarId 0) =
      (bar0Pcs.filter (· < s.site.pc)).length := by
  obtain ⟨pos, hr, hl⟩ := hI
  have hb : ((X.tr g).take k).countP (Execution.isBarId 0) = _ := congrArg Led.bars hl
  rw [hb, hr.site]
  rcases site_pc pos with ⟨rfl, -⟩ | ⟨hp, h1, h2⟩
  · rfl
  · rw [led_bars hp]
    have e1 : decide (85 < pos.site.pc) = true := decide_eq_true (by omega)
    have e2 : decide (110 < pos.site.pc) = true := decide_eq_true (by omega)
    have e3 : decide (379 < pos.site.pc) = true := decide_eq_true (by omega)
    have e4 : decide (620 < pos.site.pc) = true := decide_eq_true (by omega)
    have e5 : decide (621 < pos.site.pc) = true := decide_eq_true (by omega)
    have e6 : decide (1402 < pos.site.pc) = true := decide_eq_true (by omega)
    have e7 : decide (3113 < pos.site.pc) = false := decide_eq_false (by omega)
    have e8 : decide (3775 < pos.site.pc) = false := decide_eq_false (by omega)
    have e9 : decide (3834 < pos.site.pc) = false := decide_eq_false (by omega)
    simp [bar0Pcs, List.filter, e1, e2, e3, e4, e5, e6, e7, e8, e9]

omit hpre hX hg in
/-- **Field `bar0`** at the exit of the phase (instruction 3113): six `bar.sync 0`. -/
theorem bar0_out {k : Nat} {s : D} (ho : Out P X g k s) :
    ((X.tr g).take k).countP (Execution.isBarId 0) =
      (bar0Pcs.filter (· < s.site.pc)).length := by
  have hb : ((X.tr g).take k).countP (Execution.isBarId 0) = _ := congrArg Led.bars ho.2
  rw [hb, ledExit_bars, ho.1.site]
  rfl

omit hX in
/-- **Fields `poll` and `pollStage`** at a poll state of the phase: the tile `t` is below the
tile count; the polled mbarrier is `Bar.storeFull` of stage `t % 2` of the thread's block; the
thread is the store leader; its successful polls of that mbarrier are `uses 2 t (t % 2)`; the
instruction is past 1402; and every wait event that a concrete state of this state can fire is
on that mbarrier, with the parity of those polls. -/
theorem poll_store {k : Nat} {s : D} {j : Fin 10} (hI : Inv P X g k s)
    (hs : s.site = .mbarWait j) :
    ∃ t, RefAt P g (.wait t) s ∧ tileOf s = t ∧ t < tiles (P.length (seqOf P g)) ∧
      g = storeLeader L (g / L.block) ∧ 1402 < s.site.pc ∧
      okPolls ((Bar.storeFull (stageOf t)).loc L (g / L.block)) ((X.tr g).take k) =
        uses 2 t (stageOf t).val ∧
      ∀ {tt : TState} {ins : Instr} {e : Event} {o : Option TState},
        (code L g).AtD s tt → kernel.code[s.site.pc]? = some ins →
        Fires s.site.pc (eventTmpl Assumptions.all L g tt ins.op) e o →
        ∀ l q ok acq sc, e.kind = .wait l q ok acq sc →
          l = (Bar.storeFull (stageOf t)).loc L (g / L.block) ∧
            q % 2 = okPolls l ((X.tr g).take k) % 2 := by
  obtain ⟨pos, hr, hl⟩ := hI
  obtain ⟨t, rfl⟩ : ∃ t, pos = .wait t := by
    have h := hr.site.symm.trans hs
    cases pos <;> first | exact ⟨_, rfl⟩ | exact absurd h (by simp [Pos.site])
  have hp : Pos.wait t ≠ .entry := by intro h; cases h
  obtain ⟨-, -, hc⟩ := counts_at hpre (L := L) hp hl
  have hpoll := (hc (stageOf t)).1
  simp only [Pos.tile, Pos.polled, Nat.add_zero] at hpoll
  refine ⟨t, hr, tileOf_eq hpre hr, (lead_of hr hp).2, leader_at hpre hr hp, ?_, hpoll, ?_⟩
  · rw [hr.site]
    show (1402 : Nat) < (Site.mbarWait 9).pc
    decide
  · intro tt ins e o hat hcode hf l q ok acq sc hk
    obtain ⟨site, w, p, x⟩ := s
    obtain rfl : site = (Pos.wait t).site := hr.site
    obtain ⟨ok', rfl⟩ := ev_at hpre hg (.wait t) hr hat hcode hf
    cases hk
    have hm : fullBar P g (t % 2) = (Bar.storeFull (stageOf t)).loc L (g / L.block) :=
      fullBar_eq hpre g (stageOf t)
    rw [hm, hpoll]
    refine ⟨rfl, ?_⟩
    simp only [uses, stageOf_val]
    omega

/-- **Field `barStep`** for the one barrier of the phase: a barrier event at a state of the
phase is fired at the entry (instruction 1402, sub-step 0, tile index 0); the successor of the
machine is at a later instruction, and it is the poll of tile 0 (the store leader of a nonempty
sequence) or the exit state at instruction 3113 (every other thread of the store warp). -/
theorem barStep_store {k pc id : Nat} {cnt : Option Nat} {m : BarMode} {s s' : D}
    (he : X.get (g, k) = some ⟨pc, .bar id cnt m⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k s)
    (hn : Thread.next L g s ⟨pc, .bar id cnt m⟩ = some (some s')) :
    s.site.pc = 1402 ∧ s.site.sub = 0 ∧ tileOf s = 0 ∧ s.site.pc < s'.site.pc ∧
      ((RefAt P g (.wait 0) s' ∧ tileOf s' = 0) ∨
        (¬ (lane g = 0 ∧ 1 ≤ P.length (seqOf P g)) ∧ Exit P g s')) := by
  obtain ⟨pos, hr, hl, hev, -⟩ := store_good hpre hX hg he hσ hI
  obtain ⟨rfl, -⟩ := ev_bar_inv hev
  have ht0 := tileOf_eq hpre hr
  obtain ⟨site, w, p, x⟩ := s
  obtain rfl : site = (Pos.entry).site := hr.site
  refine ⟨rfl, rfl, ht0, ?_⟩
  rcases step_at hpre hg .entry hr hn with ⟨pos', h1, h2, h3⟩ | ⟨-, hE, hx⟩
  · cases h3
    refine ⟨?_, .inl ⟨h1, tileOf_eq hpre h1⟩⟩
    rw [h1.site]
    show (Site.bar 5).pc < (Site.mbarWait 9).pc
    decide
  · refine ⟨?_, .inr ⟨fun hlead => ?_, hE⟩⟩
    · rw [hE.site]
      show (Site.bar 5).pc < (Site.bar 7).pc
      decide
    · rw [ledExit_lead hlead.1 hlead.2] at hx
      have h0 := congrArg Led.pollF0 hx
      have hlen := hlead.2
      simp only [led, ledEntry, evDelta, dBar, Led.add_def, tiles] at h0
      omega

omit hX in
/-- **Field `left_dec`**: a step of the machine from a state of the phase lowers the counted
events left in the phase (`leftOf`) by the count of the event (1, or 0 for a failed poll); the
successor is a state of a position of the phase, or the exit state, before which exactly one
counted event of the phase was left. -/
theorem leftOf_dec {k : Nat} {s s' : D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k s)
    (hn : Thread.next L g s e = some (some s')) :
    ((∃ pos', RefAt P g pos' s') ∧
        leftOf P g s' + (if e.counts then 1 else 0) ≤ leftOf P g s) ∨
      (Exit P g s' ∧ leftOf P g s = 1) := by
  obtain ⟨pos, hr, hl⟩ := hI
  have hleft := leftOf_eq hpre hr
  obtain ⟨site, w, p, x⟩ := s
  obtain rfl : site = pos.site := hr.site
  rcases step_at hpre hg pos hr hn with ⟨pos', h1, h2, h3⟩ | ⟨hx, hd⟩
  · left
    refine ⟨⟨pos', h1⟩, ?_⟩
    rw [leftOf_eq hpre h1, hleft]
    rcases left_step hpre hr h1 h3 with h | ⟨rfl, t, rfl⟩
    · split_ifs <;> omega
    · -- a poll that leads back to itself has failed
      have hn' := (next_mbarWait_9 (L := L) (g := g) _ _ _ _).symm.trans hn
      obtain ⟨pc, kd⟩ := e
      cases kd <;> (try (simp at hn'; done))
      rename_i l q ok acq sc
      cases ok
      · simp [Event.counts]
      · exfalso
        have h0 := congrArg Led.pollF0 h2
        have h1' := congrArg Led.pollF1 h2
        simp only [led, evDelta, dPoll, Led.add_def] at h0 h1'
        split_ifs at h0 h1' <;> omega
  · right
    refine ⟨hd.1, ?_⟩
    rw [hleft]
    refine left_done hr hx hd ?_
    cases pos <;> first
      | exact hx.elim
      | exact .inl rfl
      | exact .inr ⟨_, rfl⟩

/-- **The states of the phase before a state of the phase**: the invariant holds at every
followed state from the entry up to a state with the invariant. -/
theorem inv_range {k0 k : Nat} {s : D} (hen : Entered P L X g k0)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P X g k s) :
    ∀ i si, k0 ≤ i → i < k → Frame.stateAt (code L) X g i = some (some si) →
      Inv P X g i si := by
  intro i si hi hik hσi
  obtain ⟨pos, hr, hl⟩ := hI
  by_cases hlen : i < (X.tr g).length
  · obtain ⟨si', hσi', hI'⟩ :=
      inv_before hpre hX hg hen hi (Nat.le_of_lt hik) hlen hσ hr hl
    obtain rfl : si' = si := Option.some.inj (Option.some.inj (hσi'.symm.trans hσi))
    exact hI'
  · have e1 : (X.tr g).take i = (X.tr g).take k := by
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
    have e2 : Frame.stateAt (code L) X g i = Frame.stateAt (code L) X g k := by
      rw [Frame.stateAt_of_le (by omega), Frame.stateAt_of_le (k := k) (by omega)]
    obtain rfl : s = si := Option.some.inj (Option.some.inj ((hσ.symm.trans e2.symm).trans hσi))
    exact ⟨pos, hr, by rw [e1]; exact hl⟩

omit hpre hX hg in
/-- A class that is false on the nine kinds of events of the phase is false on its events. -/
theorem quiet_of_kind {c : Event → Bool} (h : ∀ e, phaseKind e.kind → c e = false) :
    ∀ pos x e, EvX P g pos x e → c e = false :=
  fun _ _ e hev => h e (ev_kind hev)

/-- **The count of a class that the phase does not touch** is the same at a state of the phase
(or at its first exit) as at the entry: `hin` says that the followed states from `k0` up to `k`
have the invariant (`inv_range`, or the first exit of `Ref/Chain.lean: Phase.Traces.first`). -/
theorem frame_store {k0 k : Nat} {s : D} {c : Event → Bool} (hk0 : k0 ≤ k)
    (hσ : Frame.stateAt (code L) X g k = some (some s))
    (hin : ∀ i si, k0 ≤ i → i < k → Frame.stateAt (code L) X g i = some (some si) →
      Inv P X g i si)
    (hc : ∀ pos x e, EvX P g pos x e → c e = false) :
    ((X.tr g).take k).countP c = ((X.tr g).take k0).countP c := by
  refine countP_take_eq c hk0 fun i e hi hik he => ?_
  obtain ⟨si, hσi⟩ := followed_of_le hσ (Nat.le_of_lt hik)
  obtain ⟨pos, -, -, hev, -⟩ := store_good hpre hX hg he hσi (hin i si hi hik hσi)
  exact hc pos _ e hev

end

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Store
