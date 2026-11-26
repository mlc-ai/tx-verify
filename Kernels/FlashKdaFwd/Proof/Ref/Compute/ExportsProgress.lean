-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Compute.ExportsProgressSites
public import Kernels.FlashKdaFwd.Proof.Schedule.Contract
public import Kernels.FlashKdaFwd.Proof.Ref.Kinds

@[expose] public section

/-! # The Compute share of the progress contract

`Proof/Schedule/Contract.lean: RefProgress` is what the progress instance and the termination
bound need from the reference layer about a followed state `d` of a thread (the state of its
machine before its `k`-th event) and the counts over its earlier events. This file proves the
share of the Compute phase: a compute thread (thread index below 128 in its block) from its
`bar.sync 0` at instruction 1402 (the phase's entry) through the tile loop (instructions 2106
to 2944) up to, but without, its `bar.sync 0` at 3113 (the phase's exit; that state belongs to
the epilogue). Every statement is about a state with the phase invariant `Inv P L X g j0 k s`
(`Inv.lean`: the state is at a *position*, the entry or position `n < 268` of tile `t`, with the
position's registers, ledger and number of counted events since the entry at trace index `j0`),
and is written in the consumer's vocabulary (`siteCls`, `bar0Of`, `bar8Of`, `matBefore`,
`roundOf`, `pollerOf`, `collOf` of `Schedule/Defs.lean`), so that the assembly proves a field
on the states of this phase by one application. The theorems, by field:

* **The numbers** (`Nums.tile`, `Nums.left`). `tileOf P g d`: the tile index of a state of a
  compute thread, read off the state: 0 up to instruction 1402, the tile count from 3113 on,
  and in between the tile count minus what the loop counter `%r1800` still has to count (the
  register holds `2^32 - (T - t)` in tile `t`). `leftOf P g d`: the counted events (all events
  but failed polls) of the phase that the thread still has to make: `1 + 268 T` up to
  instruction 1402, none from 3113 on, and `268 (T - t) - n` at position `n` of tile `t`, with
  `n` read off the site (`posOf`). `tileOf_eq`, `leftOf_eq`: at a state of the phase they are
  the position's tile and `1 + 268 T` minus the position's count of events. `tilesOf_cta`: the
  tile count is the consumer's `ctaTiles`. `leftOf_start`, `leftOf_end`, `leftOf_entry`,
  `leftOf_exit`, `leftOf_le`: the values outside the tile loop, for the measure of the assembly.
* `tileOf_le`, `tileOf_start`, `tileOf_end`, `tile_matrix_compute`: fields `tile_le`,
  `tile_start` and `tile_end` (all three hold of `tileOf` at every state, by its definition)
  and `tile_matrix`.
* `bar0_compute`, `bar8_compute`, `matrix_compute`: the ledger fields `bar0`, `bar8`, `matrix`;
  `bar0_out`, `bar8_out`, `matrix_out`: the same at the exit state, with the tile count as
  the tile index.
* `arrLoadEmpty_compute`, `arrStoreFull_compute` (and `arr_out` at the exit): fields
  `arrLoadEmpty`, `arrStoreFull`. `not_leader`: a compute thread is neither the load leader nor
  the store leader, so `arrLoadFull`, `arrStoreEmpty` and `arrState` are vacuous for it.
* `poll_compute`, `pollStage_compute`: fields `poll` and `pollStage` at the two polls of a
  tile (the "empty" mbarrier of the tile's output stage at instruction 2144, the "full"
  mbarrier of its input stage at 2186).
* `region_compute`: field `region`. `not_coll_compute`, `not_exit_compute`: no state of the
  phase is at a shuffle, an election or the exit, so `collAt` is vacuous here; `exitAt` holds at
  every followed state by `Ref.exit_site_pc` and needs nothing of a phase.
* `barStep_compute`: field `barStep` for the two barriers of the phase (the `bar.sync 0` at
  1402 and the named barrier at 2913).
* `leftOf_dec`: field `left_dec` for every step from a state of the phase.
* `matrixShape_compute`, `matrixPrev_compute`: fields `matrixShape` and `matrixPrev`, about a
  thread's last state.
* `frame_compute`, `frame_out`, `coll_compute`, `coll_out`: a class of events that no kind of
  site of the phase can fire keeps its count from the entry to every state of the phase and to
  its first exit; field `coll` (shuffles and elections) is the instance the contract needs.
* `Ev`, `ev_at`: the event at a state of the phase, in closed form at the seven control
  positions and by its kind elsewhere. `Untouched`, `untouched_of`, `frame_ev`: the count
  transport for a class that none of these events belongs to, also when sites of the phase can
  fire events of the class on other objects; `state_counts_compute`, `state_counts_out`: the
  arrivals on, the tensor loads completing on and the successful polls of the state mbarrier
  (the classes of the field `arrState`) are those at the entry.
* `step_compute`, `inv_before`, `entry_le`: one step of the invariant with the counted events of
  both positions; before a state of the phase the thread has not left the phase.

Abbreviations: `T = tilesOf P g` is the number of tiles of the sequence of the thread's block;
a *followed state* at trace index `k` is `Frame.stateAt (code L) X g k = some (some s)`
(`At (code L) X g k s`); `c = g / L.block` is the thread's block. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Compute
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Sched (Unblocking isWarpColl)
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Protocol (Bar uses loadLeader storeLeader bar0Pcs ctaTiles)
open PTX.Kernels.FlashKdaFwd.Proof.Progress (siteCls kindCls siteCls_kind matBefore
  matBefore_eq op_of_matrix_kind bar0Of bar8Of collOf collPcs roundOf pollerOf)

noncomputable section
set_option maxRecDepth 8000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-! ### The tile index and the counted events left, read off a state -/

/-- The tile of a position: 0 at the entry. -/
def tileAt : Pos → Nat
  | .entry => 0
  | .tile t _ => t

/-- **The tile index of a state of a compute thread, read off the state**: 0 up to instruction
1402 (the startup and the entry of the phase); the tile count from instruction 3113 on (the
exit of the phase and the epilogue); in the tile loop the tile count minus what the loop
counter `%r1800` (register 2106, which holds `2^32 - (T - t)` in tile `t`) still has to
count. -/
def tileOf (P : Params) (g : Nat) (d : D) : Nat :=
  if d.site.pc ≤ 1402 then 0
  else if 3113 ≤ d.site.pc then tilesOf P g
  else tilesOf P g - (4294967296 - (d.w 2106).toNat)

/-- **The counted events of the phase that a compute thread at a state still has to make, read
off the state**: all of them, the barrier at 1402 and 268 per tile, up to instruction 1402;
none from instruction 3113 on; in the tile loop 268 per tile from the state's on, minus the
position of the state in its tile. -/
def leftOf (P : Params) (g : Nat) (d : D) : Nat :=
  if d.site.pc ≤ 1402 then 1 + 268 * tilesOf P g
  else if 3113 ≤ d.site.pc then 0
  else 268 * (tilesOf P g - tileOf P g d) - posOf d.site

/-- The tile count of the thread's block is the consumer's `ctaTiles P (g / L.block)`. -/
theorem tilesOf_cta (hpre : Pre P L mem0) (g : Nat) : tilesOf P g = ctaTiles P (g / L.block) := by
  simp only [tilesOf, seqOf, ctaTiles, hpre.block]

/-- The entry site, `bar_5`, is instruction 1402. -/
theorem entry_pc : (Site.bar 5).pc = 1402 := by decide

/-- The exit site, `bar_7`, is instruction 3113. -/
theorem exit_pc : (Site.bar 7).pc = 3113 := by decide

/-- The loop counter is among the registers of every position of a tile. -/
theorem counter_mem : ∀ n < 268, 2106 ∈ regKeys.take (cntOf n) := by decide +kernel

/-- **Field `tile_start`**: the tile index is 0 up to instruction 1402. -/
theorem tileOf_start {d : D} (h : d.site.pc ≤ 1402) : tileOf P g d = 0 := by
  simp only [tileOf, h, ↓reduceIte]

/-- **Field `tile_end`**: the tile index is the tile count from instruction 3113 on. -/
theorem tileOf_end {d : D} (h : 3113 ≤ d.site.pc) : tileOf P g d = tilesOf P g := by
  unfold tileOf
  rw [ite_eq_right (by omega), ite_eq_left h]

/-- **Field `tile_le`**: the tile index read off any state is at most the tile count. -/
theorem tileOf_le (P : Params) (g : Nat) (d : D) : tileOf P g d ≤ tilesOf P g := by
  unfold tileOf
  split_ifs <;> omega

/-- At the exit state of the phase the tile index is the tile count. -/
theorem tileOf_exit {d : D} (h : Exit P g d) : tileOf P g d = tilesOf P g :=
  tileOf_end (by rw [h.site, exit_pc])

/-- **The tile index read off a state of the phase is the tile of its position.** -/
theorem tileOf_eq (hpre : Pre P L mem0) {pos : Pos} {d : D} (hr : RefAt P L g pos d) :
    tileOf P g d = tileAt pos := by
  cases pos with
  | entry =>
    have hs : d.site = .bar 5 := hr.site
    simp only [tileOf, hs, entry_pc, le_refl, ↓reduceIte, tileAt]
  | tile t n =>
    have hf : Tile P L g t n d.w d.p d.x := hr.facts
    have hp := pc_tab n hf.pos
    have hpc : d.site.pc = pcOf n := pc_at hr.site
    have hT := tiles_lt hpre g (P := P)
    have hlt := hf.lt
    have hw : d.w 2106 = W (4294967296 - (tilesOf P g - t)) :=
      hf.regs 2106 (counter_mem n hf.pos)
    have hn : (d.w 2106).toNat = 4294967296 - (tilesOf P g - t) := by
      rw [hw, toNat_W (by omega)]
    simp only [tileOf, tileAt, hpc]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), hn]
    omega

/-- The counted events since the entry at a position are fewer than those of the phase. -/
theorem idx_le {pos : Pos} {d : D} (hr : RefAt P L g pos d) :
    pos.idx ≤ 268 * tilesOf P g := by
  cases pos with
  | entry => exact Nat.zero_le _
  | tile t n =>
    have hf : Tile P L g t n d.w d.p d.x := hr.facts
    have hlt := hf.lt
    have hpos := hf.pos
    simp only [Pos.idx]
    omega

/-- **The counted events left read off a state of the phase**: those of the whole phase
(`1 + 268 T`) minus those since the entry. -/
theorem leftOf_eq (hpre : Pre P L mem0) {pos : Pos} {d : D} (hr : RefAt P L g pos d) :
    leftOf P g d = 1 + 268 * tilesOf P g - pos.idx := by
  have ht := tileOf_eq hpre hr
  cases pos with
  | entry =>
    have hs : d.site = .bar 5 := hr.site
    simp only [leftOf, hs, entry_pc, le_refl, ↓reduceIte, Pos.idx, Nat.sub_zero]
  | tile t n =>
    have hf : Tile P L g t n d.w d.p d.x := hr.facts
    have hp := pc_tab n hf.pos
    have hpc : d.site.pc = pcOf n := pc_at hr.site
    have hlt := hf.lt
    have hpos := hf.pos
    simp only [leftOf, ht, tileAt, hpc, posOf_eq hf.pos hr.site, Pos.idx]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    omega

/-! ### Where the states of the phase are -/

section
variable {j0 k : Nat} {s : D}

/-- A state of the phase is at or after the entry. -/
theorem entry_le (hI : Inv P L X g j0 k s) : j0 ≤ k := by
  obtain ⟨-, -, -, h, -⟩ := hI
  exact h

/-- A thread with a state of the phase is a compute thread. -/
theorem compute_of_inv (hI : Inv P L X g j0 k s) : tid g < 128 := by
  obtain ⟨pos, hr, -⟩ := hI
  cases pos with
  | entry => exact (show Entry P g s from hr.facts).compute
  | tile t n => exact (show Tile P L g t n s.w s.p s.x from hr.facts).compute

/-- **The instruction of a state of the phase**: 1402 (the entry) or one of the tile loop, from
the first poll (2144) to the second arrival (2928). -/
theorem site_compute (hI : Inv P L X g j0 k s) :
    s.site.pc = 1402 ∨ (2144 ≤ s.site.pc ∧ s.site.pc ≤ 2928) := by
  obtain ⟨pos, hr, -⟩ := hI
  cases pos with
  | entry =>
    have hs : s.site = .bar 5 := hr.site
    exact .inl (by rw [hs, entry_pc])
  | tile t n =>
    have hp := pc_tab n (show Tile P L g t n s.w s.p s.x from hr.facts).pos
    rw [← pc_at hr.site] at hp
    exact .inr ⟨hp.1, hp.2.1⟩

/-- **Field `region`** at a state of the phase: it is at instruction 1402 or in the compute loop
(2106 to 2944), and its thread is a compute thread. -/
theorem region_compute (hpre : Pre P L mem0) (hI : Inv P L X g j0 k s) :
    (1402 < s.site.pc → s.site.pc ≤ 2105 → 128 ≤ g % L.block ∧ g % L.block < 160) ∧
      (2105 < s.site.pc → s.site.pc ≤ 2944 → g % L.block < 128) ∧
      (2944 < s.site.pc → s.site.pc ≤ 3112 → 160 ≤ g % L.block) := by
  have hc := compute_of_inv hI
  have hs := site_compute hI
  rw [block_mod hpre]
  refine ⟨fun h1 h2 => ?_, fun _ _ => hc, fun h1 h2 => ?_⟩ <;> omega

/-- The kind of the site of a state of the phase: a `bar.sync` at the entry, the kind of the
position's site in the tile loop. -/
theorem kind_compute (hI : Inv P L X g j0 k s) :
    s.site.kind = .bar ∨ ∃ n < 268, s.site.kind = kindOf n := by
  obtain ⟨pos, hr, -⟩ := hI
  cases pos with
  | entry =>
    have hs : s.site = .bar 5 := hr.site
    exact .inl (by rw [hs]; rfl)
  | tile t n =>
    exact .inr ⟨n, (show Tile P L g t n s.w s.p s.x from hr.facts).pos, kind_at hr.site⟩

/-- **No state of the phase is at a shuffle or an election** (field `collAt` is vacuous in the
phase). -/
theorem not_coll_compute (hI : Inv P L X g j0 k s) : siteCls s.site ≠ .coll := by
  rw [siteCls_kind]
  rcases kind_compute hI with h | ⟨n, hn, h⟩
  · rw [h]
    decide
  · rw [h]
    exact (kind_tab n hn).1

/-- **No state of the phase is at the exit.** (Field `exitAt` needs nothing of a phase: an exit
event is fired at instruction 3835 from every followed state, `Ref.exit_site_pc`.) -/
theorem not_exit_compute (hI : Inv P L X g j0 k s) : s.site.kind ≠ .exit := by
  rcases kind_compute hI with h | ⟨n, hn, h⟩
  · rw [h]
    decide
  · rw [h]
    exact (kind_tab n hn).2.1

/-! ### The tile index -/

/-- **Field `tile_matrix`** at a state of the phase: a state at a matrix event belongs to a
compute thread inside a tile. -/
theorem tile_matrix_compute (hpre : Pre P L mem0) (hI : Inv P L X g j0 k s)
    (hm : siteCls s.site = .matrix) : g % L.block < 128 ∧ tileOf P g s < tilesOf P g := by
  have hc := compute_of_inv hI
  obtain ⟨pos, hr, -⟩ := hI
  rw [block_mod hpre, tileOf_eq hpre hr]
  refine ⟨hc, ?_⟩
  cases pos with
  | entry =>
    have hs : s.site = .bar 5 := hr.site
    rw [hs] at hm
    cases hm
  | tile t n => exact (show Tile P L g t n s.w s.p s.x from hr.facts).lt

/-- Up to instruction 1402 all counted events of the phase are left: the barrier at 1402 and
268 per tile. -/
theorem leftOf_start {d : D} (h : d.site.pc ≤ 1402) :
    leftOf P g d = 1 + 268 * tilesOf P g := by
  simp only [leftOf, h, ↓reduceIte]

/-- From instruction 3113 on no counted event of the phase is left. -/
theorem leftOf_end {d : D} (h : 3113 ≤ d.site.pc) : leftOf P g d = 0 := by
  unfold leftOf
  rw [ite_eq_right (by omega), ite_eq_left h]

/-- The counted events left at the entry state of the phase. -/
theorem leftOf_entry {d : D} (h : Entry P g d) : leftOf P g d = 1 + 268 * tilesOf P g :=
  leftOf_start (by rw [h.site, entry_pc])

/-- The counted events left at the exit state of the phase: none. -/
theorem leftOf_exit {d : D} (h : Exit P g d) : leftOf P g d = 0 :=
  leftOf_end (by rw [h.site, exit_pc])

/-- At every state of the phase at most `1 + 268 T` counted events are left. -/
theorem leftOf_le (hpre : Pre P L mem0) (hI : Inv P L X g j0 k s) :
    leftOf P g s ≤ 1 + 268 * tilesOf P g := by
  obtain ⟨pos, hr, -⟩ := hI
  rw [leftOf_eq hpre hr]
  omega

end

/-! ### The ledger, count by count -/

/-- The counts of a ledger of the tile loop (`ledAt`), in the terms of the contracts. -/
theorem ledAt_read {c : Nat} {es : List Event} {a b n c' d m : Nat}
    (h : ledOf L c es = ledAt a b n c' d m) :
    es.countP (Execution.isBarId 0) = 6 ∧ es.countP (Execution.isBarId 8) = n ∧
      es.countP isMatrix = m ∧
      (∀ o : Fin 2, okPolls ((Bar.storeEmpty o).loc L c) es = uses 2 a o.val) ∧
      (∀ st : Fin 3, okPolls ((Bar.loadFull st).loc L c) es = uses 3 b st.val) ∧
      (∀ o : Fin 2, arrivals ((Bar.storeFull o).loc L c) es = uses 2 c' o.val) ∧
      ∀ st : Fin 3, arrivals ((Bar.loadEmpty st).loc L c) es = uses 3 d st.val := by
  refine ⟨congrArg Led.bar0 h, congrArg Led.bar8 h, congrArg Led.mats h, fun o => ?_,
    fun st => ?_, fun o => ?_, fun st => ?_⟩
  · fin_cases o
    · exact congrArg Led.pe0 h
    · exact congrArg Led.pe1 h
  · fin_cases st
    · exact congrArg Led.pf0 h
    · exact congrArg Led.pf1 h
    · exact congrArg Led.pf2 h
  · fin_cases o
    · exact congrArg Led.af0 h
    · exact congrArg Led.af1 h
  · fin_cases st
    · exact congrArg Led.ae0 h
    · exact congrArg Led.ae1 h
    · exact congrArg Led.ae2 h

/-- The counts of the ledger at the entry, in the terms of the contracts. -/
theorem ledEntry_read {c : Nat} {es : List Event} (h : ledOf L c es = ledEntry) :
    es.countP (Execution.isBarId 0) = 5 ∧ es.countP (Execution.isBarId 8) = 0 ∧
      es.countP isMatrix = 0 ∧
      (∀ o : Fin 2, arrivals ((Bar.storeFull o).loc L c) es = 0) ∧
      ∀ st : Fin 3, arrivals ((Bar.loadEmpty st).loc L c) es = 0 := by
  refine ⟨congrArg Led.bar0 h, congrArg Led.bar8 h, congrArg Led.mats h, fun o => ?_,
    fun st => ?_⟩
  · fin_cases o
    · exact congrArg Led.af0 h
    · exact congrArg Led.af1 h
  · fin_cases st
    · exact congrArg Led.ae0 h
    · exact congrArg Led.ae1 h
    · exact congrArg Led.ae2 h

/-- Six `bar.sync 0` instructions lie below an instruction from 1403 to 3113. -/
theorem bar0Of_mid {pc : Nat} (h1 : 1402 < pc) (h2 : pc ≤ 3113) : bar0Of pc = 6 := by
  have e1 : decide (85 < pc) = true := decide_eq_true (by omega)
  have e2 : decide (110 < pc) = true := decide_eq_true (by omega)
  have e3 : decide (379 < pc) = true := decide_eq_true (by omega)
  have e4 : decide (620 < pc) = true := decide_eq_true (by omega)
  have e5 : decide (621 < pc) = true := decide_eq_true (by omega)
  have e6 : decide (1402 < pc) = true := decide_eq_true (by omega)
  have e7 : decide (3113 < pc) = false := decide_eq_false (by omega)
  have e8 : decide (3775 < pc) = false := decide_eq_false (by omega)
  have e9 : decide (3834 < pc) = false := decide_eq_false (by omega)
  simp [bar0Of, bar0Pcs, List.filter, e1, e2, e3, e4, e5, e6, e7, e8, e9]

/-- No matrix instruction lies below the entry. -/
theorem matBefore_entry : matBefore (.bar 5) = 0 := by
  rw [matBefore_eq (by rw [entry_pc]; omega), entry_pc]
  have h : (mxPcs.filter (· < 1402)).length = 0 := by decide +kernel
  rw [← mxPcs_eq, List.filter_map, List.length_map] at h
  exact h

/-- From the exit on the consumer counts no matrix event of a current tile. -/
theorem matBefore_exit : matBefore (.bar 7) = 0 := by
  unfold matBefore
  rw [ite_eq_left (by rw [exit_pc])]

section
variable {j0 k : Nat} {s : D}

/-- **Field `bar0`** at a state of the phase. -/
theorem bar0_compute (hI : Inv P L X g j0 k s) :
    ((X.tr g).take k).countP (Execution.isBarId 0) = bar0Of s.site.pc := by
  have hs := site_compute hI
  obtain ⟨pos, hr, hl, -⟩ := hI
  cases pos with
  | entry =>
    have hs : s.site = .bar 5 := hr.site
    rw [(ledEntry_read hl).1, hs, entry_pc]
    decide
  | tile t n =>
    have hp := pc_tab n (show Tile P L g t n s.w s.p s.x from hr.facts).pos
    rw [← pc_at hr.site] at hp
    rw [(ledAt_read hl).1, bar0Of_mid (by omega) (by omega)]

/-- **Field `bar0`** at the exit of the phase. -/
theorem bar0_out (ho : Out P L X g j0 k s) :
    ((X.tr g).take k).countP (Execution.isBarId 0) = bar0Of s.site.pc := by
  obtain ⟨he, hl, -⟩ := ho
  rw [(ledAt_read hl).1, he.site, exit_pc, bar0Of_mid (by omega) (by omega)]

/-- **Field `bar8`** at a state of the phase: one named barrier per finished tile, and the
current tile's from instruction 2914 on. -/
theorem bar8_compute (hpre : Pre P L mem0) (hI : Inv P L X g j0 k s) :
    ((X.tr g).take k).countP (Execution.isBarId 8) = bar8Of s.site.pc (tileOf P g s) := by
  obtain ⟨pos, hr, hl, -⟩ := hI
  rw [tileOf_eq hpre hr]
  cases pos with
  | entry =>
    have hs : s.site = .bar 5 := hr.site
    rw [(ledEntry_read hl).2.1, hs, entry_pc]
    rfl
  | tile t n =>
    have hp := pc_tab n (show Tile P L g t n s.w s.p s.x from hr.facts).pos
    rw [(ledAt_read hl).2.1, pc_at hr.site]
    simp only [bar8Of, tileAt, ind]
    split_ifs <;> omega

/-- **Field `bar8`** at the exit of the phase, where the tile index is the tile count. -/
theorem bar8_out (ho : Out P L X g j0 k s) :
    ((X.tr g).take k).countP (Execution.isBarId 8) = bar8Of s.site.pc (tileOf P g s) := by
  obtain ⟨he, hl, -⟩ := ho
  rw [(ledAt_read hl).2.1, tileOf_exit he, he.site, exit_pc]
  rfl

/-- **Field `matrix`** at a state of the phase: 182 matrix events per finished tile, and those
of the current tile before the state's site. -/
theorem matrix_compute (hpre : Pre P L mem0) (hI : Inv P L X g j0 k s) :
    ((X.tr g).take k).countP isMatrix = 182 * tileOf P g s + matBefore s.site := by
  obtain ⟨pos, hr, hl, -⟩ := hI
  rw [tileOf_eq hpre hr]
  cases pos with
  | entry =>
    have hs : s.site = .bar 5 := hr.site
    rw [(ledEntry_read hl).2.2.1, hs, matBefore_entry]
    rfl
  | tile t n =>
    rw [(ledAt_read hl).2.2.1,
      matBefore_at (show Tile P L g t n s.w s.p s.x from hr.facts).pos hr.site]
    rfl

/-- **Field `matrix`** at the exit of the phase, where the tile index is the tile count. -/
theorem matrix_out (ho : Out P L X g j0 k s) :
    ((X.tr g).take k).countP isMatrix = 182 * tileOf P g s + matBefore s.site := by
  obtain ⟨he, hl, -⟩ := ho
  rw [(ledAt_read hl).2.2.1, tileOf_exit he, he.site, matBefore_exit]
  rfl

/-- A stage of a two-stage pipeline is used at least as often among more tiles. -/
theorem uses2_mono {a b : Nat} (h : a ≤ b) (o : Nat) : uses 2 a o ≤ uses 2 b o := by
  unfold uses
  omega

/-- **Field `arrLoadEmpty`** at a state of the phase: one arrival on the "empty" mbarrier of an
input stage per finished tile of the stage. -/
theorem arrLoadEmpty_compute (hpre : Pre P L mem0) (hI : Inv P L X g j0 k s) (st : Fin 3) :
    uses 3 (tileOf P g s) st.val ≤
      arrivals ((Bar.loadEmpty st).loc L (g / L.block)) ((X.tr g).take k) := by
  obtain ⟨pos, hr, hl, -⟩ := hI
  rw [tileOf_eq hpre hr]
  cases pos with
  | entry =>
    rw [(ledEntry_read hl).2.2.2.2 st]
    have h3 := st.isLt
    simp only [tileAt, uses]
    omega
  | tile t n => exact le_of_eq ((ledAt_read hl).2.2.2.2.2.2 st).symm

/-- **Field `arrStoreFull`** at a state of the phase: one arrival on the "full" mbarrier of an
output stage per finished tile of the stage (and the current tile's from its second-last
event on). -/
theorem arrStoreFull_compute (hpre : Pre P L mem0) (hI : Inv P L X g j0 k s) (o : Fin 2) :
    uses 2 (tileOf P g s) o.val ≤
      arrivals ((Bar.storeFull o).loc L (g / L.block)) ((X.tr g).take k) := by
  obtain ⟨pos, hr, hl, -⟩ := hI
  rw [tileOf_eq hpre hr]
  cases pos with
  | entry =>
    rw [(ledEntry_read hl).2.2.2.1 o]
    have h2 := o.isLt
    simp only [tileAt, uses]
    omega
  | tile t n =>
    rw [(ledAt_read hl).2.2.2.2.2.1 o]
    exact uses2_mono (Nat.le_add_right _ _) _

/-- **Fields `arrLoadEmpty` and `arrStoreFull`** at the exit of the phase, where the tile index
is the tile count. -/
theorem arr_out (ho : Out P L X g j0 k s) :
    (∀ st : Fin 3, uses 3 (tileOf P g s) st.val ≤
        arrivals ((Bar.loadEmpty st).loc L (g / L.block)) ((X.tr g).take k)) ∧
      ∀ o : Fin 2, uses 2 (tileOf P g s) o.val ≤
        arrivals ((Bar.storeFull o).loc L (g / L.block)) ((X.tr g).take k) := by
  obtain ⟨he, hl, -⟩ := ho
  rw [tileOf_exit he]
  exact ⟨fun st => le_of_eq ((ledAt_read hl).2.2.2.2.2.2 st).symm,
    fun o => le_of_eq ((ledAt_read hl).2.2.2.2.2.1 o).symm⟩

end

/-- **A compute thread is neither the load leader nor the store leader of its block**, so the
fields `arrLoadFull`, `arrStoreEmpty` and `arrState` are vacuous for it. -/
theorem not_leader (hpre : Pre P L mem0) (hc : tid g < 128) :
    g ≠ loadLeader L (g / L.block) ∧ g ≠ storeLeader L (g / L.block) := by
  have hb := hpre.block
  have hm := Nat.div_add_mod g L.block
  simp only [loadLeader, storeLeader, Protocol.thr, tid] at hc ⊢
  rw [hb] at hm ⊢
  constructor <;> omega

/-! ### The two polls of a tile -/

/-- A site of the class of the polls is of the kind `mbarWait`. -/
theorem kind_of_poll {κ : SiteKind} (h : kindCls κ = .poll) : κ = .mbarWait := by
  cases κ <;> first | rfl | cases h

/-- The tiles before `t` that use the output stage of tile `t`. -/
theorem uses2_self (t : Nat) : uses 2 t (t % 2) = t / 2 := by
  unfold uses
  omega

/-- The tiles before `t` that use the input stage of tile `t`. -/
theorem uses3_self (t : Nat) : uses 3 t (t % 3) = t / 3 := by
  unfold uses
  omega

/-- **A poll state of the phase**, in closed form: it is in a tile `tl` (the tile index read
off the state), and it is the first poll, of the "empty" mbarrier of the tile's output stage,
which the thread has polled successfully `tl / 2` times, or the second poll, of the "full"
mbarrier of the tile's input stage, polled successfully `tl / 3` times; every event the state
can fire is that poll, with the parity the mbarrier has then. -/
theorem poll_fire (hpre : Pre P L mem0) {j0 k : Nat} {s : D} (hI : Inv P L X g j0 k s)
    (hp : siteCls s.site = .poll) :
    ∃ tl, tileOf P g s = tl ∧ tl < tilesOf P g ∧ 1402 < s.site.pc ∧
      ((okPolls ((Bar.storeEmpty (stage2 tl)).loc L (g / L.block)) ((X.tr g).take k) = tl / 2 ∧
        ∀ {t : TState} {ins : Instr} {e : Event} {o : Option TState},
          (code L g).AtD s t → kernel.code[s.site.pc]? = some ins →
          Fires s.site.pc (eventTmpl Assumptions.all L g t ins.op) e o →
          ∃ ok, e = ⟨2144, .wait ((Bar.storeEmpty (stage2 tl)).loc L (g / L.block))
            ((tl / 2 + 1) % 2) ok true .cta⟩) ∨
      (okPolls ((Bar.loadFull (stage3 tl)).loc L (g / L.block)) ((X.tr g).take k) = tl / 3 ∧
        ∀ {t : TState} {ins : Instr} {e : Event} {o : Option TState},
          (code L g).AtD s t → kernel.code[s.site.pc]? = some ins →
          Fires s.site.pc (eventTmpl Assumptions.all L g t ins.op) e o →
          ∃ ok, e = ⟨2186, .wait ((Bar.loadFull (stage3 tl)).loc L (g / L.block))
            (tl / 3 % 2) ok true .cta⟩)) := by
  have hsite := site_compute hI
  obtain ⟨pos, hr, hl, -⟩ := hI
  have ht := tileOf_eq hpre hr
  obtain ⟨site, w, p, x⟩ := s
  cases pos with
  | entry =>
    have hs : site = .bar 5 := hr.site
    rw [show (D.mk site w p x).site = site from rfl, hs] at hp
    cases hp
  | tile tl n =>
    have hf : Tile P L g tl n w p x := hr.facts
    have hat : (skOf n).At site := hr.site
    have hn : n ≤ 1 := wait_tab n hf.pos (kind_of_poll (by rw [← cls_at hat]; exact hp))
    have hpc : 1402 < (D.mk site w p x).site.pc := by
      have := pc_tab n hf.pos
      rw [show (D.mk site w p x).site.pc = pcOf n from pc_at hat]
      omega
    refine ⟨tl, ht, hf.lt, hpc, ?_⟩
    obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
    · obtain rfl : site = .mbarWait 7 := hat
      refine .inl ⟨?_, fun hat hc hfire => ev_pollE hpre hf hat hc hfire⟩
      rw [(ledAt_read hl).2.2.2.1 (stage2 tl)]
      exact uses2_self tl
    · obtain rfl : site = .mbarWait 8 := hat
      refine .inr ⟨?_, fun hat hc hfire => ev_pollF hpre hf hat hc hfire⟩
      rw [(ledAt_read hl).2.2.2.2.1 (stage3 tl)]
      exact uses3_self tl

/-- **Field `poll`** at a poll state of the phase: the polled mbarrier is the "empty" mbarrier
of an output stage or the "full" mbarrier of an input stage of the thread's block; the thread
is a compute thread of that block (a poller of both); its successful polls of the mbarrier are
one per earlier tile of the stage (`roundOf` of the tile index); the instruction is past 1402;
and every wait event the state can fire is on that mbarrier, with the parity of those polls
plus the mbarrier's offset (1 for an "empty" mbarrier, 0 for a "full" one). -/
theorem poll_compute (hpre : Pre P L mem0) {j0 k : Nat} {s : D} (hI : Inv P L X g j0 k s)
    (hp : siteCls s.site = .poll) :
    ∃ b : Bar, pollerOf L (g / L.block) b g ∧
      okPolls (b.loc L (g / L.block)) ((X.tr g).take k) ≤ roundOf b (tileOf P g s) ∧
      (s.site.pc ≤ 1402 → b = .state) ∧
      ∀ {t : TState} {ins : Instr} {e : Event} {o : Option TState},
        (code L g).AtD s t → kernel.code[s.site.pc]? = some ins →
        Fires s.site.pc (eventTmpl Assumptions.all L g t ins.op) e o →
        ∀ l q ok acq sc, e.kind = .wait l q ok acq sc →
          l = b.loc L (g / L.block) ∧
            q % 2 = (okPolls l ((X.tr g).take k) + b.delta) % 2 := by
  have hc : g % L.block < 128 := by rw [block_mod hpre]; exact compute_of_inv hI
  obtain ⟨tl, ht, hlt, hpc, ⟨hcnt, hfire⟩ | ⟨hcnt, hfire⟩⟩ := poll_fire hpre hI hp
  · refine ⟨.storeEmpty (stage2 tl), ⟨rfl, hc⟩, ?_, fun h => absurd h (by omega), ?_⟩
    · rw [hcnt, ht]
      exact le_of_eq (uses2_self tl).symm
    · intro t ins e o hat hcode hf l q ok acq sc hk
      obtain ⟨ok', rfl⟩ := hfire hat hcode hf
      cases hk
      refine ⟨rfl, ?_⟩
      rw [hcnt]
      show (tl / 2 + 1) % 2 % 2 = (tl / 2 + 1) % 2
      omega
  · refine ⟨.loadFull (stage3 tl), ⟨rfl, hc⟩, ?_, fun h => absurd h (by omega), ?_⟩
    · rw [hcnt, ht]
      exact le_of_eq (uses3_self tl).symm
    · intro t ins e o hat hcode hf l q ok acq sc hk
      obtain ⟨ok', rfl⟩ := hfire hat hcode hf
      cases hk
      refine ⟨rfl, ?_⟩
      rw [hcnt]
      show tl / 3 % 2 % 2 = (tl / 3 + 0) % 2
      omega

/-- **Field `pollStage`** at a poll state of the phase: a wait event that the state fires on
the "full" mbarrier of input stage `st` has `st` = the tile index modulo 3, and the tile index
is below the tile count; the state fires no wait event on a "full" mbarrier of the output
pipeline (which the store leader polls). -/
theorem pollStage_compute (hpre : Pre P L mem0) {j0 k : Nat} {s : D}
    (hI : Inv P L X g j0 k s) (hp : siteCls s.site = .poll)
    {t : TState} {ins : Instr} {e : Event} {o : Option TState} (hat : (code L g).AtD s t)
    (hcode : kernel.code[s.site.pc]? = some ins)
    (hf : Fires s.site.pc (eventTmpl Assumptions.all L g t ins.op) e o) (q : Nat)
    (ok acq : Bool) (sc : MbarScope) :
    (∀ st : Fin 3, e.kind = .wait ((Bar.loadFull st).loc L (g / L.block)) q ok acq sc →
        st.val = tileOf P g s % 3 ∧ tileOf P g s < tilesOf P g) ∧
      (∀ st : Fin 2, e.kind = .wait ((Bar.storeFull st).loc L (g / L.block)) q ok acq sc →
        st.val = tileOf P g s % 2 ∧ tileOf P g s < tilesOf P g) := by
  obtain ⟨tl, ht, hlt, hpc, ⟨hcnt, hfire⟩ | ⟨hcnt, hfire⟩⟩ := poll_fire hpre hI hp
  · obtain ⟨ok', rfl⟩ := hfire hat hcode hf
    refine ⟨fun st hk => ?_, fun st hk => ?_⟩
    · have h := (Kind.wait.inj hk).1
      cases (Bar.loc_inj h).1
    · have h := (Kind.wait.inj hk).1
      cases (Bar.loc_inj h).1
  · obtain ⟨ok', rfl⟩ := hfire hat hcode hf
    refine ⟨fun st hk => ?_, fun st hk => ?_⟩
    · have h := (Kind.wait.inj hk).1
      obtain rfl : stage3 tl = st := Bar.loadFull.inj (Bar.loc_inj h).1
      rw [ht]
      exact ⟨rfl, hlt⟩
    · have h := (Kind.wait.inj hk).1
      cases (Bar.loc_inj h).1

/-! ### One step from a state of the phase -/

/-- The successor of a followed state along the thread's event, from the two states. -/
theorem next_of_at {k : Nat} {e : Event} {s s' : D} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s))
    (hσ' : Frame.stateAt (code L) X g (k + 1) = some (some s')) :
    Thread.next L g s e = some (some s') := by
  rw [Frame.stateAt_succ he, hσ] at hσ'
  exact hσ'

/-- **One step from a state of the phase**: the successor along the thread's event is a state
of the phase, at a position with as many counted events more as the event counts (one, or none
for a failed poll), or it is the exit state, and the event was the last counted one of the
phase. -/
theorem step_compute (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hg : g < L.threads) {j0 k : Nat} {s s' : D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P L X g j0 k s)
    (hn : Thread.next L g s e = some (some s')) :
    ∃ pos, RefAt P L g pos s ∧
      ((∃ pos', RefAt P L g pos' s' ∧ Inv P L X g j0 (k + 1) s' ∧
          pos'.idx = pos.idx + (if e.counts = true then 1 else 0)) ∨
        (Out P L X g j0 (k + 1) s' ∧
          1 + 268 * tilesOf P g = pos.idx + (if e.counts = true then 1 else 0))) := by
  obtain ⟨pos, hR, hled, hjk, hcnt⟩ := hI
  obtain ⟨tt, ins, o, hat, -, hc, hf⟩ := Frame.fired_site (sounds hpre) hX he hσ
  refine ⟨pos, hR, ?_⟩
  rcases good hpre hg hR hat hc hf hn with ⟨pos', hR', hl, hi⟩ | ⟨hx, hl, hi⟩
  · exact .inl ⟨pos', hR', ⟨pos', hR', by rw [ledOf_succ he, hled, hl], by omega,
      by rw [counted_succ hjk he, hcnt, hi]⟩, hi⟩
  · exact .inr ⟨⟨hx, by rw [ledOf_succ he, hled, hl], by omega,
      by rw [counted_succ hjk he, hcnt, hi]⟩, hi⟩

/-- **Field `left_dec`** for a step from a state of the phase, with the counted events left read
off the states: the successor is a state of the phase or the exit state, and it has one event
less left when the event counts (every event but a failed poll); at the exit state none is
left. A global measure of the form `E g + leftOf P g d` on the states of this phase, with `E g`
at least the measure of the exit state, therefore satisfies the field on the steps of the
phase. -/
theorem leftOf_dec (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hg : g < L.threads) {j0 k : Nat} {s s' : D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P L X g j0 k s)
    (hn : Thread.next L g s e = some (some s')) :
    (Inv P L X g j0 (k + 1) s' ∨ Out P L X g j0 (k + 1) s') ∧
      leftOf P g s' + (if e.counts then 1 else 0) = leftOf P g s := by
  obtain ⟨pos, hR, ⟨pos', hR', hI', hi⟩ | ⟨hO, hi⟩⟩ := step_compute hpre hX hg he hσ hI hn
  · refine ⟨.inl hI', ?_⟩
    rw [leftOf_eq hpre hR, leftOf_eq hpre hR']
    have h1 := idx_le hR'
    generalize (if e.counts = true then 1 else 0) = c at hi ⊢
    omega
  · refine ⟨.inr hO, ?_⟩
    rw [leftOf_eq hpre hR, leftOf_exit hO.1]
    generalize (if e.counts = true then 1 else 0) = c at hi ⊢
    omega

/-- **Field `barStep`** for the two barriers of the phase. A barrier event at a state of the
phase is fired at sub-step 0, at the entry (the `bar.sync 0` at instruction 1402, tile index 0)
or at the named barrier of a tile (instruction 2913). The successor is at a later instruction
and its tile index is not smaller; it is a state of the phase (the first poll of tile 0, or
the fence of the same tile) or, from the entry of a sequence without tiles, the exit state at
instruction 3113 (where the tile index is the tile count, 0). -/
theorem barStep_compute (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads)
    {j0 k pc id : Nat} {cnt : Option Nat} {m : BarMode} {s s' : D}
    (he : X.get (g, k) = some ⟨pc, .bar id cnt m⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P L X g j0 k s)
    (hσ' : Frame.stateAt (code L) X g (k + 1) = some (some s')) :
    s.site.sub = 0 ∧ s.site.pc < s'.site.pc ∧ tileOf P g s ≤ tileOf P g s' ∧
      (Inv P L X g j0 (k + 1) s' ∨ Out P L X g j0 (k + 1) s') := by
  have hn := next_of_at he hσ hσ'
  obtain ⟨⟨j, hj⟩, hsub, -⟩ := bar_site_pc (sounds hpre) hX he hσ rfl
  obtain ⟨pos, hR, h⟩ := step_compute hpre hX hg he hσ hI hn
  have hcount : (if (Event.mk pc (.bar id cnt m)).counts = true then 1 else 0) = 1 := rfl
  rw [hcount] at h
  refine ⟨hsub, ?_⟩
  have ht := tileOf_eq hpre hR
  cases pos with
  | entry =>
    have hs : s.site = .bar 5 := hR.site
    have hpc : s.site.pc = 1402 := by rw [hs, entry_pc]
    rcases h with ⟨pos', hR', hI', hi⟩ | ⟨hO, hi⟩
    · refine ⟨?_, by rw [ht]; exact Nat.zero_le _, .inl hI'⟩
      cases pos' with
      | entry => simp only [Pos.idx] at hi; omega
      | tile t' n' =>
        have hp := pc_tab n' (show Tile P L g t' n' s'.w s'.p s'.x from hR'.facts).pos
        rw [hpc, pc_at hR'.site]
        omega
    · refine ⟨?_, by rw [ht]; exact Nat.zero_le _, .inr hO⟩
      rw [hpc, hO.1.site, exit_pc]
      omega
  | tile t n =>
    have hf : Tile P L g t n s.w s.p s.x := hR.facts
    have hat : (skOf n).At s.site := hR.site
    have hk : kindOf n = .bar := (kind_at hat).symm.trans (congrArg Site.kind hj)
    obtain rfl := bar_tab n hf.pos hk
    rcases h with ⟨pos', hR', hI', hi⟩ | ⟨hO, hi⟩
    · cases pos' with
      | entry => simp only [Pos.idx] at hi; omega
      | tile t' n' =>
        have hn' := (show Tile P L g t' n' s'.w s'.p s'.x from hR'.facts).pos
        have hat' : (skOf n').At s'.site := hR'.site
        simp only [Pos.idx] at hi
        obtain ⟨rfl, rfl⟩ : t' = t ∧ n' = 265 := by omega
        have h1 := pc_tab 264 (by omega)
        have h2 := pc_tab 265 (by omega)
        refine ⟨?_, ?_, .inl hI'⟩
        · rw [pc_at hat, pc_at hat']
          omega
        · rw [ht, tileOf_eq hpre hR']
          exact le_rfl
    · simp only [Pos.idx] at hi
      omega

/-! ### Earlier states of the thread -/

/-- The counted events since the entry grow with the trace index. -/
theorem counted_mono (j0 : Nat) {k k' : Nat} (h : k ≤ k') :
    counted X g j0 k ≤ counted X g j0 k' := by
  unfold counted
  exact ((List.take_sublist_take_left h).drop j0).countP_le

/-- **Before a state of the phase the thread has not left the phase**: with the entry condition
at the followed state at `k0` and the invariant at `k`, every followed state between the two
satisfies the invariant. (At the exit the thread has made `1 + 268 T` counted events since the
entry, more than at any position.) -/
theorem inv_before (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hg : g < L.threads) {k0 k i : Nat} {s0 s si : D} (h0 : At (code L) X g k0 s0)
    (hin : In P L X g k0 s0) (hI : Inv P L X g k0 k s) (hk : k ≤ (X.tr g).length)
    (hki : k0 ≤ i) (hik : i ≤ k) (hsi : At (code L) X g i si) : Inv P L X g k0 i si := by
  rcases inv_at hpre hX hg h0 hin hki (by omega) hsi with h | ⟨j, s1, h1, h2, -, -, -, -, hc⟩
  · exact h
  · obtain ⟨pos, hr, -, -, hcnt⟩ := hI
    have hm := counted_mono (X := X) (g := g) k0 (show j ≤ k by omega)
    have hle := idx_le hr
    rw [hc, hcnt] at hm
    omega

/-! ### The thread's last state at a matrix event -/

/-- **The template of a state at a matrix event** is undefined behaviour or a matrix event
with the operation of the warp matrix instruction at the state's site. -/
theorem tmpl_matrix {d : D} {t : TState} (hat : (code L g).AtD d t)
    (hm : siteCls d.site = .matrix) :
    (∃ f, (code L g).tmpl (some d) t = .ub f) ∨
      ∃ ins i own k, kernel.code[d.site.pc]? = some ins ∧ ins.op = .matrix i ∧
        (code L g).tmpl (some d) t = .matrix i.op own k := by
  simp only [Code.tmpl]
  cases hi : kernel.code[d.site.pc]? with
  | none => exact .inl ⟨_, rfl⟩
  | some ins =>
    have hκ := Ref.site_op d.site hi
    have hsub : t.sub = d.site.sub := hat.2.1
    rw [← hsub] at hκ
    obtain ⟨i, hop⟩ := op_of_matrix_kind hκ (by rw [← siteCls_kind]; exact hm)
    rw [hop] at hκ
    rcases matrix_tmpl (L := L) (g := g) hκ (by rw [← siteCls_kind]; exact hm) with
      ⟨f, hf⟩ | ⟨own, k, hk⟩
    · refine .inl ⟨f, ?_⟩
      show eventTmpl Assumptions.all L g t ins.op = .ub f
      rw [hop]
      exact hf
    · refine .inr ⟨ins, i, own, k, rfl, hop, ?_⟩
      show eventTmpl Assumptions.all L g t ins.op = .matrix i.op own k
      rw [hop]
      exact hk

/-- **Field `matrixShape`** at a thread's last state, when it is a state of the phase at a
matrix event: the template of the state is undefined behaviour, or it is the matrix event of
the instruction whose ordinal in the consumer's table `Top.matrixSites` is the number of the
thread's matrix events modulo 182, with that instruction's operation. -/
theorem matrixShape_compute (hpre : Pre P L mem0) (hg : g < L.threads) {j0 : Nat} {d : D}
    {t : TState} {m : Tmpl} (hI : Inv P L X g j0 (X.tr g).length d)
    (hm : siteCls d.site = .matrix) (hat : (code L g).AtD d t)
    (hout : out kernel Assumptions.all L g t = .ev m) :
    (∃ f, m = .ub f) ∨
      ∃ pc op own k, Top.matrixSites[(X.tr g).countP isMatrix % 182]? = some (pc, op) ∧
        t.pc = pc ∧ m = .matrix op own k := by
  have ho := Code.site_out (Thread.sound hpre hg) (d := d) (t := t) ⟨hat, trivial⟩
  rw [hout] at ho
  have hm' : m = (code L g).tmpl (some d) t := by injection ho
  subst hm'
  rcases tmpl_matrix hat hm with h | ⟨ins, i, own, k, hi, hop, hk⟩
  · exact .inl h
  · refine .inr ⟨d.site.pc, i.op, own, k, ?_, hat.1, hk⟩
    obtain ⟨pos, hr, hl, -⟩ := hI
    cases pos with
    | entry =>
      have hs : d.site = .bar 5 := hr.site
      rw [hs] at hm
      cases hm
    | tile tl n =>
      have hf : Tile P L g tl n d.w d.p d.x := hr.facts
      have hsk : (skOf n).At d.site := hr.site
      obtain ⟨-, hlt, htab, -, -⟩ := mx_tab n hf.pos (by rw [← cls_at hsk]; exact hm)
      have hcnt : (X.tr g).countP isMatrix = 182 * tl + matOf n := by
        have h := (ledAt_read hl).2.2.1
        rwa [List.take_length] at h
      rw [hcnt, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
      obtain ⟨op', hop'⟩ := mxPcs_site htab
      obtain ⟨ins', i', hc', hi', rfl⟩ := matrixSites_op hop'
      rw [← pc_at hsk] at hc' hop'
      obtain rfl : ins' = ins := Option.some.inj (hc'.symm.trans hi)
      obtain rfl : i' = i := Op.matrix.inj (hi'.symm.trans hop)
      exact hop'

/-- **Field `matrixPrev`** at a thread's last state, when it is a state of the phase at a matrix
event: the thread's last event never blocks. It was fired at the position of the state (a failed
poll: none is at a matrix event) or at the position before it in the same tile, which is no
`bar.sync`: the row read of the same `ldmatrix`, a matrix event, a row write or a scalar
load. -/
theorem matrixPrev_compute (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads) {k0 : Nat}
    {s0 d : D} (h0 : At (code L) X g k0 s0) (hin : In P L X g k0 s0)
    (hσ : Frame.stateAt (code L) X g (X.tr g).length = some (some d))
    (hI : Inv P L X g k0 (X.tr g).length d) (hm : siteCls d.site = .matrix) {q : Event}
    (hq : X.get (g, (X.tr g).length - 1) = some q) : Unblocking q.kind := by
  obtain ⟨pos, hr, hl, hk0, hcnt⟩ := hI
  cases pos with
  | entry =>
    have hs : d.site = .bar 5 := hr.site
    rw [hs] at hm
    cases hm
  | tile t n =>
    have hf : Tile P L g t n d.w d.p d.x := hr.facts
    have hsk : (skOf n).At d.site := hr.site
    obtain ⟨hn3, -, -, hb, hb'⟩ := mx_tab n hf.pos (by rw [← cls_at hsk]; exact hm)
    have hlen : k0 < (X.tr g).length := by
      by_contra hc
      obtain rfl : k0 = (X.tr g).length := by omega
      rw [counted_self] at hcnt
      simp only [Pos.idx] at hcnt
      omega
    have hlast : (X.tr g).length - 1 + 1 = (X.tr g).length := by omega
    obtain ⟨d0, hd0⟩ := followed_of_le hσ (Nat.sub_le _ 1)
    obtain ⟨pos0, hr0, -, hk00, hcnt0⟩ := inv_before hpre hX hg h0 hin
      ⟨_, hr, hl, hk0, hcnt⟩ le_rfl (by omega) (Nat.sub_le _ 1) hd0
    have hs := counted_succ (X := X) (g := g) hk00 hq
    rw [hlast, hcnt, hcnt0] at hs
    have hc1 : (if q.counts = true then 1 else 0) ≤ 1 := by split_ifs <;> omega
    generalize (if q.counts = true then 1 else 0) = c at hs hc1
    refine unblocking_of_fired (site_fires (sounds hpre) hX hq hd0) ?_ ?_
    · cases pos0 with
      | entry => simp only [Pos.idx] at hs; omega
      | tile t0 n0 =>
        have hn0 := (show Tile P L g t0 n0 d0.w d0.p d0.x from hr0.facts).pos
        have hpos := hf.pos
        simp only [Pos.idx] at hs
        rw [kind_at hr0.site]
        obtain rfl | rfl : n0 = n ∨ n0 = n - 1 := by omega
        · exact hb
        · exact hb'
    · cases pos0 with
      | entry => simp only [Pos.idx] at hs; omega
      | tile t0 n0 =>
        rw [kind_at hr0.site]
        exact (kind_tab n0 (show Tile P L g t0 n0 d0.w d0.p d0.x from hr0.facts).pos).2.2

/-! ### Classes of events the phase does not touch -/

/-- The kinds of the sites of the phase: a `bar.sync`, a poll, the two events of an `ldmatrix`
and of a `stmatrix`, an `mma`, a `movmatrix`, a scalar load, a proxy fence, an mbarrier
arrival. -/
def phaseKinds : List SiteKind :=
  [.bar, .mbarWait, .matrixLoad, .matrixLoadMx, .warpMma, .matrixMove, .matrixStore,
   .matrixStoreWr, .load, .fenceProxy, .mbarArrive]

/-- The site of every position of a tile is of one of the kinds of the phase. -/
theorem kindOf_mem : ∀ n < 268, kindOf n ∈ phaseKinds := by decide +kernel

/-- The site of a state of the phase is of one of the kinds of the phase. -/
theorem kind_mem {j0 k : Nat} {s : D} (hI : Inv P L X g j0 k s) : s.site.kind ∈ phaseKinds := by
  rcases kind_compute hI with h | ⟨n, hn, h⟩
  · rw [h]
    decide
  · rw [h]
    exact kindOf_mem n hn

/-- **A class of events that no kind of site of the phase fires keeps its count** between two
trace indices `k0 ≤ k` when every followed state from `k0` to before `k` is a state of the
phase. `FiredOnly c K` (`Ref/Kinds/Count.lean`): events of class `c` are fired only at sites
whose kind is in `K`. -/
theorem frame_states (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    {c : Event → Bool} {K : List SiteKind} (hK : FiredOnly c K)
    (hd : ∀ κ ∈ K, κ ∉ phaseKinds) {k0 k : Nat} {s : D} (hk0 : k0 ≤ k)
    (hs : At (code L) X g k s)
    (hall : ∀ i si, k0 ≤ i → i < k → At (code L) X g i si → Inv P L X g k0 i si) :
    ((X.tr g).take k).countP c = ((X.tr g).take k0).countP c :=
  count_transport_of_state (sounds hpre) hX hK hk0 hs (Nat.le_succ k) fun i d h1 h2 hd' =>
    .inl fun hmem => hd _ hmem (kind_mem (hall i d h1 h2 hd'))

/-- **Count transport through the phase, to a state of the phase**: the count of a class of
events that no kind of site of the phase fires (warp collectives, tensor copies, mbarrier
initializations, bulk-group commits and waits, stores, the exit) is at every state of the phase
the count at the entry. -/
theorem frame_compute (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hg : g < L.threads) {c : Event → Bool} {K : List SiteKind} (hK : FiredOnly c K)
    (hd : ∀ κ ∈ K, κ ∉ phaseKinds) {k0 k : Nat} {s0 s : D} (h0 : At (code L) X g k0 s0)
    (hin : In P L X g k0 s0) (hk : k ≤ (X.tr g).length) (hs : At (code L) X g k s)
    (hI : Inv P L X g k0 k s) :
    ((X.tr g).take k).countP c = ((X.tr g).take k0).countP c :=
  frame_states hpre hX hK hd (entry_le hI) hs fun _ _ h1 h2 hsi =>
    inv_before hpre hX hg h0 hin hI hk h1 h2.le hsi

/-- **Count transport through the phase, to its first exit**: the same at the exit state, when
every followed state between the entry and it is a state of the phase (the exit condition of
`Phase.first`, `Ref/Chain.lean`). -/
theorem frame_out (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    {c : Event → Bool} {K : List SiteKind} (hK : FiredOnly c K)
    (hd : ∀ κ ∈ K, κ ∉ phaseKinds) {k0 j : Nat} {s1 : D} (hs1 : At (code L) X g j s1)
    (ho : Out P L X g k0 j s1)
    (hfirst : ∀ i si, k0 ≤ i → i < j → At (code L) X g i si → Inv P L X g k0 i si) :
    ((X.tr g).take j).countP c = ((X.tr g).take k0).countP c :=
  frame_states hpre hX hK hd ho.2.2.1 hs1 hfirst

/-- A warp collective (a shuffle, an election, a warp barrier or a ballot) is fired only at a
shuffle or an election site. -/
theorem firedOnly_isWarpColl : FiredOnly isWarpColl [.elect, .shfl] := by
  fired_only [isWarpColl]

/-- Past instruction 312 a warp has made all its collectives. -/
theorem collOf_late {w pc : Nat} (h : 312 < pc) : collOf w pc = (collPcs w).length := by
  have h312 : ∀ p ∈ Progress.collAll, p ≤ 312 := by decide
  unfold collOf
  rw [List.filter_eq_self.mpr]
  intro a ha
  have := h312 a (Progress.collPcs_sub w a ha)
  exact decide_eq_true (by omega)

/-- **Field `coll`** at a state of the phase, from the field at the entry state: the phase has
no shuffle and no election, and the consumer's count `collOf` is the same at every instruction
from the entry on. -/
theorem coll_compute (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hg : g < L.threads) {k0 k : Nat} {s0 s : D} (h0 : At (code L) X g k0 s0)
    (hin : In P L X g k0 s0) (hk : k ≤ (X.tr g).length) (hs : At (code L) X g k s)
    (hI : Inv P L X g k0 k s)
    (hc0 : ((X.tr g).take k0).countP isWarpColl = collOf (g % L.block / 32) s0.site.pc) :
    ((X.tr g).take k).countP isWarpColl = collOf (g % L.block / 32) s.site.pc := by
  have hpc := site_compute hI
  rw [frame_compute hpre hX hg firedOnly_isWarpColl (by decide) h0 hin hk hs hI, hc0,
    hin.1.site, entry_pc, collOf_late (by omega), collOf_late (by omega)]

/-- **Field `coll`** at the first exit of the phase, from the field at the entry state. -/
theorem coll_out (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    {k0 j : Nat} {s0 s1 : D} (hin : In P L X g k0 s0) (hs1 : At (code L) X g j s1)
    (ho : Out P L X g k0 j s1)
    (hfirst : ∀ i si, k0 ≤ i → i < j → At (code L) X g i si → Inv P L X g k0 i si)
    (hc0 : ((X.tr g).take k0).countP isWarpColl = collOf (g % L.block / 32) s0.site.pc) :
    ((X.tr g).take j).countP isWarpColl = collOf (g % L.block / 32) s1.site.pc := by
  rw [frame_out hpre hX firedOnly_isWarpColl (by decide) hs1 ho hfirst, hc0, hin.1.site,
    entry_pc, ho.1.site, exit_pc, collOf_late (by omega), collOf_late (by omega)]

/-! ### The events of the phase, and the classes none of them belongs to -/

/-- The kinds of the sites of the 262 positions of a tile between its two polls and its named
barrier: the two events of an `ldmatrix` and of a `stmatrix`, an `mma`, a `movmatrix`, a scalar
load. -/
def bodyKinds : List SiteKind :=
  [.matrixLoad, .matrixLoadMx, .warpMma, .matrixMove, .matrixStore, .matrixStoreWr, .load]

/-- The sites of the positions 2 to 263 of a tile are of the kinds of the body. -/
theorem body_tab : ∀ n < 268, 2 ≤ n → n < 264 → kindOf n ∈ bodyKinds := by decide +kernel

/-- **The events a state at a position fires**: in closed form at the seven control positions
(the `bar.sync 0` of the entry, the two polls, the named barrier, the proxy fence and the two
arrivals of a tile), and by the kind of the site at the 262 other positions of a tile (a memory
read, a matrix event or a memory write, as the table `firedAt` of `Ref/Kinds` says, or
undefined behaviour). -/
def Ev (L : Launch) (g : Nat) : Pos → Event → Prop
  | .entry, e => e = ⟨1402, .bar 0 none .sync⟩
  | .tile t n, e =>
    n < 268 ∧
    (n = 0 → ∃ ok, e = ⟨2144, .wait ((Bar.storeEmpty (stage2 t)).loc L (g / L.block))
      ((t / 2 + 1) % 2) ok true .cta⟩) ∧
    (n = 1 → ∃ ok, e = ⟨2186, .wait ((Bar.loadFull (stage3 t)).loc L (g / L.block))
      (t / 3 % 2) ok true .cta⟩) ∧
    (n = 264 → e = ⟨2913, .bar 8 (some 128) .sync⟩) ∧
    (n = 265 → e = ⟨2914, .fenceProxy (.async (some (.shared .cta))) none⟩) ∧
    (n = 266 → e = ⟨2920, .arrive ((Bar.storeFull (stage2 t)).loc L (g / L.block)) 0 1 true
      .cta⟩) ∧
    (n = 267 → e = ⟨2928, .arrive ((Bar.loadEmpty (stage3 t)).loc L (g / L.block)) 0 1 true
      .cta⟩) ∧
    (2 ≤ n → n < 264 → firedAt e.kind (kindOf n) = true)

/-- **The event at a state of the phase is one its position fires.** -/
theorem ev_at (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hg : g < L.threads) {j0 k : Nat} {s : D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P L X g j0 k s) :
    ∃ pos, RefAt P L g pos s ∧ Ev L g pos e := by
  obtain ⟨pos, hR, -⟩ := hI
  obtain ⟨tt, ins, o, hat, -, hc, hf⟩ := Frame.fired_site (sounds hpre) hX he hσ
  have hkind := site_fires (sounds hpre) hX he hσ
  refine ⟨pos, hR, ?_⟩
  obtain ⟨site, w, p, x⟩ := s
  cases pos with
  | entry =>
    obtain rfl : site = .bar 5 := hR.site
    exact ev_entry hc hf
  | tile t n =>
    have hT : Tile P L g t n w p x := hR.facts
    have hsk : (skOf n).At site := hR.site
    refine ⟨hT.pos, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
      fun h => ?_, fun _ _ => ?_⟩
    · subst h
      obtain rfl : site = .mbarWait 7 := hsk
      exact ev_pollE hpre hT hat hc hf
    · subst h
      obtain rfl : site = .mbarWait 8 := hsk
      exact ev_pollF hpre hT hat hc hf
    · subst h
      obtain rfl : site = .bar 6 := hsk
      exact ev_bar8 hpre hT hat hc hf
    · subst h
      obtain rfl : site = .fenceProxy 2 := hsk
      exact ev_fence hc hf
    · subst h
      obtain rfl : site = .mbarArrive 4 := hsk
      exact ev_arriveF hpre hT hat hc hf
    · subst h
      obtain rfl : site = .mbarArrive 5 := hsk
      exact ev_arriveE hpre hg hT hat hc hf
    · rw [← kind_at hsk]
      exact hkind

/-- A class of events that no event of the phase belongs to. -/
def Untouched (L : Launch) (g : Nat) (c : Event → Bool) : Prop :=
  ∀ pos e, Ev L g pos e → c e = false

/-- **A class is one that no event of the phase belongs to** when none of the seven control
events is of the class and no site of the body of a tile can fire it (`FiredOnly c K` with no
kind of `K` among `bodyKinds`). -/
theorem untouched_of {c : Event → Bool} {K : List SiteKind} (hK : FiredOnly c K)
    (hd : ∀ κ ∈ K, κ ∉ bodyKinds) (h1 : c ⟨1402, .bar 0 none .sync⟩ = false)
    (h2 : ∀ t ok, c ⟨2144, .wait ((Bar.storeEmpty (stage2 t)).loc L (g / L.block))
      ((t / 2 + 1) % 2) ok true .cta⟩ = false)
    (h3 : ∀ t ok, c ⟨2186, .wait ((Bar.loadFull (stage3 t)).loc L (g / L.block))
      (t / 3 % 2) ok true .cta⟩ = false)
    (h4 : c ⟨2913, .bar 8 (some 128) .sync⟩ = false)
    (h5 : c ⟨2914, .fenceProxy (.async (some (.shared .cta))) none⟩ = false)
    (h6 : ∀ t, c ⟨2920, .arrive ((Bar.storeFull (stage2 t)).loc L (g / L.block)) 0 1 true
      .cta⟩ = false)
    (h7 : ∀ t, c ⟨2928, .arrive ((Bar.loadEmpty (stage3 t)).loc L (g / L.block)) 0 1 true
      .cta⟩ = false) : Untouched L g c := by
  intro pos e h
  cases pos with
  | entry => rw [show e = _ from h]; exact h1
  | tile t n =>
    obtain ⟨hn, e0, e1, e264, e265, e266, e267, ebody⟩ := h
    by_cases hb : 2 ≤ n ∧ n < 264
    · cases hc : c e
      · rfl
      · exact absurd (body_tab n hn hb.1 hb.2) (hd _ (hK e _ hc (ebody hb.1 hb.2)))
    · obtain rfl | rfl | rfl | rfl | rfl | rfl :
          n = 0 ∨ n = 1 ∨ n = 264 ∨ n = 265 ∨ n = 266 ∨ n = 267 := by omega
      · obtain ⟨ok, rfl⟩ := e0 rfl
        exact h2 t ok
      · obtain ⟨ok, rfl⟩ := e1 rfl
        exact h3 t ok
      · rw [e264 rfl]
        exact h4
      · rw [e265 rfl]
        exact h5
      · rw [e266 rfl]
        exact h6 t
      · rw [e267 rfl]
        exact h7 t

/-- **Count transport for a class that no event of the phase belongs to**: its count is the same
at two trace indices `k0 ≤ k` when every followed state from `k0` to before `k` is a state of
the phase. -/
theorem frame_ev (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hg : g < L.threads) {c : Event → Bool} (hc : Untouched L g c) {k0 k : Nat} {s : D}
    (hk0 : k0 ≤ k) (hs : At (code L) X g k s)
    (hall : ∀ i si, k0 ≤ i → i < k → At (code L) X g i si → Inv P L X g k0 i si) :
    ((X.tr g).take k).countP c = ((X.tr g).take k0).countP c := by
  refine countP_take_eq c hk0 fun i e h1 h2 he => ?_
  obtain ⟨si, hsi⟩ := followed_of_le hs (show i ≤ k by omega)
  obtain ⟨pos, -, hev⟩ := ev_at hpre hX hg he hsi (hall i si h1 h2 hsi)
  exact hc pos e hev

/-- **The arrivals on, the tensor loads completing on and the successful polls of the state
mbarrier of the thread's block are classes that no event of the phase belongs to**: the polls of
the phase are on an "empty" mbarrier of the output pipeline and a "full" mbarrier of the input
pipeline, its arrivals on a "full" mbarrier of the output pipeline and an "empty" mbarrier of
the input pipeline, and it issues no tensor load. -/
theorem state_untouched :
    Untouched L g (arrivesOn (Bar.state.loc L (g / L.block))) ∧
      Untouched L g (issuesTo (Bar.state.loc L (g / L.block))) ∧
      Untouched L g (okPoll (Bar.state.loc L (g / L.block))) := by
  refine ⟨untouched_of (firedOnly_arrivesOn _) (by decide) rfl (fun _ _ => rfl)
      (fun _ _ => rfl) rfl rfl
      (fun t => arrivesOn_other rfl fun h => by cases (Bar.loc_inj h).1)
      (fun t => arrivesOn_other rfl fun h => by cases (Bar.loc_inj h).1),
    untouched_of (firedOnly_issuesTo _) (by decide) rfl (fun _ _ => rfl) (fun _ _ => rfl) rfl
      rfl (fun _ => rfl) (fun _ => rfl),
    untouched_of (firedOnly_okPoll _) (by decide) rfl
      (fun t ok => okPoll_other rfl fun h => by cases (Bar.loc_inj h).1)
      (fun t ok => okPoll_other rfl fun h => by cases (Bar.loc_inj h).1) rfl rfl
      (fun _ => rfl) (fun _ => rfl)⟩

/-- **The counts on the state mbarrier through the phase** (the classes of the field
`arrState`; the field itself is about the load leader and vacuous for a compute thread,
`not_leader`): at every state of the phase the thread's arrivals on, its tensor loads
completing on and its successful polls of the state mbarrier of its block are those at the
entry. -/
theorem state_counts_compute (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads) {k0 k : Nat}
    {s0 s : D} (h0 : At (code L) X g k0 s0) (hin : In P L X g k0 s0)
    (hk : k ≤ (X.tr g).length) (hs : At (code L) X g k s) (hI : Inv P L X g k0 k s) :
    arrivals (Bar.state.loc L (g / L.block)) ((X.tr g).take k) =
        arrivals (Bar.state.loc L (g / L.block)) ((X.tr g).take k0) ∧
      ((X.tr g).take k).countP (issuesTo (Bar.state.loc L (g / L.block))) =
        ((X.tr g).take k0).countP (issuesTo (Bar.state.loc L (g / L.block))) ∧
      okPolls (Bar.state.loc L (g / L.block)) ((X.tr g).take k) =
        okPolls (Bar.state.loc L (g / L.block)) ((X.tr g).take k0) := by
  have hall : ∀ i si, k0 ≤ i → i < k → At (code L) X g i si → Inv P L X g k0 i si :=
    fun i si h1 h2 hsi => inv_before hpre hX hg h0 hin hI hk h1 h2.le hsi
  have hk0 : k0 ≤ k := entry_le hI
  obtain ⟨ha, hi, hp⟩ := state_untouched (L := L) (g := g)
  exact ⟨frame_ev hpre hX hg ha hk0 hs hall, frame_ev hpre hX hg hi hk0 hs hall,
    frame_ev hpre hX hg hp hk0 hs hall⟩

/-- **The counts on the state mbarrier at the first exit of the phase** are those at the
entry. -/
theorem state_counts_out (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads) {k0 j : Nat}
    {s1 : D} (hs1 : At (code L) X g j s1) (ho : Out P L X g k0 j s1)
    (hfirst : ∀ i si, k0 ≤ i → i < j → At (code L) X g i si → Inv P L X g k0 i si) :
    arrivals (Bar.state.loc L (g / L.block)) ((X.tr g).take j) =
        arrivals (Bar.state.loc L (g / L.block)) ((X.tr g).take k0) ∧
      ((X.tr g).take j).countP (issuesTo (Bar.state.loc L (g / L.block))) =
        ((X.tr g).take k0).countP (issuesTo (Bar.state.loc L (g / L.block))) ∧
      okPolls (Bar.state.loc L (g / L.block)) ((X.tr g).take j) =
        okPolls (Bar.state.loc L (g / L.block)) ((X.tr g).take k0) := by
  obtain ⟨ha, hi, hp⟩ := state_untouched (L := L) (g := g)
  exact ⟨frame_ev hpre hX hg ha ho.2.2.1 hs1 hfirst, frame_ev hpre hX hg hi ho.2.2.1 hs1 hfirst,
    frame_ev hpre hX hg hp ho.2.2.1 hs1 hfirst⟩

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Compute
