-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Producer.Exports

@[expose] public section

/-! # The Producer share of the progress contract

`Proof/Schedule/Contract.lean: RefProgress` is what the progress instance needs from the
reference layer about a followed state `d` of a thread and the counts over its earlier events.
This file proves the share of the Producer phase (a thread of the load warp between its
`bar.sync 0` at instruction 1402 and the one at 3113), in the pattern of the startup phase's
`Ref/Startup/Progress.lean`: the statements do not import the progress files; each is in the
terms the field unfolds to (the field is named in the docstring), for a state that satisfies the
phase invariant `Inv` or, where it matters, the exit condition `Out`.

* `site_pc`, `region_producer`, `kind_producer`: field `region` (a state of the phase is at an
  instruction from 1402 to 2105; the thread is of the load warp by hypothesis) and the
  vacuous cases of `collAt`, `tile_matrix`, `exitAt` (a state of the phase is at a barrier, a
  poll, an arrival or a tensor copy: never at an election, a shuffle, a matrix instruction or
  the exit).
* `tileOf`, `leftOf`: the tile index and the counted events left as functions of the STATE
  (its site and the register `%r1797`), for the contract's `Nums.tile` and `Nums.left`;
  `tileOf_eq`, `leftOf_eq`: they are the position's `tileAt` and `leftAt` of `Exports.lean`.
  `tilesOf_cta`: the tile count is the protocol layer's `ctaTiles P (g / L.block)`.
* `tile_producer`: fields `tile_le`, `tile_start`, `arrLoadFull`. `leftOf_dec`: field
  `left_dec`.
* `bar0_producer`, `bar0_out`: field `bar0` (`bar0Of d.site.pc` unfolded:
  `(bar0Pcs.filter (· < pc)).length`).
* `fires_ev`: the template-level form of the closed-form events: every event that a concrete
  state of the phase can fire is the event `Ev` of its position.
* `poll_producer`: field `poll` at the six poll sites: the polled mbarrier is `Bar.loadEmpty
  st` of the thread's block, the thread is the load leader, its successful polls of it are
  `uses 3 (tileOf P g s) st` (= `roundOf (.loadEmpty st)` of the tile index), the instruction
  is past 1402, and every wait event the state fires is on that mbarrier with the parity of
  those polls plus one (`Bar.delta = 1`). `pollStage_producer`: field `pollStage` is vacuous in
  the phase (such an event is on no "full" mbarrier).
* `barStep_producer`: field `barStep` for the one barrier of the phase (1402): sub-step 0, a
  later instruction, and the successor is a position of the load leader with tile index 0 or,
  for a lane other than lane 0, the exit state at 3113.
* `frame_producer`: every class of events that no event of the phase belongs to (`Untouched`)
  keeps its count from the entry to every state of the phase and to its exit. With `ev_kinds`
  (an event of the phase is a barrier arrival, a poll, an mbarrier arrival or a tensor load
  issue; `untouched_of_kinds`) and `ev_state_free` (it is no arrival on, no load completing on
  and no successful poll of the state mbarrier) this gives the fields `coll` (no warp
  collective in the phase: the count is the entry's, six for the load warp) and `arrState`
  (`state_counts_producer`: the counts on the state mbarrier are those at the entry).

`tile_end` is the convention at the exit state (instruction 3113), which belongs to the
epilogue. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Producer
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Protocol (Bar uses loadLeader bar0Before bar0Pcs)

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 4000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-! ### Where the states of the phase are -/

/-- The tensor-copy sites of the phase are at the instructions 1470 to 2067. -/
theorem copy_pc : ∀ j : Fin 258, 16 ≤ j.val → j.val < 226 →
    1402 < (Site.tensorCopy j).pc ∧ (Site.tensorCopy j).pc ≤ 2105 := by
  decide +kernel

/-- The poll sites of the phase (three of the loop, three of the tail) are at the instructions
1443 to 2103. -/
theorem wait_pc : ∀ j : Fin 10, 1 ≤ j.val → j.val < 7 →
    1402 < (Site.mbarWait j).pc ∧ (Site.mbarWait j).pc ≤ 2105 := by
  decide +kernel

/-- The arrival sites of the phase are at the instructions 1451 to 1877. -/
theorem arrive_pc : ∀ j : Fin 7, 1 ≤ j.val → j.val < 4 →
    1402 < (Site.mbarArrive j).pc ∧ (Site.mbarArrive j).pc ≤ 2105 := by
  decide +kernel

/-- **The instruction of a position**: 1402 at the entry, between 1403 and 2105 elsewhere. -/
theorem site_pc (pos : Pos) :
    (pos = .entry ∧ pos.site.pc = 1402) ∨
      (pos ≠ .entry ∧ 1402 < pos.site.pc ∧ pos.site.pc ≤ 2105) := by
  cases pos with
  | entry => exact .inl ⟨rfl, rfl⟩
  | poll c u =>
    have hc := c.isLt
    exact .inr ⟨by simp, wait_pc ⟨c.val + 1, by omega⟩ (by simp) (by simp only; omega)⟩
  | arrive c u =>
    have hc := c.isLt
    exact .inr ⟨by simp, arrive_pc ⟨c.val + 1, by omega⟩ (by simp) (by simp only; omega)⟩
  | load c u i =>
    have hc := c.isLt
    have hi := i.isLt
    exact .inr ⟨by simp, copy_pc ⟨16 + (70 * c.val + i.val), by omega⟩ (by simp) (by
      simp only; omega)⟩
  | tail j =>
    have hj := j.isLt
    exact .inr ⟨by simp, wait_pc ⟨j.val + 4, by omega⟩ (by simp) (by simp only; omega)⟩

/-- **Field `region`**: a state of the phase is at an instruction from 1402 to 2105. -/
theorem region_producer {k : Nat} {s : D} (hI : Inv P L X g k s) :
    1402 ≤ s.site.pc ∧ s.site.pc ≤ 2105 := by
  obtain ⟨pos, hr, -⟩ := hI
  rw [hr.site]
  rcases site_pc pos with ⟨-, h⟩ | ⟨-, h1, h2⟩ <;> omega

/-- **The kind of site of a state of the phase**: a barrier, a poll, an arrival or a tensor
copy (so the fields `collAt`, `tile_matrix` and `exitAt` are vacuous in the phase). -/
theorem kind_producer {k : Nat} {s : D} (hI : Inv P L X g k s) :
    (∃ j, s.site = .bar j) ∨ (∃ j, s.site = .mbarWait j) ∨ (∃ j, s.site = .mbarArrive j) ∨
      ∃ j, s.site = .tensorCopy j := by
  obtain ⟨pos, hr, -⟩ := hI
  rw [hr.site]
  cases pos with
  | entry => exact .inl ⟨_, rfl⟩
  | poll c u => exact .inr (.inl ⟨_, rfl⟩)
  | arrive c u => exact .inr (.inr (.inl ⟨_, rfl⟩))
  | load c u i => exact .inr (.inr (.inr ⟨_, rfl⟩))
  | tail j => exact .inr (.inl ⟨_, rfl⟩)

/-! ### The tile index and the events left, read off a state

`Exports.lean` gives the tile index `tileAt P g pos` and the counted events left
`leftAt P g pos` as functions of the ghost position. The progress contract wants them as
functions of the state (`Nums.tile`, `Nums.left`); `tileOf` and `leftOf` read them off the site
and one register, and agree with the position's at every state of the phase. -/

/-- The tile count of the thread's block, in the protocol layer's terms (the right-hand side is
`Protocol.ctaTiles P (g / L.block)` unfolded). -/
theorem tilesOf_cta (hpre : Pre P L mem0) (g : Nat) :
    tilesOf P g = tiles (P.length (g / L.block % P.sequences)) := by
  simp only [tilesOf, seqOf, hpre.block]

/-- The base index of the unrolled tile loop, read off a state: register `%r1797` (the loop
counter that both copies of the unrolled loop and the remainder keep). -/
def baseOf (d : D) : Nat := (d.w 2103).toNat

/-- **The tile index of a state of the phase, read off the state**: at a site of the tile loop
the base index, plus one in the second copy of the unrolled loop (the poll at 1650, the arrival
at 1658, the tensor copies 86 to 155); the tile count at the three polls of the tail; 0 at the
barrier. -/
def tileOf (P : Params) (g : Nat) (d : D) : Nat :=
  match d.site with
  | .mbarWait j => if j.val < 4 then baseOf d + (if j.val = 2 then 1 else 0) else tilesOf P g
  | .mbarArrive j => baseOf d + (if j.val = 2 then 1 else 0)
  | .tensorCopy j => baseOf d + (if (j.val - 16) / 70 = 1 then 1 else 0)
  | _ => 0

/-- **The counted events left in the phase, read off a state** (`leftAt` in the terms of the
site): 72 per tile from the poll on and the three polls of the tail; at the barrier also the
barrier's own event, and nothing else for a lane other than the leader. -/
def leftOf (P : Params) (g : Nat) (d : D) : Nat :=
  match d.site with
  | .mbarWait j => if j.val < 4 then 72 * (tilesOf P g - tileOf P g d) + 3 else 7 - j.val
  | .mbarArrive _ => 72 * (tilesOf P g - tileOf P g d) + 2
  | .tensorCopy j => 72 * (tilesOf P g - tileOf P g d) + 1 - (j.val - 16) % 70
  | _ => if tid g = 128 then 72 * tilesOf P g + 4 else 1

/-- At a position of the tile loop the register `%r1797` holds the base index. -/
theorem base_eq (hpre : Pre P L mem0) {pos : Pos} {d : D} (hr : RefAt P g pos d) :
    (∀ c u, pos = .poll c u → baseOf d = u) ∧ (∀ c u, pos = .arrive c u → baseOf d = u) ∧
      ∀ c u i, pos = .load c u i → baseOf d = u := by
  obtain ⟨h1, h2, h3⟩ := tile_lt hr
  have hT := tiles_lt hpre g
  have hle : ∀ (c : Fin 3) (u : Nat), tile c u < tilesOf P g → u < 2 ^ 64 := by
    intro c u h
    simp only [tile] at h
    split_ifs at h <;> omega
  have h := hr.pos
  refine ⟨?_, ?_, ?_⟩
  · rintro c u rfl
    simp only [AtPos] at h
    have hw : d.w 2103 = W u := by
      fin_cases c <;> simp only [finVal, Loop, Rem] at h <;> simp only [h]
    rw [baseOf, hw, toNat_W (hle c u (h1 c u rfl))]
  · rintro c u rfl
    simp only [AtPos] at h
    have hw : d.w 2103 = W u := by
      fin_cases c <;> simp only [finVal, Loop, Rem] at h <;> simp only [h]
    rw [baseOf, hw, toNat_W (hle c u (h2 c u rfl))]
  · rintro c u i rfl
    simp only [AtPos] at h
    have hw : d.w 2103 = W u := by
      fin_cases c <;> simp only [finVal, Loop, Rem] at h <;> simp only [h]
    rw [baseOf, hw, toNat_W (hle c u (h3 c u i rfl))]

/-- **The tile index read off a state of the phase is the tile index of its position.** -/
theorem tileOf_eq (hpre : Pre P L mem0) {pos : Pos} {d : D} (hr : RefAt P g pos d) :
    tileOf P g d = tileAt P g pos := by
  obtain ⟨hb1, hb2, hb3⟩ := base_eq hpre hr
  have hs := hr.site
  cases pos with
  | entry => simp only [tileOf, hs, Pos.site, tileAt]
  | poll c u =>
    simp only [tileOf, hs, Pos.site, hb1 c u rfl, tileAt, tile]
    fin_cases c <;> simp
  | arrive c u =>
    simp only [tileOf, hs, Pos.site, hb2 c u rfl, tileAt, tile]
    fin_cases c <;> simp
  | load c u i =>
    have hi := i.isLt
    simp only [tileOf, hs, Pos.site, hb3 c u i rfl, tileAt, tile]
    rw [show (16 + (70 * c.val + i.val) - 16) / 70 = c.val by omega]
    split_ifs <;> omega
  | tail j =>
    have hj := j.isLt
    simp only [tileOf, hs, Pos.site, tileAt]
    split_ifs <;> first | rfl | omega

/-- **The counted events left read off a state of the phase are those of its position.** -/
theorem leftOf_eq (hpre : Pre P L mem0) {pos : Pos} {d : D} (hr : RefAt P g pos d) :
    leftOf P g d = leftAt P g pos := by
  have ht := tileOf_eq hpre hr
  have hs := hr.site
  cases pos with
  | entry => simp only [leftOf, hs, Pos.site, leftAt]
  | poll c u =>
    have hc := c.isLt
    simp only [leftOf, hs, Pos.site, ht, tileAt, leftAt]
    split_ifs <;> first | rfl | omega
  | arrive c u => simp only [leftOf, hs, Pos.site, ht, tileAt, leftAt]
  | load c u i =>
    have hi := i.isLt
    simp only [leftOf, hs, Pos.site, ht, tileAt, leftAt]
    rw [show (16 + (70 * c.val + i.val) - 16) % 70 = i.val by omega]
  | tail j =>
    have hj := j.isLt
    simp only [leftOf, hs, Pos.site, leftAt]
    split_ifs <;> omega

/-- **Fields `tile_le`, `tile_start` and `arrLoadFull`** at a state of the phase, with the tile
index read off the state: it is at most the tile count; it is 0 at the barrier (instruction
1402); and the thread has made one arrival on and issued 70 loads completing on the "full"
mbarrier of a stage for every earlier tile of that stage. -/
theorem tile_producer (hpre : Pre P L mem0) {k : Nat} {s : D} (hI : Inv P L X g k s) :
    tileOf P g s ≤ tilesOf P g ∧ (s.site.pc ≤ 1402 → tileOf P g s = 0) ∧ ∀ st : Fin 3,
      uses 3 (tileOf P g s) st.val ≤
          arrivals ((Bar.loadFull st).loc L (g / L.block)) ((X.tr g).take k) ∧
        70 * uses 3 (tileOf P g s) st.val ≤
          ((X.tr g).take k).countP (issuesTo ((Bar.loadFull st).loc L (g / L.block))) := by
  obtain ⟨pos, hr, hl⟩ := hI
  rw [tileOf_eq hpre hr]
  refine ⟨tileAt_le hr, fun hpc => ?_, fun st => counts_at hr hl st⟩
  rw [hr.site] at hpc
  rcases site_pc pos with ⟨rfl, -⟩ | ⟨-, h, -⟩
  · rfl
  · omega

/-- **Field `left_dec`** for a step of the phase, with the counted events left read off the
states: the successor is a state of the phase with one event less left when the event counts
(every event but a failed poll), or it is the exit state and the event was the last one left. -/
theorem leftOf_dec (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hg : g < L.threads) (hw : warp g = 4) {k : Nat} {s s' : D} {e : Event}
    (he : X.get (g, k) = some e) (hσ : Frame.stateAt (code L) X g k = some (some s))
    (hI : Inv P L X g k s) (hn : Thread.next L g s e = some (some s')) :
    (Inv P L X g (k + 1) s' ∧ leftOf P g s' + (if e.counts then 1 else 0) = leftOf P g s) ∨
      (Out P L X g (k + 1) s' ∧ (if e.counts then 1 else 0) = leftOf P g s) := by
  obtain ⟨pos, w, p, x, rfl, hr, hl, hev, d', hd', hsucc⟩ :=
    producer_good hpre hX hg hw he hσ hI
  rw [hd'] at hn
  obtain rfl := Option.some.inj (Option.some.inj hn)
  have h1 := left_led hr
  have h2 := ledEv_counted L (g / L.block) hev
  rw [leftOf_eq hpre hr]
  rcases hsucc with ⟨pos', hr', hl'⟩ | ⟨hE, hl'⟩
  · have h3 := left_led hr'
    rw [hl'] at h3
    simp only [Led.counted, Led.add_def] at h1 h2 h3
    refine .inl ⟨⟨pos', hr', by rw [ledOf_succ he, hl, hl']⟩, ?_⟩
    rw [leftOf_eq hpre hr']
    omega
  · have h3 := exit_counted P g
    rw [hl'] at h3
    simp only [Led.counted, Led.add_def] at h1 h2 h3
    exact .inr ⟨⟨hE, by rw [ledOf_succ he, hl, hl']⟩, by omega⟩

/-! ### Field `bar0` -/

/-- Six `bar.sync 0` instructions lie below an instruction from 1403 to 3113. -/
theorem bar0_mid {pc : Nat} (h1 : 1402 < pc) (h2 : pc ≤ 3113) :
    (bar0Pcs.filter (· < pc)).length = 6 := by
  have e1 : decide (85 < pc) = true := decide_eq_true (by omega)
  have e2 : decide (110 < pc) = true := decide_eq_true (by omega)
  have e3 : decide (379 < pc) = true := decide_eq_true (by omega)
  have e4 : decide (620 < pc) = true := decide_eq_true (by omega)
  have e5 : decide (621 < pc) = true := decide_eq_true (by omega)
  have e6 : decide (1402 < pc) = true := decide_eq_true (by omega)
  have e7 : decide (3113 < pc) = false := decide_eq_false (by omega)
  have e8 : decide (3775 < pc) = false := decide_eq_false (by omega)
  have e9 : decide (3834 < pc) = false := decide_eq_false (by omega)
  simp [bar0Pcs, List.filter, e1, e2, e3, e4, e5, e6, e7, e8, e9]

/-- **The `bar.sync 0` count of a position** is the number of `bar.sync 0` instructions below
the position's instruction. -/
theorem led_bar0 (P : Params) (g : Nat) (pos : Pos) :
    (led P g pos).bars = (bar0Pcs.filter (· < pos.site.pc)).length := by
  rcases site_pc pos with ⟨rfl, -⟩ | ⟨hne, h1, h2⟩
  · rfl
  · rw [bar0_mid h1 (by omega)]
    cases pos with
    | entry => exact absurd rfl hne
    | poll c u => rfl
    | arrive c u => rfl
    | load c u i => rfl
    | tail j => rfl

/-- **Field `bar0`** at a state of the phase. -/
theorem bar0_producer {k : Nat} {s : D} (hI : Inv P L X g k s) :
    ((X.tr g).take k).countP (Execution.isBarId 0) = (bar0Pcs.filter (· < s.site.pc)).length := by
  obtain ⟨pos, hr, hl⟩ := hI
  rw [hr.site, ← led_bar0 P g pos, ← hl]
  rfl

/-- **Field `bar0`** at the exit of the phase. -/
theorem bar0_out {k : Nat} {s : D} (ho : Out P L X g k s) :
    ((X.tr g).take k).countP (Execution.isBarId 0) = (bar0Pcs.filter (· < s.site.pc)).length := by
  obtain ⟨he, hl⟩ := ho
  have h6 : (ledExit P g).bars = 6 := by
    unfold ledExit
    split_ifs <;> rfl
  rw [he.site, show ((X.tr g).take k).countP (Execution.isBarId 0) = (ledExit P g).bars from
    congrArg Led.bars hl, h6]
  rfl

/-! ### The events a state can fire -/

/-- **Every event that a concrete state of the phase can fire is the closed-form event of its
position** (the template-level form of `event_at`: no trace is involved). -/
theorem fires_ev (hpre : Pre P L mem0) (hg : g < L.threads) (hw : warp g = 4) {pos : Pos}
    {s : D} (hr : RefAt P g pos s) {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hat : (code L g).AtD s t) (hc : kernel.code[s.site.pc]? = some ins)
    (hf : Fires s.site.pc (eventTmpl Assumptions.all L g t ins.op) e o) : Ev P L g pos e := by
  obtain ⟨site, w, p, x⟩ := s
  obtain rfl : site = pos.site := hr.site
  exact (good_at hpre hg hw pos hr hat hc hf).1

/-- An event of the phase is a barrier arrival, a poll, an mbarrier arrival or a tensor load
issue (so: no warp collective, no matrix event, no memory access, no exit). -/
theorem ev_kinds {pos : Pos} {e : Event} (h : Ev P L g pos e) :
    (∃ id cnt m, e.kind = .bar id cnt m) ∨ (∃ l q ok acq sc, e.kind = .wait l q ok acq sc) ∨
      (∃ l tx n rel sc, e.kind = .arrive l tx n rel sc) ∨ ∃ a sp, e.kind = .tensorIssue a sp := by
  cases pos with
  | entry => rw [show e = _ from h]; exact .inl ⟨_, _, _, rfl⟩
  | poll c u => obtain ⟨ok, rfl⟩ := h; exact .inr (.inl ⟨_, _, _, _, _, rfl⟩)
  | arrive c u => rw [show e = _ from h]; exact .inr (.inr (.inl ⟨_, _, _, _, _, rfl⟩))
  | load c u i => rw [show e = _ from h]; exact .inr (.inr (.inr ⟨_, _, rfl⟩))
  | tail j => obtain ⟨ok, rfl⟩ := h; exact .inr (.inl ⟨_, _, _, _, _, rfl⟩)

/-- An event of the phase is no arrival on, no load completing on and no successful poll of
the state mbarrier of the thread's block. -/
theorem ev_state_free (hpre : Pre P L mem0) {pos : Pos} {e : Event} (h : Ev P L g pos e) :
    arrivesOn (Bar.state.loc L (g / L.block)) e = false ∧
      issuesTo (Bar.state.loc L (g / L.block)) e = false ∧
      okPoll (Bar.state.loc L (g / L.block)) e = false := by
  have hne : ∀ st : Fin 3, emptyLoc L (g / L.block) st ≠ Bar.state.loc L (g / L.block) :=
    fun st h => by cases (Bar.loc_inj h).1
  have hnf : ∀ st : Fin 3, fullLoc L (g / L.block) st ≠ Bar.state.loc L (g / L.block) :=
    fun st h => by cases (Bar.loc_inj h).1
  cases pos with
  | entry => rw [show e = _ from h]; exact ⟨rfl, rfl, rfl⟩
  | poll c u =>
    obtain ⟨ok, rfl⟩ := h
    refine ⟨rfl, rfl, ?_⟩
    cases ok
    · rfl
    · simp [okPoll, sourceWaitSuccess, hne]
  | arrive c u =>
    rw [show e = _ from h]
    refine ⟨?_, rfl, rfl⟩
    simp [arrivesOn, sourceArrive, hnf]
  | load c u i =>
    rw [show e = _ from h]
    refine ⟨rfl, ?_, rfl⟩
    simp [issuesTo, tileLoad, fullLoc_eq hpre, hnf]
  | tail j =>
    obtain ⟨ok, rfl⟩ := h
    refine ⟨rfl, rfl, ?_⟩
    cases ok
    · rfl
    · simp [okPoll, sourceWaitSuccess, hne]

/-! ### Field `poll` -/

/-- **Field `poll`** at a poll state of the phase: the polled mbarrier is the "empty" mbarrier
of a stage `st` of the thread's block; the thread is the load leader; its successful polls of
that mbarrier so far are one per earlier tile of the stage (`roundOf (.loadEmpty st)` of the
tile index read off the state); the instruction is past 1402; and every wait event the state
can fire is on that mbarrier, with the parity of those polls plus one. -/
theorem poll_producer (hpre : Pre P L mem0) (hg : g < L.threads) (hw : warp g = 4) {k : Nat}
    {s : D} (hI : Inv P L X g k s) (hpoll : ∃ j, s.site = .mbarWait j) :
    ∃ st : Fin 3, g = loadLeader L (g / L.block) ∧
      okPolls ((Bar.loadEmpty st).loc L (g / L.block)) ((X.tr g).take k) =
        uses 3 (tileOf P g s) st.val ∧ 1402 < s.site.pc ∧
      ∀ {t : TState} {ins : Instr} {e : Event} {o : Option TState},
        (code L g).AtD s t → kernel.code[s.site.pc]? = some ins →
        Fires s.site.pc (eventTmpl Assumptions.all L g t ins.op) e o →
        ∀ l q ok acq sc, e.kind = .wait l q ok acq sc →
          l = (Bar.loadEmpty st).loc L (g / L.block) ∧
            q % 2 = (okPolls l ((X.tr g).take k) + 1) % 2 := by
  obtain ⟨pos, hr, hl⟩ := hI
  obtain ⟨j, hj⟩ := hpoll
  have hne : pos ≠ .entry := by
    rintro rfl
    rw [hr.site] at hj
    cases hj
  have ht := lead_of hr hne
  have hpc : 1402 < s.site.pc := by
    rw [hr.site]
    rcases site_pc pos with ⟨h, -⟩ | ⟨-, h, -⟩
    · exact absurd h hne
    · exact h
  -- the stage and the count, by position
  have key : ∃ tt, (∀ e, Ev P L g pos e → ∃ pc ok, e = ⟨pc,
      .wait (emptyLoc L (g / L.block) (stage tt)) (par tt) ok true .cta⟩) ∧
      okPolls (emptyLoc L (g / L.block) (stage tt)) ((X.tr g).take k) = tt / 3 ∧
      okPolls (emptyLoc L (g / L.block) (stage tt)) ((X.tr g).take k) =
        uses 3 (tileAt P g pos) (stage tt).val := by
    cases pos with
    | entry => exact absurd rfl hne
    | arrive c u => rw [hr.site] at hj; cases hj
    | load c u i => rw [hr.site] at hj; cases hj
    | poll c u =>
      have h3 : tile c u % 3 < 3 := Nat.mod_lt _ (by decide)
      refine ⟨tile c u, fun e he => ?_, ?_, ?_⟩
      · obtain ⟨ok, rfl⟩ := he
        exact ⟨_, ok, rfl⟩
      · rw [led_e hl]; simp only [stage]; omega
      · rw [led_e hl]; rfl
    | tail j' =>
      have h3 : (tilesOf P g + j'.val) % 3 < 3 := Nat.mod_lt _ (by decide)
      have hj' := j'.isLt
      refine ⟨tilesOf P g + j'.val, fun e he => ?_, ?_, ?_⟩
      · obtain ⟨ok, rfl⟩ := he
        exact ⟨_, ok, rfl⟩
      · rw [led_e hl]; simp only [stage]; omega
      · rw [led_e hl]; simp only [stage, tileAt, uses_eq]; omega
  obtain ⟨tt, hev, hp, hu⟩ := key
  refine ⟨stage tt, leader_eq hpre ht, by rw [tileOf_eq hpre hr]; exact hu, hpc, ?_⟩
  intro t ins e o hat hc hf l q ok acq sc hk
  obtain ⟨pc, ok', rfl⟩ := hev e (fires_ev hpre hg hw hr hat hc hf)
  cases hk
  refine ⟨rfl, ?_⟩
  rw [show okPolls ((Bar.loadEmpty (stage tt)).loc L (g / L.block)) ((X.tr g).take k) = tt / 3
    from hp]
  simp only [par]
  omega

/-- **Field `pollStage`** is vacuous in the phase: a wait event that a poll state of the phase
fires is on an "empty" mbarrier of the load pipeline, hence on no "full" mbarrier of the load
or of the store pipeline. -/
theorem pollStage_producer (hpre : Pre P L mem0) (hg : g < L.threads) (hw : warp g = 4)
    {k : Nat} {s : D} (hI : Inv P L X g k s) (hpoll : ∃ j, s.site = .mbarWait j)
    {t : TState} {ins : Instr} {e : Event} {o : Option TState} (hat : (code L g).AtD s t)
    (hc : kernel.code[s.site.pc]? = some ins)
    (hf : Fires s.site.pc (eventTmpl Assumptions.all L g t ins.op) e o) {l : Loc} {q : Nat}
    {ok acq : Bool} {sc : MbarScope} (hk : e.kind = .wait l q ok acq sc) :
    (∀ st : Fin 3, l ≠ (Bar.loadFull st).loc L (g / L.block)) ∧
      ∀ ot : Fin 2, l ≠ (Bar.storeFull ot).loc L (g / L.block) := by
  obtain ⟨st, -, -, -, hfire⟩ := poll_producer hpre hg hw hI hpoll
  obtain ⟨rfl, -⟩ := hfire hat hc hf l q ok acq sc hk
  exact ⟨fun st' h => (by cases (Bar.loc_inj h).1), fun ot h => (by cases (Bar.loc_inj h).1)⟩

/-! ### Field `barStep` -/

/-- A position whose ledger is the entry's plus one `bar.sync 0` has tile index 0. -/
theorem tile_of_led {pos : Pos} (h : led P g pos = led P g .entry + dBar) :
    tileAt P g pos = 0 := by
  have hb : (led P g pos).polls = 1 := by rw [h]; rfl
  cases pos with
  | entry =>
    have : (led P g .entry).bars = (led P g .entry + dBar).bars := congrArg Led.bars h
    simp [led, ledEntry, dBar, Led.add_def] at this
  | poll c u => simp only [led, ledAt] at hb; simp only [tileAt]; omega
  | arrive c u => simp only [led, ledAt] at hb; omega
  | load c u i => simp only [led, ledAt] at hb; omega
  | tail j => simp only [led, ledAt] at hb; simp only [tileAt]; omega

/-- **Field `barStep`** for the barrier of the phase: a barrier event at a state of the phase
is fired at the entry (instruction 1402, sub-step 0, tile index 0). The successor is at a later
instruction; it is a position of the load leader with tile index 0, or, for a lane other than
lane 0, the exit state at instruction 3113 (where the tile index is the tile count: the field's
"not smaller"). -/
theorem barStep_producer (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads) (hw : warp g = 4)
    {k pc id : Nat} {cnt : Option Nat} {m : BarMode} {s s' : D}
    (he : X.get (g, k) = some ⟨pc, .bar id cnt m⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hI : Inv P L X g k s)
    (hn : Thread.next L g s ⟨pc, .bar id cnt m⟩ = some (some s')) :
    s.site.pc = 1402 ∧ s.site.sub = 0 ∧ s.site.pc < s'.site.pc ∧
      ((∃ pos', RefAt P g pos' s' ∧ tileAt P g pos' = 0) ∨ (tid g ≠ 128 ∧ Exit P g s')) := by
  obtain ⟨pos, w, p, x, rfl, hr, hl, hev, d', hd', hsucc⟩ :=
    producer_good hpre hX hg hw he hσ hI
  rw [hd'] at hn
  obtain rfl := Option.some.inj (Option.some.inj hn)
  obtain ⟨rfl, -⟩ := bar_shape hl hev
  have hdelta : ledEv L (g / L.block) ⟨pc, .bar id cnt m⟩ = dBar := by
    rw [show (⟨pc, .bar id cnt m⟩ : Event) = _ from hev]
    rfl
  rw [hdelta] at hsucc
  refine ⟨rfl, rfl, ?_, ?_⟩
  · rcases hsucc with ⟨pos', hr', hl'⟩ | ⟨hE, -⟩
    · rw [hr'.site]
      rcases site_pc pos' with ⟨rfl, -⟩ | ⟨-, h, -⟩
      · have : (led P g .entry).bars = (led P g .entry + dBar).bars := congrArg Led.bars hl'
        simp [led, ledEntry, dBar, Led.add_def] at this
      · exact h
    · rw [hE.site]
      show (Site.bar 5).pc < (Site.bar 7).pc
      decide
  · rcases hsucc with ⟨pos', hr', hl'⟩ | ⟨hE, hl'⟩
    · exact .inl ⟨pos', hr', tile_of_led hl'⟩
    · refine .inr ⟨fun ht => ?_, hE⟩
      have : (ledExit P g).polls = (led P g .entry + dBar).polls := congrArg Led.polls hl'
      simp [ledExit, ht, ledAt, led, ledEntry, dBar, Led.add_def] at this

/-! ### Classes of events the phase does not touch -/

/-- A class of events that no event of the phase belongs to. -/
def Untouched (P : Params) (L : Launch) (g : Nat) (c : Event → Bool) : Prop :=
  ∀ pos e, Ev P L g pos e → c e = false

/-- A class that holds no barrier arrival, no poll, no mbarrier arrival and no tensor load issue
(the warp collectives, the matrix events, the memory accesses, the exit) is one that no event of
the phase belongs to. -/
theorem untouched_of_kinds {c : Event → Bool}
    (hc : ∀ e : Event, ((∃ id cnt m, e.kind = .bar id cnt m) ∨
      (∃ l q ok acq sc, e.kind = .wait l q ok acq sc) ∨
      (∃ l tx n rel sc, e.kind = .arrive l tx n rel sc) ∨ ∃ a sp, e.kind = .tensorIssue a sp) →
      c e = false) : Untouched P L g c :=
  fun _ e h => hc e (ev_kinds h)

/-- **A class of events that no event of the phase belongs to keeps its count through the
phase**: from the entry before event `k0`, at every later state of the phase, and at its exit,
the count of every such class over the thread's earlier events is the count at the entry. -/
theorem frame_producer (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hg : g < L.threads) (hw : warp g = 4) {k0 k : Nat} (hen : Entered P L X g k0)
    (hk0 : k0 ≤ k) {s : D} (hk : k < (X.tr g).length)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    (Inv P L X g k s ∧ ∀ c, Untouched P L g c →
        ((X.tr g).take k).countP c = ((X.tr g).take k0).countP c) ∨
      ∃ j ≤ k, ∃ s1, Frame.stateAt (code L) X g j = some (some s1) ∧ Out P L X g j s1 ∧
        ∀ c, Untouched P L g c → ((X.tr g).take j).countP c = ((X.tr g).take k0).countP c := by
  obtain ⟨s0, h0, hE⟩ := hen.state
  have hI0 : Inv P L X g k0 s0 :=
    ⟨.entry, ⟨hE.site, hE.tid, hE.p85, hE.p86, hE.p87, hE.p88, hE.scan, hE.elected⟩, hen.led⟩
  refine phase_from (C := code L) (machineSound hpre) hX
    (fun k s => Inv P L X g k s ∧ ∀ c, Untouched P L g c →
      ((X.tr g).take k).countP c = ((X.tr g).take k0).countP c)
    (fun j s1 => Out P L X g j s1 ∧ ∀ c, Untouched P L g c →
      ((X.tr g).take j).countP c = ((X.tr g).take k0).countP c)
    h0 ⟨hI0, fun _ _ => rfl⟩ ?_ k s hk0 hk hσ
  intro k e s s' t ins o he hσ hI _ _ _ _ hn
  obtain ⟨hI, hcnt⟩ := hI
  obtain ⟨pos, w, p, x, rfl, hr, hl, hev, -⟩ := producer_good hpre hX hg hw he hσ hI
  have hcount : ∀ c, Untouched P L g c →
      ((X.tr g).take (k + 1)).countP c = ((X.tr g).take k0).countP c := by
    intro c hc
    rw [count_snoc c he, hc pos e hev, hcnt c hc]
    rfl
  rcases inv_step hpre hX hg hw he hσ hI hn with h | h
  · exact .inl ⟨h, hcount⟩
  · exact .inr ⟨h, hcount⟩

/-- **Field `coll` and field `arrState` through the phase**: at every state of the phase, or at
the exit that the thread took at or before it, the events of a class that the phase does not
touch are those at the entry; the arrivals on, the loads completing on and the successful polls
of the state mbarrier of the thread's block are such classes (`ev_state_free`), and so is every
class of warp collectives, matrix events and memory accesses (`ev_kinds`). -/
theorem state_counts_producer (hpre : Pre P L mem0)
    (hX : Consistent L kernel Assumptions.all mem0 X) (hg : g < L.threads) (hw : warp g = 4)
    {k0 k : Nat} (hen : Entered P L X g k0) (hk0 : k0 ≤ k) {s : D} (hk : k < (X.tr g).length)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    ∃ j ≤ k, (j = k ∨ ∃ s1, Frame.stateAt (code L) X g j = some (some s1) ∧ Out P L X g j s1) ∧
      arrivals (Bar.state.loc L (g / L.block)) ((X.tr g).take j) =
        arrivals (Bar.state.loc L (g / L.block)) ((X.tr g).take k0) ∧
      ((X.tr g).take j).countP (issuesTo (Bar.state.loc L (g / L.block))) =
        ((X.tr g).take k0).countP (issuesTo (Bar.state.loc L (g / L.block))) ∧
      okPolls (Bar.state.loc L (g / L.block)) ((X.tr g).take j) =
        okPolls (Bar.state.loc L (g / L.block)) ((X.tr g).take k0) := by
  have ha : Untouched P L g (arrivesOn (Bar.state.loc L (g / L.block))) :=
    fun pos e h => (ev_state_free hpre h).1
  have hi : Untouched P L g (issuesTo (Bar.state.loc L (g / L.block))) :=
    fun pos e h => (ev_state_free hpre h).2.1
  have hp : Untouched P L g (okPoll (Bar.state.loc L (g / L.block))) :=
    fun pos e h => (ev_state_free hpre h).2.2
  rcases frame_producer hpre hX hg hw hen hk0 hk hσ with ⟨-, h⟩ | ⟨j, hj, s1, hs1, ho, h⟩
  · exact ⟨k, le_rfl, .inl rfl, h _ ha, h _ hi, h _ hp⟩
  · exact ⟨j, hj, .inr ⟨s1, hs1, ho⟩, h _ ha, h _ hi, h _ hp⟩

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Producer
