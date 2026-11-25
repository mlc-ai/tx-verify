-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Producer.Trace
public import Kernels.FlashKdaFwd.Proof.Protocol.LoadRing

@[expose] public section

/-! # Exports of the Producer phase: facts about the events of a thread of the load warp

What the layers above read off the reference invariant of the Producer phase (instructions
1403 to 2105, and the `bar.sync 0` at 1402 that enters it). Two levels:

**Position level** (no trace, no machine): from the register facts of a position (`RefAt`), the
ledger of the events before it (`ledOf … = led P g pos`) and the closed form of the event
(`Ev`):

* `poll_shape`, `arrive_shape`, `issue_shape`, `bar_shape`: an event of each kind, in closed
  form over a tile index `tt`, with the counts the contracts of the protocol layer ask for
  (`Proof/Protocol/LoadRing.lean`): the successful polls of the "empty" mbarrier of the stage,
  the arrivals on its "full" mbarrier, the loads completing on it, six `bar.sync 0`;
* `ev_not_ub`, `ev_kinds`: an event of the phase is no undefined behaviour and is a barrier
  arrival, a poll, an mbarrier arrival or a tensor load issue;
* `tileAt`, `leftAt`: the tile index and the number of counted events left, as functions of
  the position (for the progress instance and the termination bound), with `tileAt_le` and
  `left_led` (the events left plus the events counted so far are constant);
* `counts_at`: at every position the load leader has arrived on, and issued 70 loads to, the
  "full" mbarrier of a stage once per earlier tile of the stage.

**Trace level**: `Entered P L X g k0` says that the thread is at the phase's entry before its
event `k0` (the condition the earlier phases prove); `Left P L X g k` that it left the phase at
or before event `k`. `event_at` gives, for an event `k ≥ k0` at a followed state, a position
with its facts, ledger, closed-form event and a successor state, or `Left`. The corollaries
have the shape of the contract fields, for the events of this phase:

| theorem | contract field |
|---|---|
| `full_arrive_producer` | `LoadFacts.full_arrive` |
| `full_issue_producer` | `LoadFacts.full_issue`, `no_tensor_empty`; `StoreFacts.no_tensor`; fill |
| `empty_poll_producer` | `LoadFacts.empty_poll`; progress `poll` |
| `use_ev_producer` | `InitFacts.use_ev`; `SafetyFacts.mbarFrame` |
| `noUb_producer` | `SafetyFacts.loadNoUb` (the control half) |
| `bar_producer` | `BarFacts` (the sixth `bar.sync 0`) |
| `issues_le_producer` | `LifeFacts.full_issues` (the bound up to the phase's exit) |
| `progress_producer` | progress `tile_le`, `bar0`, `arrLoadFull` |
| `left_dec_producer` | progress `left_dec` |

The tensor loads' destination footprint is `tileLoad_writeLoc` (which bytes of the block's
shared window the load at position `i` of tile `tt` writes: `InInput`, and the piece `i` by
`pieceOf`). On the source side: `tileLoad_bounds` (the statement of `SafetyFacts.loadBounds`
for the copy of a tile load: only the loads of `v` and `beta` can select an element outside
their tensor) and `tileLoad_ok` (routing, validity and a non-empty box: the first three parts
of the progress premise `TensorSources`). -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Producer
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Protocol (Bar uses loadLeader bar0Before loadBytes InInput)

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 4000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {g : Nat}

/-! ### The tile index and the counted events left -/

/-- **The tile index of a position**: 0 at the entry, the tile being worked on inside the tile
loop, the tile count at the tail. -/
def tileAt (P : Params) (g : Nat) : Pos → Nat
  | .entry => 0
  | .poll c u => tile c u
  | .arrive c u => tile c u
  | .load c u _ => tile c u
  | .tail _ => tilesOf P g

/-- **The counted events left** in the phase at a position (every event but a failed poll
counts): 72 per tile from the poll on, and the three polls of the tail; at the entry also its
`bar.sync 0` (for a lane other than the leader nothing else). -/
def leftAt (P : Params) (g : Nat) : Pos → Nat
  | .entry => if tid g = 128 then 72 * tilesOf P g + 4 else 1
  | .poll c u => 72 * (tilesOf P g - tile c u) + 3
  | .arrive c u => 72 * (tilesOf P g - tile c u) + 2
  | .load c u i => 72 * (tilesOf P g - tile c u) + 1 - i.val
  | .tail j => 3 - j.val

/-- The events of a ledger that count: the barrier arrivals, the mbarrier arrivals, the load
issues and the successful polls. -/
def Led.counted (l : Led) : Nat := l.bars + l.arrs + l.issues + l.polls

/-- The counted events of a thread of the load warp from the launch to the phase's exit. -/
def countedExit (P : Params) (g : Nat) : Nat := if tid g = 128 then 72 * tilesOf P g + 27 else 7

variable {pos : Pos} {d : D}

/-- A state at a position other than the entry is a state of the load leader. -/
theorem lead_of (hr : RefAt P g pos d) (hp : pos ≠ .entry) : tid g = 128 := by
  have h := hr.pos
  cases pos with
  | entry => exact absurd rfl hp
  | poll c u => simp only [AtPos, Lead] at h; exact h.1.1
  | arrive c u => simp only [AtPos, Lead] at h; exact h.1.1
  | load c u i => simp only [AtPos, Lead] at h; exact h.1.1
  | tail j => simp only [AtPos] at h; exact h.1

/-- Inside the tile loop the tile index is below the tile count. -/
theorem tile_lt (hr : RefAt P g pos d) :
    (∀ c u, pos = .poll c u → tile c u < tilesOf P g) ∧
    (∀ c u, pos = .arrive c u → tile c u < tilesOf P g) ∧
    (∀ c u i, pos = .load c u i → tile c u < tilesOf P g) := by
  have h := hr.pos
  refine ⟨?_, ?_, ?_⟩
  · rintro c u rfl
    simp only [AtPos] at h
    fin_cases c <;> simp only [finVal, Loop, Rem] at h
    · show u < tilesOf P g; omega
    · show u + 1 < tilesOf P g; omega
    · show u < tilesOf P g; omega
  · rintro c u rfl
    simp only [AtPos] at h
    fin_cases c <;> simp only [finVal, Loop, Rem] at h
    · show u < tilesOf P g; omega
    · show u + 1 < tilesOf P g; omega
    · show u < tilesOf P g; omega
  · rintro c u i rfl
    simp only [AtPos] at h
    fin_cases c <;> simp only [finVal, Loop, Rem] at h
    · show u < tilesOf P g; omega
    · show u + 1 < tilesOf P g; omega
    · show u < tilesOf P g; omega

/-- The tile index is at most the tile count. -/
theorem tileAt_le (hr : RefAt P g pos d) : tileAt P g pos ≤ tilesOf P g := by
  obtain ⟨h1, h2, h3⟩ := tile_lt hr
  cases pos with
  | entry => exact Nat.zero_le _
  | poll c u => exact Nat.le_of_lt (h1 c u rfl)
  | arrive c u => exact Nat.le_of_lt (h2 c u rfl)
  | load c u i => exact Nat.le_of_lt (h3 c u i rfl)
  | tail j => exact le_rfl

/-- **The events left and the events counted so far add up to the events of the thread up to
the phase's exit.** -/
theorem left_led (hr : RefAt P g pos d) :
    leftAt P g pos + (led P g pos).counted = countedExit P g := by
  obtain ⟨h1, h2, h3⟩ := tile_lt hr
  cases pos with
  | entry =>
    simp only [leftAt, led, ledEntry, Led.counted, countedExit]
    split_ifs <;> omega
  | poll c u =>
    have ht := lead_of hr (by simp)
    have := h1 c u rfl
    simp only [leftAt, led, ledAt, Led.counted, countedExit, ht, ↓reduceIte]
    omega
  | arrive c u =>
    have ht := lead_of hr (by simp)
    have := h2 c u rfl
    simp only [leftAt, led, ledAt, Led.counted, countedExit, ht, ↓reduceIte]
    omega
  | load c u i =>
    have ht := lead_of hr (by simp)
    have := h3 c u i rfl
    have := i.isLt
    simp only [leftAt, led, ledAt, Led.counted, countedExit, ht, ↓reduceIte]
    omega
  | tail j =>
    have ht := lead_of hr (by simp)
    have := j.isLt
    simp only [leftAt, led, ledAt, Led.counted, countedExit, ht, ↓reduceIte]
    omega

/-- The counted events at the exit. -/
theorem exit_counted (P : Params) (g : Nat) : (ledExit P g).counted = countedExit P g := by
  unfold ledExit countedExit
  split_ifs
  · simp only [ledAt, Led.counted]
    omega
  · rfl

/-- The ledger of an event counts it once when it counts (every event of the phase but a failed
poll), and not otherwise. -/
theorem ledEv_counted (L : Launch) (c : Nat) {e : Event} (h : Ev P L g pos e) :
    (ledEv L c e).counted = if e.counts then 1 else 0 := by
  cases pos with
  | entry => rw [show e = _ from h]; rfl
  | poll c u => obtain ⟨ok, rfl⟩ := h; cases ok <;> rfl
  | arrive c u => rw [show e = _ from h]; rfl
  | load c u i => rw [show e = _ from h]; rfl
  | tail j => obtain ⟨ok, rfl⟩ := h; cases ok <;> rfl

/-! ### Ledger projections -/

section
variable {es : List Event} {a b n : Nat} (hl : ledOf L (g / L.block) es = ledAt a b n)
include hl

theorem led_bars : es.countP (Execution.isBarId 0) = 6 := congrArg Led.bars hl

theorem led_e (s : Fin 3) : okPolls (emptyLoc L (g / L.block) s) es = (a + 2 - s.val) / 3 := by
  fin_cases s
  · exact congrArg Led.e0 hl
  · exact congrArg Led.e1 hl
  · exact congrArg Led.e2 hl

theorem led_a (s : Fin 3) : arrivals (fullLoc L (g / L.block) s) es = (b + 2 - s.val) / 3 := by
  fin_cases s
  · exact congrArg Led.a0 hl
  · exact congrArg Led.a1 hl
  · exact congrArg Led.a2 hl

theorem led_i (s : Fin 3) :
    es.countP (issuesTo (fullLoc L (g / L.block) s)) = issuedOn n s.val := by
  fin_cases s
  · exact congrArg Led.i0 hl
  · exact congrArg Led.i1 hl
  · exact congrArg Led.i2 hl

end

/-- The number of tiles `t' < t` on stage `s`, in the protocol layer's notation. -/
theorem uses_eq (t s : Nat) : uses 3 t s = (t + 2 - s) / 3 := rfl

/-- The loads on the "full" mbarrier of the stage of tile `tt` before the load at position `i`
of that tile. -/
theorem issuedOn_stage (tt i : Nat) (hi : i < 70) :
    issuedOn (70 * tt + i) (stage tt).val = 70 * (tt / 3) + i := by
  have h1 : (70 * tt + i) / 70 = tt := by omega
  have h2 : (70 * tt + i) % 70 = i := by omega
  have h3 : tt % 3 < 3 := Nat.mod_lt _ (by decide)
  simp only [issuedOn, stage, h1, h2, ↓reduceIte]
  omega

/-! ### The events of the phase, by kind -/

variable {es : List Event} {e : Event}

/-- An event of the phase is no undefined behaviour. -/
theorem ev_not_ub (h : Ev P L g pos e) : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
  intro pc f he
  subst he
  cases pos with
  | entry => cases h
  | poll c u => obtain ⟨ok, h⟩ := h; cases h
  | arrive c u => cases h
  | load c u i => cases h
  | tail j => obtain ⟨ok, h⟩ := h; cases h

/-- An event of the phase is at the instruction of its position. -/
theorem ev_pc (h : Ev P L g pos e) : e.pc = pos.site.pc := by
  cases pos with
  | entry => rw [show e = _ from h]; rfl
  | poll c u => obtain ⟨ok, rfl⟩ := h; rfl
  | arrive c u => rw [show e = _ from h]
  | load c u i => rw [show e = _ from h]
  | tail j => obtain ⟨ok, rfl⟩ := h; rfl

/-- **A barrier event of the phase** is the `bar.sync 0` at instruction 1402, the thread's
sixth. -/
theorem bar_shape (hl : ledOf L (g / L.block) es = led P g pos) {pc id : Nat} {cnt : Option Nat}
    {mode : BarMode} (hev : Ev P L g pos ⟨pc, .bar id cnt mode⟩) :
    pos = .entry ∧ pc = 1402 ∧ id = 0 ∧ cnt = none ∧ mode = .sync ∧
      es.countP (Execution.isBarId 0) = 5 := by
  cases pos with
  | entry =>
    cases hev
    exact ⟨rfl, rfl, rfl, rfl, rfl, congrArg Led.bars hl⟩
  | poll c u => obtain ⟨ok, h⟩ := hev; cases h
  | arrive c u => cases hev
  | load c u i => cases hev
  | tail j => obtain ⟨ok, h⟩ := hev; cases h

/-- **A poll of the phase**: the load leader's, of the "empty" mbarrier of the stage of a tile
index `tt` (in the loop the tile being loaded, in the tail `T + j`), with the parity `par tt`,
acquiring; before it the leader has polled that mbarrier successfully `tt / 3` times, which is
once per earlier tile of the stage, and made six `bar.sync 0`. -/
theorem poll_shape (hr : RefAt P g pos d) (hl : ledOf L (g / L.block) es = led P g pos)
    {pc q : Nat} {m : Loc} {ok acq : Bool} {sc : MbarScope}
    (hev : Ev P L g pos ⟨pc, .wait m q ok acq sc⟩) :
    ∃ tt, m = emptyLoc L (g / L.block) (stage tt) ∧ q = par tt ∧ acq = true ∧ sc = .cta ∧
      tid g = 128 ∧ okPolls m es = tt / 3 ∧
      okPolls m es = uses 3 (tileAt P g pos) (stage tt).val ∧
      es.countP (Execution.isBarId 0) = 6 := by
  have ht := lead_of hr (by rintro rfl; cases hev)
  cases pos with
  | entry => cases hev
  | arrive c u => cases hev
  | load c u i => cases hev
  | poll c u =>
    obtain ⟨ok', h⟩ := hev
    cases h
    have h3 : tile c u % 3 < 3 := Nat.mod_lt _ (by decide)
    refine ⟨tile c u, rfl, rfl, rfl, rfl, ht, ?_, ?_, led_bars hl⟩
    · rw [led_e hl]; simp only [stage]; omega
    · rw [led_e hl]; rfl
  | tail j =>
    obtain ⟨ok', h⟩ := hev
    cases h
    have h3 : (tilesOf P g + j.val) % 3 < 3 := Nat.mod_lt _ (by decide)
    have hj := j.isLt
    refine ⟨tilesOf P g + j.val, rfl, rfl, rfl, rfl, ht, ?_, ?_, led_bars hl⟩
    · rw [led_e hl]; simp only [stage]; omega
    · rw [led_e hl]; simp only [stage, tileAt, uses_eq]; omega

/-- **An arrival of the phase**: the load leader's, on the "full" mbarrier of the stage of a
tile `tt < T`, expecting 17984 bytes; before it the leader has arrived on that mbarrier
`tt / 3` times and polled the stage's "empty" mbarrier successfully `tt / 3 + 1` times. -/
theorem arrive_shape (hr : RefAt P g pos d) (hl : ledOf L (g / L.block) es = led P g pos)
    {pc tx cnt : Nat} {m : Loc} {rel : Bool} {sc : MbarScope}
    (hev : Ev P L g pos ⟨pc, .arrive m tx cnt rel sc⟩) :
    ∃ tt, tt < tilesOf P g ∧ tileAt P g pos = tt ∧ m = fullLoc L (g / L.block) (stage tt) ∧
      tx = 17984 ∧ cnt = 1 ∧ rel = true ∧ sc = .cta ∧ tid g = 128 ∧
      arrivals m es = tt / 3 ∧ okPolls (emptyLoc L (g / L.block) (stage tt)) es = tt / 3 + 1 ∧
      es.countP (Execution.isBarId 0) = 6 := by
  have ht := lead_of hr (by rintro rfl; cases hev)
  obtain ⟨-, h2, -⟩ := tile_lt hr
  cases pos with
  | entry => cases hev
  | poll c u => obtain ⟨ok, h⟩ := hev; cases h
  | load c u i => cases hev
  | tail j => obtain ⟨ok, h⟩ := hev; cases h
  | arrive c u =>
    cases hev
    have h3 : tile c u % 3 < 3 := Nat.mod_lt _ (by decide)
    refine ⟨tile c u, h2 c u rfl, rfl, rfl, rfl, rfl, rfl, rfl, ht, ?_, ?_, led_bars hl⟩
    · rw [led_a hl]; simp only [stage]; omega
    · rw [led_e hl]; simp only [stage]; omega

/-- **A tensor load of the phase**: the load leader's load at a position `i < 70` of a tile
`tt < T`: the copy `tileLoad P L g tt i` through the map of parameter object `mapFin i`; before
it the leader has issued `70 (tt / 3) + i` loads on the "full" mbarrier of the tile's stage,
polled the stage's "empty" mbarrier successfully `tt / 3 + 1` times and arrived on the "full"
one `tt / 3 + 1` times. -/
theorem issue_shape (hr : RefAt P g pos d) (hl : ledOf L (g / L.block) es = led P g pos)
    {pc al : Nat} {sp : TensorCopy.Spec} (hev : Ev P L g pos ⟨pc, .tensorIssue al sp⟩) :
    ∃ tt i, tt < tilesOf P g ∧ i < 70 ∧ tileAt P g pos = tt ∧ al = P.objectBase (mapFin i) ∧
      sp = tileLoad P L g tt i ∧ tid g = 128 ∧
      es.countP (issuesTo (fullLoc L (g / L.block) (stage tt))) = 70 * (tt / 3) + i ∧
      okPolls (emptyLoc L (g / L.block) (stage tt)) es = tt / 3 + 1 ∧
      arrivals (fullLoc L (g / L.block) (stage tt)) es = tt / 3 + 1 ∧
      es.countP (Execution.isBarId 0) = 6 := by
  have ht := lead_of hr (by rintro rfl; cases hev)
  obtain ⟨-, -, h2⟩ := tile_lt hr
  cases pos with
  | entry => cases hev
  | poll c u => obtain ⟨ok, h⟩ := hev; cases h
  | arrive c u => cases hev
  | tail j => obtain ⟨ok, h⟩ := hev; cases h
  | load c u i =>
    cases hev
    have h3 : tile c u % 3 < 3 := Nat.mod_lt _ (by decide)
    have hi := i.isLt
    refine ⟨tile c u, i.val, h2 c u i rfl, hi, rfl, rfl, rfl, ht, ?_, ?_, ?_, led_bars hl⟩
    · rw [led_i hl]
      exact issuedOn_stage _ _ hi
    · rw [led_e hl]; simp only [stage]; omega
    · rw [led_a hl]; simp only [stage]; omega

/-- **Counts at every position of the load leader**, for progress: for each stage `s`, one
arrival on the "full" mbarrier and 70 loads completing on it per earlier tile of the stage (the
tiles below the position's tile index). -/
theorem counts_at (hr : RefAt P g pos d) (hl : ledOf L (g / L.block) es = led P g pos)
    (s : Fin 3) :
    uses 3 (tileAt P g pos) s.val ≤ arrivals (fullLoc L (g / L.block) s) es ∧
      70 * uses 3 (tileAt P g pos) s.val ≤
        es.countP (issuesTo (fullLoc L (g / L.block) s)) := by
  have hs := s.isLt
  cases pos with
  | entry => simp only [tileAt, uses_eq]; omega
  | poll c u =>
    rw [led_a hl, led_i hl]
    simp only [tileAt, uses_eq, issuedOn]
    rw [show 70 * tile c u / 70 = tile c u by omega]
    omega
  | arrive c u =>
    rw [led_a hl, led_i hl]
    simp only [tileAt, uses_eq, issuedOn]
    rw [show 70 * tile c u / 70 = tile c u by omega]
    omega
  | load c u i =>
    have hi := i.isLt
    rw [led_a hl, led_i hl]
    simp only [tileAt, uses_eq, issuedOn]
    rw [show (70 * tile c u + i.val) / 70 = tile c u by omega]
    omega
  | tail j =>
    rw [led_a hl, led_i hl]
    simp only [tileAt, uses_eq, issuedOn]
    rw [show 70 * tilesOf P g / 70 = tilesOf P g by omega]
    omega

/-- **The loads on a "full" mbarrier never exceed 70 per use of its stage**, at a position. -/
theorem issues_le_at (hr : RefAt P g pos d) (hl : ledOf L (g / L.block) es = led P g pos)
    (s : Fin 3) :
    es.countP (issuesTo (fullLoc L (g / L.block) s)) ≤ 70 * uses 3 (tilesOf P g) s.val := by
  have hs := s.isLt
  obtain ⟨h1, h2, h3⟩ := tile_lt hr
  cases pos with
  | entry =>
    have h : es.countP (issuesTo (fullLoc L (g / L.block) s)) = 0 := by
      simp only [led, ledEntry] at hl
      fin_cases s
      · exact congrArg Led.i0 hl
      · exact congrArg Led.i1 hl
      · exact congrArg Led.i2 hl
    omega
  | poll c u =>
    have := h1 c u rfl
    rw [led_i hl]
    simp only [uses_eq, issuedOn]
    rw [show 70 * tile c u / 70 = tile c u by omega]
    split_ifs <;> omega
  | arrive c u =>
    have := h2 c u rfl
    rw [led_i hl]
    simp only [uses_eq, issuedOn]
    rw [show 70 * tile c u / 70 = tile c u by omega]
    split_ifs <;> omega
  | load c u i =>
    have hi := i.isLt
    have := h3 c u i rfl
    rw [led_i hl]
    simp only [uses_eq, issuedOn]
    rw [show (70 * tile c u + i.val) / 70 = tile c u by omega,
      show (70 * tile c u + i.val) % 70 = i.val by omega]
    split_ifs <;> omega
  | tail j =>
    rw [led_i hl]
    simp only [uses_eq, issuedOn]
    rw [show 70 * tilesOf P g / 70 = tilesOf P g by omega]
    split_ifs <;> omega

/-! ### The destination footprint of a tile load -/

/-- **The position of the load that writes a byte of an input buffer**, from the byte's offset
in the buffer (0 to 18047): the owner function `Owners.piece` of the union-region contract
(`Proof/Protocol/UnionClass.lean`) can be chosen as
`fun l => pieceOf ((l.addr - (L.sharedBase + 32768)) % 18048)`. The 64 bytes from offset 4160
are written by no load (they are attributed to position 16 here). -/
def pieceOf (off : Nat) : Nat :=
  if off < 4096 then off / 256 else if off < 4224 then 16
  else if off < 16512 then 17 + (off - 4224) / 256 else if off < 17024 then 65
  else 66 + (off - 17024) / 256

/-- The bytes a load moves, in the protocol layer's notation. -/
theorem mapBytes_eq (i : Nat) (hi : i < 70) : mapBytes (mapFin i) = loadBytes i := by
  interval_cases i <;> rfl

/-- The destination offsets as a function of the position: three runs of 256-byte pieces,
with the 64 bytes of `beta` (and a 64-byte hole) after the first and the 512 bytes of `g_total`
after the second. -/
theorem dstAbs_form (i : Nat) (hi : i < 70) :
    dstAbs i = 32768 +
      (if i ≤ 16 then 256 * i else if i ≤ 65 then 256 * i - 128 else 256 * i + 128) := by
  interval_cases i <;> rfl

/-- **Where the load at position `i` of tile `tt` writes**: every byte it writes is in the
`loadBytes i` bytes from offset `dstAbs i` of the stage's part of the block's shared window; it
is a byte of input buffer `tt % 3`, and its piece is `i`. -/
theorem tileLoad_writeLoc (hpre : Pre P L mem0) {tt i x y k : Nat} {l : Loc} (hi : i < 70)
    (h : TensorCopy.writeLoc (tileLoad P L g tt i) x y k = some l) :
    InInput L (g / L.block) (stage tt).val l ∧
      P.sharedBase + 18048 * (tt % 3) + dstAbs i ≤ l.addr ∧
      l.addr < P.sharedBase + 18048 * (tt % 3) + dstAbs i + loadBytes i ∧
      pieceOf ((l.addr - (L.sharedBase + 32768)) % 18048) = i := by
  obtain ⟨h1, h2, h3, h4⟩ := writeLoc_range h
  rw [mapBytes_eq i hi] at h4
  have h5 : tt % 3 < 3 := Nat.mod_lt _ (by decide)
  have hb := hpre.sharedBase
  have hd := dstAbs_form i hi
  refine ⟨⟨h1, h2, ?_, ?_⟩, h3, h4, ?_⟩
  · simp only [stage]
    split_ifs at hd <;> omega
  · simp only [stage]
    simp only [loadBytes] at h4
    split_ifs at hd h4 <;> omega
  · simp only [loadBytes] at h4
    obtain ⟨o, ho, hol⟩ : ∃ o, l.addr = P.sharedBase + 32768 + 18048 * (tt % 3) + o ∧
        o < 18048 :=
      ⟨l.addr - (P.sharedBase + 32768 + 18048 * (tt % 3)), by split_ifs at hd <;> omega,
        by split_ifs at hd h4 <;> omega⟩
    have hmod : (l.addr - (L.sharedBase + 32768)) % 18048 = o := by
      rw [hb, ho, show P.sharedBase + 32768 + 18048 * (tt % 3) + o - (P.sharedBase + 32768) =
        o + 18048 * (tt % 3) by omega, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hol]
    rw [hmod]
    simp only [pieceOf]
    split_ifs at hd h4 ⊢ <;> omega

/-! ### The source side of a tile load -/

/-- **`SafetyFacts.loadBounds` for a tile load**: a load that selects an element outside its
tensor through a large-class map is a load of the values `v` (positions 0 to 15: the tile's 16
token rows may reach past the last token of the batch) or of the gate logits `beta` (position
16). The loads of the six workspace arrays stay inside their tensors: the features (or
columns) `c0 .. c0 + 7` and the rows `0 .. 15` exist, and the slot of a tile of the block is a
slot of the workspace (`slot_lt`). -/
theorem tileLoad_bounds (hpre : Pre P L mem0) (hg : g < L.threads) {tt i : Nat}
    (ht : tt < tilesOf P g) (hi : i < 70)
    (hoob : TensorHasOob (tileLoad P L g tt i).descriptor (tileLoad P L g tt i).origin
      (tileLoad P L g tt i).rows)
    (hlarge : (tileLoad P L g tt i).descriptor.allocationClass = .large) :
    ((tileLoad P L g tt i).descriptor.base = P.valuesBase ∧ P.allocation 0 = .large) ∨
      ((tileLoad P L g tt i).descriptor.base = P.logitsBase ∧ P.allocation 1 = .large) := by
  interval_cases i <;> first
    | exact .inl ⟨rfl, hlarge⟩
    | exact .inr ⟨rfl, hlarge⟩
    | exact absurd hoob (noOob3 (fun _ => rfl) rfl rfl rfl rfl (Nat.le_of_ble_eq_true rfl)
        (Nat.le_of_ble_eq_true rfl) (slot_lt hpre hg ht))
    | exact absurd hoob (noOob2 (fun _ => rfl) rfl rfl rfl (Nat.le_of_ble_eq_true rfl)
        (slot_lt hpre hg ht))

/-- **The first three parts of the progress premise `TensorSources` for a tile load**: the
copy is routed to the issuer's own block, its descriptor is valid, and its box is not empty. -/
theorem tileLoad_ok (hpre : Pre P L mem0) (hg : g < L.threads) (tt : Nat) {i : Nat}
    (hi : i < 70) :
    TensorCopy.RoutingOk L (g / L.block) (tileLoad P L g tt i) ∧
      TensorDescriptor.Valid (tileLoad P L g tt i).descriptor ∧
      0 < TensorTransfer.bytes (tileLoad P L g tt i).descriptor := by
  refine ⟨ownRoute hpre hg _ _, preMap_valid hpre (mapFin i), ?_⟩
  rw [tileLoad, loadSpec_bytes, mapBytes_eq i hi]
  unfold loadBytes
  split_ifs <;> decide

/-! ### Along the trace -/

/-- **The thread is at the entry of the Producer phase before its event `k0`**: the state is
the entry state, the ledger is the entry ledger, and the thread has polled the state mbarrier
of its block successfully (in the startup phase). The phases before this one prove it for
every thread of the load warp. -/
structure Entered (P : Params) (L : Launch) (X : Execution) (g k0 : Nat) : Prop where
  state : ∃ s0, Frame.stateAt (code L) X g k0 = some (some s0) ∧ Entry P g s0
  led : ledOf L (g / L.block) ((X.tr g).take k0) = ledEntry g
  polled : 1 ≤ okPolls (Bar.state.loc L (g / L.block)) ((X.tr g).take k0)

/-- The thread left the Producer phase at or before its event `k`. -/
def Left (P : Params) (L : Launch) (X : Execution) (g k : Nat) : Prop :=
  ∃ j ≤ k, ∃ s1, Frame.stateAt (code L) X g j = some (some s1) ∧ Out P L X g j s1

/-- A thread that entered has polled the state mbarrier at every later position. -/
theorem Entered.polled_at {k0 k : Nat} (h : Entered P L X g k0) (hk : k0 ≤ k) :
    1 ≤ okPolls (Bar.state.loc L (g / L.block)) ((X.tr g).take k) :=
  le_trans h.polled ((List.take_sublist_take_left hk).countP_le)

/-- A thread of block `c` with index 128 in its block is the load leader of `c`. -/
theorem leader_eq (hpre : Pre P L mem0) (ht : tid g = 128) :
    g = loadLeader L (g / L.block) := by
  simp only [loadLeader, Protocol.thr, hpre.block]
  unfold tid at ht
  omega

section
variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
  (hg : g < L.threads) (hw : warp g = 4) {k0 k : Nat} (hen : Entered P L X g k0) (hk0 : k0 ≤ k)
include hpre hX hg hw hen hk0

/-- **A state of the thread from the entry on** is at a position with its facts and ledger, or
the thread has left the phase. -/
theorem state_at {s : D} (hk : k < (X.tr g).length)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    (∃ pos, RefAt P g pos s ∧ ledOf L (g / L.block) ((X.tr g).take k) = led P g pos) ∨
      Left P L X g k := by
  obtain ⟨s0, h0, hE⟩ := hen.state
  exact producer_inv hpre hX hg hw h0 hE hen.led hk0 hk hσ

/-- **An event of the thread from the entry on** is the closed-form event of a position whose
register facts and ledger hold, and the machine has a successor state for it; or the thread has
left the phase (then the event belongs to the epilogue). -/
theorem event_at {s : D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    (∃ pos, RefAt P g pos s ∧ ledOf L (g / L.block) ((X.tr g).take k) = led P g pos ∧
      Ev P L g pos e ∧ ∃ s', Thread.next L g s e = some (some s')) ∨ Left P L X g k := by
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  rcases state_at hpre hX hg hw hen hk0 hk hσ with hI | h
  · obtain ⟨pos, w, p, x, rfl, hr, hl, hev, d', hd', -⟩ :=
      producer_good hpre hX hg hw he hσ hI
    exact .inl ⟨pos, hr, hl, hev, d', hd'⟩
  · exact .inr h

/-- **`SafetyFacts.loadNoUb`, control half**: an event of the phase is no undefined
behaviour. -/
theorem noUb_producer {s : D} {pc : Nat} {f : Fault} (he : X.get (g, k) = some ⟨pc, .ub f⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) : Left P L X g k := by
  rcases event_at hpre hX hg hw hen hk0 he hσ with ⟨pos, -, -, hev, -⟩ | h
  · exact absurd rfl (ev_not_ub hev pc f)
  · exact h

/-- **`BarFacts`**: a barrier event from the entry on, inside the phase, is the thread's sixth
`bar.sync 0`, at instruction 1402. -/
theorem bar_producer {s : D} {pc id : Nat} {cnt : Option Nat} {mode : BarMode}
    (he : X.get (g, k) = some ⟨pc, .bar id cnt mode⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    (pc = 1402 ∧ id = 0 ∧ cnt = none ∧ mode = .sync ∧ bar0Before X (g, k) = 5) ∨
      Left P L X g k := by
  rcases event_at hpre hX hg hw hen hk0 he hσ with ⟨pos, -, hl, hev, -⟩ | h
  · obtain ⟨-, h1, h2, h3, h4, h5⟩ := bar_shape hl hev
    exact .inl ⟨h1, h2, h3, h4, h5⟩
  · exact .inr h

/-- **`LoadFacts.full_arrive`**: an arrival of the phase on the "full" mbarrier of a stage. -/
theorem full_arrive_producer {s : D} {pc tx cnt : Nat} {m : Loc} {rel : Bool} {sc : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .arrive m tx cnt rel sc⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    (∃ st : Fin 3, m = (Bar.loadFull st).loc L (g / L.block) ∧ g = loadLeader L (g / L.block) ∧
      tx = 17984 ∧ cnt = 1 ∧ rel = true ∧ sc = .cta ∧ bar0Before X (g, k) = 6 ∧
      arrivals ((Bar.loadFull st).loc L (g / L.block)) ((X.tr g).take k) + 1 ≤
        okPolls ((Bar.loadEmpty st).loc L (g / L.block)) ((X.tr g).take k)) ∨
      Left P L X g k := by
  rcases event_at hpre hX hg hw hen hk0 he hσ with ⟨pos, hr, hl, hev, -⟩ | h
  · obtain ⟨tt, -, -, rfl, rfl, rfl, rfl, rfl, ht, ha, hp, hb⟩ := arrive_shape hr hl hev
    refine .inl ⟨stage tt, rfl, leader_eq hpre ht, rfl, rfl, rfl, rfl, hb, ?_⟩
    show arrivals (fullLoc L (g / L.block) (stage tt)) _ + 1 ≤
      okPolls (emptyLoc L (g / L.block) (stage tt)) _
    omega
  · exact .inr h

/-- **`LoadFacts.full_issue`** (and `no_tensor_empty`, `StoreFacts.no_tensor`,
`SafetyFacts.loadFill`): a tensor load of the phase completes on the "full" mbarrier of a
stage; it is the load leader's load at position `i` of a tile `tt`, where `i` is the number of
its earlier loads on that mbarrier modulo 70; it moves `loadBytes i` bytes, fills with zero,
and follows `count / 70 + 1` successful polls of the stage's "empty" mbarrier and as many
arrivals on the "full" one; six `bar.sync 0` and a successful poll of the state mbarrier
precede it. -/
theorem full_issue_producer {s : D} {pc al : Nat} {sp : TensorCopy.Spec}
    (he : X.get (g, k) = some ⟨pc, .tensorIssue al sp⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    (∃ tt i, tt < tilesOf P g ∧ i < 70 ∧ al = P.objectBase (mapFin i) ∧
      sp = tileLoad P L g tt i ∧ sp.mbar = (Bar.loadFull (stage tt)).loc L (g / L.block) ∧
      g = loadLeader L (g / L.block) ∧
      ((X.tr g).take k).countP (issuesTo ((Bar.loadFull (stage tt)).loc L (g / L.block))) % 70
        = i ∧
      TensorTransfer.bytes sp.descriptor = loadBytes i ∧
      sp.descriptor.fill = .zero ∧ sp.descriptor.format ≠ .f64 ∧
      ((X.tr g).take k).countP (issuesTo ((Bar.loadFull (stage tt)).loc L (g / L.block))) / 70
        + 1 ≤ okPolls ((Bar.loadEmpty (stage tt)).loc L (g / L.block)) ((X.tr g).take k) ∧
      ((X.tr g).take k).countP (issuesTo ((Bar.loadFull (stage tt)).loc L (g / L.block))) / 70
        + 1 ≤ arrivals ((Bar.loadFull (stage tt)).loc L (g / L.block)) ((X.tr g).take k) ∧
      bar0Before X (g, k) = 6 ∧
      1 ≤ okPolls (Bar.state.loc L (g / L.block)) ((X.tr g).take k)) ∨ Left P L X g k := by
  rcases event_at hpre hX hg hw hen hk0 he hσ with ⟨pos, hr, hl, hev, -⟩ | h
  · obtain ⟨tt, i, htt, hi, -, rfl, rfl, ht, hc, hp, ha, hb⟩ := issue_shape hr hl hev
    have hc' : ((X.tr g).take k).countP
        (issuesTo ((Bar.loadFull (stage tt)).loc L (g / L.block))) = 70 * (tt / 3) + i := hc
    have hbytes : TensorTransfer.bytes (tileLoad P L g tt i).descriptor = loadBytes i := by
      rw [tileLoad, loadSpec_bytes]
      interval_cases i <;> rfl
    refine .inl ⟨tt, i, htt, hi, rfl, rfl, ?_, leader_eq hpre ht, ?_, hbytes,
      (loadSpec_fill ..).1, (loadSpec_fill ..).2, ?_, ?_, hb, hen.polled_at hk0⟩
    · rw [tileLoad, loadSpec_mbar, fullLoc_eq hpre]
    · rw [hc']; omega
    · rw [hc']
      show _ ≤ okPolls (emptyLoc L (g / L.block) (stage tt)) _
      omega
    · rw [hc']
      show _ ≤ arrivals (fullLoc L (g / L.block) (stage tt)) _
      omega
  · exact .inr h

/-- **`LoadFacts.empty_poll`** (and the progress field `poll`): a poll of the phase is the load
leader's, of the "empty" mbarrier of a stage, acquiring, with the parity of its earlier
successful polls of that mbarrier plus one; these are at most one per earlier tile of the
stage. -/
theorem empty_poll_producer {s : D} {pc q : Nat} {m : Loc} {ok acq : Bool} {sc : MbarScope}
    (he : X.get (g, k) = some ⟨pc, .wait m q ok acq sc⟩)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    (∃ pos st, RefAt P g pos s ∧ m = (Bar.loadEmpty st).loc L (g / L.block) ∧
      g = loadLeader L (g / L.block) ∧ acq = true ∧ sc = .cta ∧
      q % 2 = (okPolls m ((X.tr g).take k) + 1) % 2 ∧
      okPolls m ((X.tr g).take k) = uses 3 (tileAt P g pos) st.val ∧
      bar0Before X (g, k) = 6) ∨ Left P L X g k := by
  rcases event_at hpre hX hg hw hen hk0 he hσ with ⟨pos, hr, hl, hev, -⟩ | h
  · obtain ⟨tt, rfl, rfl, rfl, rfl, ht, hp, hu, hb⟩ := poll_shape hr hl hev
    refine .inl ⟨pos, stage tt, hr, rfl, leader_eq hpre ht, rfl, rfl, ?_, hu, hb⟩
    rw [hp]
    simp only [par]
    omega
  · exact .inr h

/-- **`InitFacts.use_ev`** (and `SafetyFacts.mbarFrame`): an event of the phase that names an
mbarrier names one of the six mbarriers of the load pipeline of the thread's own block, after
the `bar.sync 0` that publishes it (the first; the thread has made six). -/
theorem use_ev_producer {s : D} {e : Event} {m : Loc} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (hm : Frame.MbarOf e m) :
    (∃ b : Bar, m = b.loc L (g / L.block) ∧ b.gen + 1 ≤ bar0Before X (g, k)) ∨
      Left P L X g k := by
  rcases event_at hpre hX hg hw hen hk0 he hσ with ⟨pos, hr, hl, hev, -⟩ | h
  · refine .inl ?_
    obtain ⟨pc, kd⟩ := e
    cases pos with
    | entry => cases hev; exact hm.elim
    | poll c u =>
      obtain ⟨ok, h⟩ := id hev
      cases h
      obtain ⟨tt, -, -, -, -, -, -, -, hb⟩ := poll_shape hr hl hev
      exact ⟨.loadEmpty (stage (tile c u)), hm, by
        rw [show bar0Before X (g, k) = 6 from hb]; exact (by decide : 0 + 1 ≤ 6)⟩
    | arrive c u =>
      cases id hev
      obtain ⟨tt, -, -, -, -, -, -, -, -, -, -, hb⟩ := arrive_shape hr hl hev
      exact ⟨.loadFull (stage (tile c u)), hm, by
        rw [show bar0Before X (g, k) = 6 from hb]; exact (by decide : 0 + 1 ≤ 6)⟩
    | load c u i =>
      cases id hev
      obtain ⟨tt, j, -, -, -, -, -, -, -, -, -, hb⟩ := issue_shape hr hl hev
      refine ⟨.loadFull (stage (tile c u)), ?_, by
        rw [show bar0Before X (g, k) = 6 from hb]; exact (by decide : 0 + 1 ≤ 6)⟩
      rw [← show (tileLoad P L g (tile c u) i.val).mbar = m from hm, tileLoad, loadSpec_mbar,
        fullLoc_eq hpre]
    | tail j =>
      obtain ⟨ok, h⟩ := id hev
      cases h
      obtain ⟨tt, -, -, -, -, -, -, -, hb⟩ := poll_shape hr hl hev
      exact ⟨.loadEmpty (stage (tilesOf P g + j.val)), hm,
        by rw [show bar0Before X (g, k) = 6 from hb]; exact (by decide : 0 + 1 ≤ 6)⟩
  · exact .inr h

/-- **Progress `tile_le`, `bar0`, `arrLoadFull`** at a state of the phase: the tile index is at
most the tile count; the thread has made five `bar.sync 0` at the entry and six after it; and
the load leader has arrived on, and issued 70 loads to, the "full" mbarrier of each stage once
per tile below the tile index. -/
theorem progress_producer {s : D} (hk : k < (X.tr g).length)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) :
    (∃ pos, RefAt P g pos s ∧ tileAt P g pos ≤ tilesOf P g ∧
      bar0Before X (g, k) = (if pos = .entry then 5 else 6) ∧
      ∀ st : Fin 3,
        uses 3 (tileAt P g pos) st.val ≤
          arrivals ((Bar.loadFull st).loc L (g / L.block)) ((X.tr g).take k) ∧
        70 * uses 3 (tileAt P g pos) st.val ≤
          ((X.tr g).take k).countP (issuesTo ((Bar.loadFull st).loc L (g / L.block)))) ∨
      Left P L X g k := by
  rcases state_at hpre hX hg hw hen hk0 hk hσ with ⟨pos, hr, hl⟩ | h
  · refine .inl ⟨pos, hr, tileAt_le hr, ?_, fun st => counts_at hr hl st⟩
    have hb : bar0Before X (g, k) = (led P g pos).bars := congrArg Led.bars hl
    rw [hb]
    cases pos <;> simp [led, ledEntry, ledAt]
  · exact .inr h

/-- **`LifeFacts.full_issues`, up to the exit of the phase**: the loads the thread has issued on
the "full" mbarrier of a stage are at most 70 per tile of the stage. -/
theorem issues_le_producer {s : D} (hk : k < (X.tr g).length)
    (hσ : Frame.stateAt (code L) X g k = some (some s)) (st : Fin 3) :
    ((X.tr g).take k).countP (issuesTo ((Bar.loadFull st).loc L (g / L.block))) ≤
      70 * uses 3 (tilesOf P g) st.val ∨ Left P L X g k := by
  rcases state_at hpre hX hg hw hen hk0 hk hσ with ⟨pos, hr, hl⟩ | h
  · exact .inl (issues_le_at hr hl st)
  · exact .inr h

/-- **Progress `left_dec`**: a step inside the phase lowers the counted events left by one when
the event counts (every event but a failed poll). The successor is at a position `pos'` of the
phase, or at the exit, where no counted event of the phase is left. -/
theorem left_dec_producer {s s' : D} {e : Event} (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (code L) X g k = some (some s))
    (hn : Thread.next L g s e = some (some s')) :
    (∃ pos, RefAt P g pos s ∧
      ((∃ pos', RefAt P g pos' s' ∧
          leftAt P g pos' + (if e.counts then 1 else 0) = leftAt P g pos) ∨
        (Exit P g s' ∧ (if e.counts then 1 else 0) = leftAt P g pos))) ∨ Left P L X g k := by
  have hk : k < (X.tr g).length := (List.getElem?_eq_some_iff.mp he).1
  rcases state_at hpre hX hg hw hen hk0 hk hσ with hI | h
  · obtain ⟨pos, w, p, x, rfl, hr, hl, hev, d', hd', hsucc⟩ :=
      producer_good hpre hX hg hw he hσ hI
    rw [hd'] at hn
    obtain rfl := Option.some.inj (Option.some.inj hn)
    have h1 := left_led hr
    have h2 := ledEv_counted L (g / L.block) hev
    refine .inl ⟨pos, hr, ?_⟩
    rcases hsucc with ⟨pos', hr', hl'⟩ | ⟨hE, hl'⟩
    · have h3 := left_led hr'
      rw [hl'] at h3
      simp only [Led.counted, Led.add_def] at h1 h2 h3
      exact .inl ⟨pos', hr', by omega⟩
    · have h3 := exit_counted P g
      rw [hl'] at h3
      simp only [Led.counted, Led.add_def] at h1 h2 h3
      exact .inr ⟨hE, by omega⟩
  · exact .inr h

end

/-! ### After the phase -/

/-- **After the phase**: the exit state and its ledger held at an earlier position. -/
theorem left_exit {k : Nat} (h : Left P L X g k) :
    ∃ j ≤ k, ∃ s1, Frame.stateAt (code L) X g j = some (some s1) ∧ Exit P g s1 ∧
      ledOf L (g / L.block) ((X.tr g).take j) = ledExit P g :=
  let ⟨j, hj, s1, h1, h2, h3⟩ := h
  ⟨j, hj, s1, h1, h2, h3⟩

/-- The counts of the load leader at the exit, per stage `s`: one successful poll of the
"empty" mbarrier per tile of the stage and one more (the tail), one arrival on the "full"
mbarrier and 70 loads completing on it per tile of the stage. -/
theorem exit_counts {es : List Event} (ht : tid g = 128)
    (hl : ledOf L (g / L.block) es = ledExit P g) (s : Fin 3) :
    okPolls (emptyLoc L (g / L.block) s) es = uses 3 (tilesOf P g) s.val + 1 ∧
      arrivals (fullLoc L (g / L.block) s) es = uses 3 (tilesOf P g) s.val ∧
      es.countP (issuesTo (fullLoc L (g / L.block) s)) = 70 * uses 3 (tilesOf P g) s.val := by
  have hs := s.isLt
  simp only [ledExit, ht, ↓reduceIte] at hl
  rw [led_e hl, led_a hl, led_i hl]
  simp only [uses_eq, issuedOn]
  rw [show 70 * tilesOf P g / 70 = tilesOf P g by omega]
  refine ⟨by omega, trivial, ?_⟩
  split_ifs <;> omega

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Producer
