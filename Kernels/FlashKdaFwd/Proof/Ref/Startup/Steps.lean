-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Startup.Arith

@[expose] public section

/-! # The reference invariant of the startup phase is kept: the sites outside the scan

One lemma per site: from the invariant at the site (`RefAt`), the state that the generated
transition function gives is at a position of the phase with its invariant, and the ledger of
that position is the ledger of the site plus what the site's event counts (`Succ`), or it is
the exit of the phase (`st_wait`).

Every proof has the same four parts (`ref_at pos [lemmas]`): the site of the successor, the
facts that hold from the entry on (`Base.of_w`: the transition leaves three registers alone),
the registers of the new position, and the ledger. Each part is one `simp only` that unfolds
the transition function, reads the rewritten file at the literal registers (`file_simp`),
rewrites with the facts of the old position and the closed forms of `Common` and `Arith`, and
normalizes the 32-bit arithmetic on words (`w32_norm`, bounds by `omega` from the context).

A transition with branches is proved after a case split on the closed form of each branch
condition (the thread's warp, whether its lane was elected): in each case the conditions of the
transition function are rewritten to `true` or `false` first, so that the `if`s are gone before
the file is read. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Startup
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

/-! ### The elections of a thread, by position

The ledger `Led` counts shuffles but not elections (an election changes no field of it). The
progress contract counts both (`RefProgress.coll`), so every step lemma also proves how the
number of elections changes: `elects g pos` is the number of elections a thread of the role of
`g` has made before position `pos`, and a step from `pos` adds `elOf pos` (1 at an election).
The first election (instruction 32) is made by the load warp only, the third and the fourth
(61, 93) by warp 0 only. -/

/-- 1 in warp 0 (threads 0 to 31 of a block), 0 elsewhere. -/
def w0 (g : Nat) : Nat := if tid g < 32 then 1 else 0

/-- 1 in the load warp (threads 128 to 159 of a block), 0 elsewhere. -/
def w4 (g : Nat) : Nat := if 128 ≤ tid g ∧ tid g < 160 then 1 else 0

theorem w0_cases (g : Nat) : (tid g < 32 ∧ w0 g = 1) ∨ (¬ tid g < 32 ∧ w0 g = 0) := by
  unfold w0
  split_ifs with h
  · exact .inl ⟨h, rfl⟩
  · exact .inr ⟨h, rfl⟩

theorem w4_cases (g : Nat) :
    ((128 ≤ tid g ∧ tid g < 160) ∧ w4 g = 1) ∨ (¬ (128 ≤ tid g ∧ tid g < 160) ∧ w4 g = 0) := by
  unfold w4
  split_ifs with h
  · exact .inl ⟨h, rfl⟩
  · exact .inr ⟨h, rfl⟩

/-- **The elections a thread has made before a position.** -/
def elects (g : Nat) : Pos → Nat
  | .elect j =>
    match j.val with
    | 0 => 0
    | 1 => w4 g
    | 2 => w4 g + 1
    | 3 => w4 g + 1 + w0 g
    | _ => w4 g + 1 + 2 * w0 g
  | .shfl j =>
    match j.val with
    | 0 => w4 g
    | 1 => w4 g + 1
    | _ => w4 g + 1 + w0 g
  | .init j =>
    match j.val with
    | 0 | 1 | 2 | 3 | 4 | 5 => w4 g + 2
    | 6 | 7 | 8 | 9 => w4 g + 2 + w0 g
    | _ => w4 g + 2 + 2 * w0 g
  | .fence j =>
    match j.val with
    | 0 => w4 g + 1 + w0 g
    | 1 => w4 g + 1 + 2 * w0 g
    | _ => w4 g + 2 + 2 * w0 g
  | .bar j =>
    match j.val with
    | 0 => w4 g + 1 + w0 g
    | 1 => w4 g + 1 + 2 * w0 g
    | _ => w4 g + 2 + 2 * w0 g
  | .load _ => w4 g + 1 + 2 * w0 g
  | .arrive => w4 g + 2 + 2 * w0 g
  | .copy _ => w4 g + 2 + 2 * w0 g
  | .wait => w4 g + 2 + 2 * w0 g

/-- The elections a thread has made when it leaves the phase. -/
def electsExit (g : Nat) : Nat := w4 g + 2 + 2 * w0 g

/-- 1 at an election position: the elections of the event fired there. -/
def elOf : Pos → Nat
  | .elect _ => 1
  | _ => 0

/-! ### The counted events left, by position

For termination, every step of a thread must lower a measure of its state (every event but a
failed poll is counted). In the startup phase every control-flow edge but two goes to a later
instruction: the back edge of the scan's loop of eight and the poll that fails. So the measure
of a position is the distance of its instruction from instruction 400, plus 100 for each
sequence the loop of eight still has to scan: all of `seq - seq % 8` before the loop, that
minus the loop's index (register `%r1791`, 2097) inside it, nothing after it. The back edge
goes back 65 instructions and lowers the second term by 800. -/

/-- The instruction index of a position (`pos.site.pc`, as a table of numbers). -/
def pcOf : Pos → Nat
  | .elect j => [32, 52, 61, 93, 312].getD j.val 0
  | .shfl j => [48, 55, 87].getD j.val 0
  | .init j => [69, 72, 74, 76, 78, 80, 101, 104, 106, 108, 324].getD j.val 0
  | .fence j => [81, 109, 325].getD j.val 0
  | .bar j => [85, 110, 379].getD j.val 0
  | .load j => [115, 116, 126, 131, 141, 150, 159, 168, 177, 186, 196, 215, 216, 226, 235, 245,
      260, 264, 265, 276, 291].getD j.val 0
  | .arrive => 327
  | .copy j => 333 + 3 * j.val
  | .wait => 384

/-- The sequences the scan's loop of eight still has to scan, seen from a position: all
`seq - seq % 8` before the loop, the rest inside it (`w 2097` is the loop's index), none
after it. -/
def loopOf (P : Params) (g : Nat) : Pos → (Nat → BitVec 64) → Nat
  | .load j, w =>
    match j.val with
    | 0 | 1 | 2 => seqOf P g - seqOf P g % 8
    | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 => seqOf P g - seqOf P g % 8 - (w 2097).toNat
    | _ => 0
  | .elect j, _ =>
    match j.val with
    | 4 => 0
    | _ => seqOf P g - seqOf P g % 8
  | .shfl _, _ => seqOf P g - seqOf P g % 8
  | .init j, _ =>
    match j.val with
    | 10 => 0
    | _ => seqOf P g - seqOf P g % 8
  | .fence j, _ =>
    match j.val with
    | 2 => 0
    | _ => seqOf P g - seqOf P g % 8
  | .bar j, _ =>
    match j.val with
    | 2 => 0
    | _ => seqOf P g - seqOf P g % 8
  | .arrive, _ => 0
  | .copy _, _ => 0
  | .wait, _ => 0

/-- **The counted events a thread at a position still makes in the phase, at most** (plus 13
at the exit, the measure of the exit state). -/
def leftP (P : Params) (g : Nat) (pos : Pos) (w : Nat → BitVec 64) : Nat :=
  (400 - pcOf pos) + 100 * loopOf P g pos w

/-- **A successor inside the phase**: the state `d'` is at a position with its invariant, and
that position's ledger is the ledger of `pos` plus `δ`. -/
def Succ (P : Params) (g : Nat) (pos : Pos) (w : Nat → BitVec 64) (δ : Led) (d' : D) :
    Prop :=
  ∃ pos', RefAt P g pos' d' ∧ led g pos' = led g pos + δ ∧
    elects g pos' = elects g pos + elOf pos ∧ leftP P g pos' d'.w + 1 ≤ leftP P g pos w

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
  {w : Nat → BitVec 64} {p : Nat → Bool} {x : Nat → Value}

theorem Base.of_w {d d' : D} (hb : Base P g d) (h1 : d'.w 307 = d.w 307)
    (h2 : d'.w 308 = d.w 308) (h3 : d'.w 2247 = d.w 2247) : Base P g d' :=
  ⟨h1.trans hb.tid, h2.trans hb.warp, h3.trans hb.offs⟩

/-- `ref_base [lemmas]`: the facts from the entry on, from those of the predecessor `hb`. -/
syntax "ref_base" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| ref_base [$ls,*]) => `(tactic| (
      refine Base.of_w hb ?_ ?_ ?_ <;>
        first | rfl | (file_simp [Bool.false_eq_true, ↓reduceIte, $ls,*]; done)))

/-- `ref_pos [lemmas]`: register facts of the successor (a conjunction of closed forms):
`ref_facts` of `Ref/Lib.lean` with the predicates of this phase. -/
syntax "ref_pos" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| ref_pos [$ls,*]) => `(tactic|
      ref_facts [AtPos, copyDst, copyCoord, Flags, flagsOf, Scan, Cta, Own, Loop8, Mid, $ls,*])

/-- `ref_led`: the ledger equation, by the role facts in context. -/
macro "ref_led" : tactic => `(tactic| (first
  | (simp (disch := omega) [led, finVal, Led.add_def]; done)
  | (simp (disch := omega) [led, finVal, Led.add_def, *]; done)
  | (simp (disch := omega) [led, finVal, Led.add_def] <;> omega)))

set_option hygiene false in
/-- `ref_el`: the election count of the successor, by the role facts in context. -/
macro "ref_el" : tactic => `(tactic| (first
  | rfl
  | (simp only [elects, elOf, electsExit, finVal]; done)
  | (simp only [elects, elOf, electsExit, finVal]
     have e0' := w0_cases g
     have e4' := w4_cases g
     have et' := tid_eq g
     have el' := lane_lt g
     omega)))

/-- `ref_left`: the measure of the successor is lower (for a successor outside the loop of
eight, whose measure does not read the register file). -/
macro "ref_left" : tactic => `(tactic| (
  simp only [leftP, loopOf, pcOf, PTX.Kernels.FlashKdaFwd.Proof.Ref.finVal,
    PTX.Kernels.FlashKdaFwd.Proof.Ref.getLit]
  omega))

/-- `ref_at pos [lemmas]`: the successor is at `pos`. -/
syntax "ref_at " term:max " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| ref_at $pos [$ls,*]) => `(tactic| (
      refine ⟨$pos, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
      · ref_site [$ls,*]
      · ref_base [$ls,*]
      · ref_pos [$ls,*]
      · ref_led
      · ref_el
      · ref_left))

/-! ### The entry -/

/-- **The first state of a thread** is at the first election in the load warp and at the
first shuffle elsewhere, with the role flags of its class. -/
theorem st_init (hpre : Pre P L mem0) :
    ∃ pos, RefAt P g pos (init L g) ∧ led g pos = ⟨0, 0, 0, 0, 0, 0⟩ ∧ elects g pos = 0 := by
  have ht := tid_lt g
  have e1 := tidWord (g := g) hpre
  have e2 := offsetsWord hpre
  by_cases h1 : tid g < 128
  · refine ⟨.shfl 0, ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩, rfl, (by
          simp only [elects, finVal]
          have := w4_cases g
          omega)⟩ <;>
      file_simp [init, entry, e1, e2, warpWord, tid_lt128, tid_lt160, h1, decide_true,
        Arith32.sel, cmpLit, ↓reduceIte, AtPos, finVal, Flags, flagsOf, roleFlags, Pos.site,
        and_self]
  · by_cases h2 : tid g < 160
    · have hw : warp g = 4 := (warp_eq4_iff g).mpr ⟨by omega, h2⟩
      refine ⟨.elect 0, ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩, rfl, rfl⟩ <;>
        file_simp [init, entry, e1, e2, warpWord, tid_lt128, tid_lt160, h1, h2, decide_true,
          decide_false, Arith32.sel, cmpLit, ↓reduceIte, Bool.false_eq_true, AtPos, finVal,
          Pos.site, hw, and_self, true_and]
      rfl
    · refine ⟨.shfl 0, ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩, rfl, (by
          simp only [elects, finVal]
          have := w4_cases g
          omega)⟩ <;>
        file_simp [init, entry, e1, e2, warpWord, tid_lt128, tid_lt160, h1, h2, decide_true,
          decide_false, Arith32.sel, cmpLit, ↓reduceIte, Bool.false_eq_true, AtPos, finVal,
          Flags, flagsOf, roleFlags, Pos.site, and_self]

/-! ### Elections and shuffles before the scan -/

theorem st_elect_0 (hpre : Pre P L mem0) (h : RefAt P g (.elect 0) ⟨.elect 0, w, p, x⟩) :
    Succ P g (.elect 0) w ⟨0, 0, 0, 0, 0, 0⟩
      (after_elect_0 L g (scope_elect_0 ⟨.elect 0, w, p, x⟩ 0 (decide (lane g = 0)))) := by
  obtain ⟨-, hb, h⟩ := h
  simp only [AtPos, finVal] at h
  have h1 : ¬ tid g < 128 := by have := (warp_eq4_iff g).mp h.1; omega
  have h2 : tid g < 160 := ((warp_eq4_iff g).mp h.1).2
  by_cases hl : lane g = 0 <;>
    ref_at (.shfl 0) [after_elect_0, scope_elect_0, roleFlags, h, hl, h1, h2, Arith32.sel,
      cmpLit, decide_true, decide_false, ne_eq, not_true_eq_false, not_false_eq_true]

theorem st_shfl_0 (hpre : Pre P L mem0) (ok : Bool)
    (h : RefAt P g (.shfl 0) ⟨.shfl 0, w, p, x⟩) :
    Succ P g (.shfl 0) w ⟨0, 0, 0, 0, 0, 1⟩ (after_shfl_0 L g ⟨.shfl 0, w, p, x⟩ 0 ok) := by
  obtain ⟨-, hb, h⟩ := h
  simp only [AtPos, finVal, Flags, flagsOf] at h
  ref_at (.elect 1) [after_shfl_0, h]

theorem st_elect_1 (hpre : Pre P L mem0) (h : RefAt P g (.elect 1) ⟨.elect 1, w, p, x⟩) :
    Succ P g (.elect 1) w ⟨0, 0, 0, 0, 0, 0⟩
      (after_elect_1 L g (scope_elect_1 ⟨.elect 1, w, p, x⟩ 0 (decide (lane g = 0)))) := by
  obtain ⟨-, hb, h⟩ := h
  simp only [AtPos, finVal, Flags, flagsOf] at h
  ref_at (.shfl 1) [after_elect_1, scope_elect_1, h]

/-- A thread outside warp 0 is not the init leader. -/
theorem tid_ne_zero_of_warp {g : Nat} (h : warp g ≠ 0) : tid g ≠ 0 := by
  unfold warp tid at *; omega

/-- Lane 0 of warp 0 is thread 0. -/
theorem tid_zero_of {g : Nat} (h1 : warp g = 0) (h2 : lane g = 0) : tid g = 0 := by
  unfold warp tid lane at *; omega

theorem tid_ne_zero_of_lane {g : Nat} (h : lane g ≠ 0) : tid g ≠ 0 := by
  unfold tid lane at *; omega

/-- The comparison `setp.ne.b32 %p, %r, 0` of the received warp index. -/
theorem warp_ne0 {g : Nat} : scmpi .ne .b (W (warp g)) 0 = decide (warp g ≠ 0) := by
  have := warp_lt g
  rw [scmpi_ne_b_W (by omega) (by decide) (by decide)]
  rfl

theorem st_shfl_1 (hpre : Pre P L mem0) (ok : Bool)
    (h : RefAt P g (.shfl 1) ⟨.shfl 1, w, p, x⟩) :
    Succ P g (.shfl 1) w ⟨0, 0, 0, 0, 0, 1⟩
      (after_shfl_1 L g ⟨.shfl 1, w, p, x⟩ (W (warp g)) ok) := by
  obtain ⟨-, hb, h⟩ := h
  simp only [AtPos, finVal, Flags, flagsOf] at h
  by_cases h0 : warp g = 0
  · ref_at (.elect 2) [after_shfl_1, warp_ne0, h, h0, cmpLit, decide_false, ne_eq,
      not_true_eq_false]
  · have ht := tid_ne_zero_of_warp h0
    ref_at (.fence 0) [after_shfl_1, warp_ne0, h, h0, ht, decide_true, ne_eq,
      not_false_eq_true]

theorem st_elect_2 (hpre : Pre P L mem0) (h : RefAt P g (.elect 2) ⟨.elect 2, w, p, x⟩) :
    Succ P g (.elect 2) w ⟨0, 0, 0, 0, 0, 0⟩
      (after_elect_2 L g (scope_elect_2 ⟨.elect 2, w, p, x⟩ 0 (decide (lane g = 0)))) := by
  obtain ⟨-, hb, h⟩ := h
  have hs := shared_lt hpre
  have e1 := sharedWord hpre
  simp only [AtPos, finVal, Flags, flagsOf] at h
  by_cases hl : lane g = 0
  · have ht := tid_zero_of h.2.1 hl
    ref_at (.init 0) [after_elect_2, scope_elect_2, h, hl, ht, e1, Arith32.sel, cmpLit,
      decide_true]
  · have ht := tid_ne_zero_of_lane hl
    ref_at (.fence 0) [after_elect_2, scope_elect_2, h, hl, ht, Arith32.sel, cmpLit,
      decide_false]

theorem st_shfl_2 (hpre : Pre P L mem0) (ok : Bool)
    (h : RefAt P g (.shfl 2) ⟨.shfl 2, w, p, x⟩) :
    Succ P g (.shfl 2) w ⟨0, 0, 0, 0, 0, 1⟩
      (after_shfl_2 L g ⟨.shfl 2, w, p, x⟩ (W (warp g)) ok) := by
  obtain ⟨-, hb, h⟩ := h
  simp only [AtPos, finVal, Flags, flagsOf] at h
  by_cases h0 : warp g = 0
  · ref_at (.elect 3) [after_shfl_2, warp_ne0, h, h0, cmpLit, decide_false, ne_eq,
      not_true_eq_false]
  · have ht := tid_ne_zero_of_warp h0
    ref_at (.fence 1) [after_shfl_2, warp_ne0, h, h0, ht, decide_true, ne_eq,
      not_false_eq_true]

theorem st_elect_3 (hpre : Pre P L mem0) (h : RefAt P g (.elect 3) ⟨.elect 3, w, p, x⟩) :
    Succ P g (.elect 3) w ⟨0, 0, 0, 0, 0, 0⟩
      (after_elect_3 L g (scope_elect_3 ⟨.elect 3, w, p, x⟩ 0 (decide (lane g = 0)))) := by
  obtain ⟨-, hb, h⟩ := h
  have hs := shared_lt hpre
  have e1 := sharedWord hpre
  simp only [AtPos, finVal, Flags, flagsOf] at h
  by_cases hl : lane g = 0
  · have ht := tid_zero_of h.2.2.1 hl
    ref_at (.init 6) [after_elect_3, scope_elect_3, h, hl, ht, e1, Arith32.sel, cmpLit,
      decide_true]
  · have ht := tid_ne_zero_of_lane hl
    ref_at (.fence 1) [after_elect_3, scope_elect_3, h, hl, ht, Arith32.sel, cmpLit,
      decide_false]

/-! ### The ten pipeline barriers, the fences and the first two `bar.sync 0` -/

/-- `plain A B δ after`: the transition `after` leads from position `A` to position `B`. -/
syntax "plain " term:max term:max " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| plain $a $b [$ls,*]) => `(tactic| (
      obtain ⟨-, hb, h⟩ := h
      have hs := shared_lt hpre
      simp only [AtPos, finVal, copyDst, copyCoord, getLit, Flags, flagsOf, Scan, Cta] at h
      ref_at $b [$ls,*, h]))

theorem st_init_0 (hpre : Pre P L mem0) (h : RefAt P g (.init 0) ⟨.mbarInit 0, w, p, x⟩) :
    Succ P g (.init 0) w ⟨0, 1, 0, 0, 0, 0⟩ (after_mbarInit_0 L g ⟨.mbarInit 0, w, p, x⟩) := by
  plain (.init 0) (.init 1) [after_mbarInit_0]

theorem st_init_1 (hpre : Pre P L mem0) (h : RefAt P g (.init 1) ⟨.mbarInit 1, w, p, x⟩) :
    Succ P g (.init 1) w ⟨0, 1, 0, 0, 0, 0⟩ (after_mbarInit_1 L g ⟨.mbarInit 1, w, p, x⟩) := by
  plain (.init 1) (.init 2) [after_mbarInit_1]

theorem st_init_2 (hpre : Pre P L mem0) (h : RefAt P g (.init 2) ⟨.mbarInit 2, w, p, x⟩) :
    Succ P g (.init 2) w ⟨0, 1, 0, 0, 0, 0⟩ (after_mbarInit_2 L g ⟨.mbarInit 2, w, p, x⟩) := by
  plain (.init 2) (.init 3) [after_mbarInit_2]

theorem st_init_3 (hpre : Pre P L mem0) (h : RefAt P g (.init 3) ⟨.mbarInit 3, w, p, x⟩) :
    Succ P g (.init 3) w ⟨0, 1, 0, 0, 0, 0⟩ (after_mbarInit_3 L g ⟨.mbarInit 3, w, p, x⟩) := by
  plain (.init 3) (.init 4) [after_mbarInit_3]

theorem st_init_4 (hpre : Pre P L mem0) (h : RefAt P g (.init 4) ⟨.mbarInit 4, w, p, x⟩) :
    Succ P g (.init 4) w ⟨0, 1, 0, 0, 0, 0⟩ (after_mbarInit_4 L g ⟨.mbarInit 4, w, p, x⟩) := by
  plain (.init 4) (.init 5) [after_mbarInit_4]

theorem st_init_5 (hpre : Pre P L mem0) (h : RefAt P g (.init 5) ⟨.mbarInit 5, w, p, x⟩) :
    Succ P g (.init 5) w ⟨0, 1, 0, 0, 0, 0⟩ (after_mbarInit_5 L g ⟨.mbarInit 5, w, p, x⟩) := by
  plain (.init 5) (.fence 0) [after_mbarInit_5]

theorem st_fence_0 (hpre : Pre P L mem0) (h : RefAt P g (.fence 0) ⟨.fenceMbarInit 0, w, p, x⟩) :
    Succ P g (.fence 0) w ⟨0, 0, 0, 0, 0, 0⟩
      (after_fenceMbarInit_0 L g ⟨.fenceMbarInit 0, w, p, x⟩) := by
  plain (.fence 0) (.bar 0) [after_fenceMbarInit_0]

theorem st_bar_0 (hpre : Pre P L mem0) (hg : g < L.threads)
    (h : RefAt P g (.bar 0) ⟨.bar 0, w, p, x⟩) :
    Succ P g (.bar 0) w ⟨1, 0, 0, 0, 0, 0⟩ (after_bar_0 L g ⟨.bar 0, w, p, x⟩) := by
  have e1 := clusterRank hpre hg
  plain (.bar 0) (.shfl 2) [after_bar_0, e1]

theorem st_init_6 (hpre : Pre P L mem0) (h : RefAt P g (.init 6) ⟨.mbarInit 6, w, p, x⟩) :
    Succ P g (.init 6) w ⟨0, 1, 0, 0, 0, 0⟩ (after_mbarInit_6 L g ⟨.mbarInit 6, w, p, x⟩) := by
  plain (.init 6) (.init 7) [after_mbarInit_6]

theorem st_init_7 (hpre : Pre P L mem0) (h : RefAt P g (.init 7) ⟨.mbarInit 7, w, p, x⟩) :
    Succ P g (.init 7) w ⟨0, 1, 0, 0, 0, 0⟩ (after_mbarInit_7 L g ⟨.mbarInit 7, w, p, x⟩) := by
  plain (.init 7) (.init 8) [after_mbarInit_7]

theorem st_init_8 (hpre : Pre P L mem0) (h : RefAt P g (.init 8) ⟨.mbarInit 8, w, p, x⟩) :
    Succ P g (.init 8) w ⟨0, 1, 0, 0, 0, 0⟩ (after_mbarInit_8 L g ⟨.mbarInit 8, w, p, x⟩) := by
  plain (.init 8) (.init 9) [after_mbarInit_8]

theorem st_init_9 (hpre : Pre P L mem0) (h : RefAt P g (.init 9) ⟨.mbarInit 9, w, p, x⟩) :
    Succ P g (.init 9) w ⟨0, 1, 0, 0, 0, 0⟩ (after_mbarInit_9 L g ⟨.mbarInit 9, w, p, x⟩) := by
  plain (.init 9) (.fence 1) [after_mbarInit_9]

theorem st_fence_1 (hpre : Pre P L mem0) (h : RefAt P g (.fence 1) ⟨.fenceMbarInit 1, w, p, x⟩) :
    Succ P g (.fence 1) w ⟨0, 0, 0, 0, 0, 0⟩
      (after_fenceMbarInit_1 L g ⟨.fenceMbarInit 1, w, p, x⟩) := by
  plain (.fence 1) (.bar 1) [after_fenceMbarInit_1]

theorem st_bar_1 (hpre : Pre P L mem0) (hg : g < L.threads)
    (h : RefAt P g (.bar 1) ⟨.bar 1, w, p, x⟩) :
    Succ P g (.bar 1) w ⟨1, 0, 0, 0, 0, 0⟩ (after_bar_1 L g ⟨.bar 1, w, p, x⟩) := by
  have e1 := ctaidX hpre hg
  have e2 := ctaidY hpre hg
  have e3 := ptr_word hpre (Nat.le_of_lt (seq_lt hpre g))
  have e4 := h.base.offs
  dsimp only at e4
  plain (.bar 1) (.load 0) [after_bar_1, e1, e2, e3, e4]

/-! ### The state barrier: the load leader's initialization, arrival and sixteen loads -/

/-- The load leader is lane 0 of warp 4. -/
theorem tid_128_iff {g : Nat} : tid g = 128 ↔ warp g = 4 ∧ lane g = 0 := by
  unfold warp tid lane; omega

theorem st_elect_4 (hpre : Pre P L mem0) (h : RefAt P g (.elect 4) ⟨.elect 4, w, p, x⟩) :
    Succ P g (.elect 4) w ⟨0, 0, 0, 0, 0, 0⟩
      (after_elect_4 L g (scope_elect_4 ⟨.elect 4, w, p, x⟩ 0
        (decide (lane g = 0)))) := by
  have e0 := h.base.tid
  dsimp only at e0
  obtain ⟨-, hb, h⟩ := h
  have hs := shared_lt hpre
  have e1 := sharedWord hpre
  have e2 := headsWord hpre
  simp only [AtPos, finVal, Flags, flagsOf, Scan, Cta] at h
  by_cases hl : lane g = 0
  · by_cases hw : warp g = 4
    · have ht : tid g = 128 := tid_128_iff.mpr ⟨hw, hl⟩
      ref_at (.init 10) [after_elect_4, scope_elect_4, tail_320, e0, tid_and224, h, hw, hl, ht,
        e1, e2, Arith32.sel, cmpLit, decide_true, decide_false, ne_eq, not_true_eq_false,
        Bool.or_self, Bool.or_false, Bool.false_or]
    · have ht : tid g ≠ 128 := fun h' => hw (tid_128_iff.mp h').1
      ref_at (.bar 2) [after_elect_4, scope_elect_4, tail_320, e0, tid_and224, h, hw, hl, ht,
        Arith32.sel, cmpLit, decide_true, decide_false, ne_eq, not_false_eq_true, Bool.true_or,
        Bool.or_true]
  · have ht : tid g ≠ 128 := fun h' => hl (tid_128_iff.mp h').2
    ref_at (.bar 2) [after_elect_4, scope_elect_4, tail_320, e0, tid_and224, h, hl, ht,
      Arith32.sel, cmpLit, decide_true, decide_false, ne_eq, not_false_eq_true, Bool.true_or,
      Bool.or_true]

theorem st_init_10 (hpre : Pre P L mem0) (h : RefAt P g (.init 10) ⟨.mbarInit 10, w, p, x⟩) :
    Succ P g (.init 10) w ⟨0, 1, 0, 0, 0, 0⟩ (after_mbarInit_10 L g ⟨.mbarInit 10, w, p, x⟩) := by
  plain (.init 10) (.fence 2) [after_mbarInit_10]

theorem st_fence_2 (hpre : Pre P L mem0) (h : RefAt P g (.fence 2) ⟨.fenceMbarInit 2, w, p, x⟩) :
    Succ P g (.fence 2) w ⟨0, 0, 0, 0, 0, 0⟩
      (after_fenceMbarInit_2 L g ⟨.fenceMbarInit 2, w, p, x⟩) := by
  plain (.fence 2) (.arrive) [after_fenceMbarInit_2]

theorem st_arrive (hpre : Pre P L mem0) (hg : g < L.threads)
    (h : RefAt P g .arrive ⟨.mbarArrive 0, w, p, x⟩) :
    Succ P g .arrive w ⟨0, 0, 1, 0, 0, 0⟩ (after_mbarArrive_0 L g ⟨.mbarArrive 0, w, p, x⟩) := by
  have e1 := plane_word hpre hg
  plain (.arrive) (.copy 0) [after_mbarArrive_0, e1, Nat.reduceMul, Nat.reduceAdd]

theorem st_copy_0 (hpre : Pre P L mem0) (h : RefAt P g (.copy 0) ⟨.tensorCopy 0, w, p, x⟩) :
    Succ P g (.copy 0) w ⟨0, 0, 0, 1, 0, 0⟩ (after_tensorCopy_0 L g ⟨.tensorCopy 0, w, p, x⟩) := by
  plain (.copy 0) (.copy 1) [after_tensorCopy_0, Nat.reduceMul, Nat.reduceAdd]

theorem st_copy_1 (hpre : Pre P L mem0) (h : RefAt P g (.copy 1) ⟨.tensorCopy 1, w, p, x⟩) :
    Succ P g (.copy 1) w ⟨0, 0, 0, 1, 0, 0⟩ (after_tensorCopy_1 L g ⟨.tensorCopy 1, w, p, x⟩) := by
  plain (.copy 1) (.copy 2) [after_tensorCopy_1, Nat.reduceMul, Nat.reduceAdd]

theorem st_copy_2 (hpre : Pre P L mem0) (h : RefAt P g (.copy 2) ⟨.tensorCopy 2, w, p, x⟩) :
    Succ P g (.copy 2) w ⟨0, 0, 0, 1, 0, 0⟩ (after_tensorCopy_2 L g ⟨.tensorCopy 2, w, p, x⟩) := by
  plain (.copy 2) (.copy 3) [after_tensorCopy_2, Nat.reduceMul, Nat.reduceAdd]

theorem st_copy_3 (hpre : Pre P L mem0) (h : RefAt P g (.copy 3) ⟨.tensorCopy 3, w, p, x⟩) :
    Succ P g (.copy 3) w ⟨0, 0, 0, 1, 0, 0⟩ (after_tensorCopy_3 L g ⟨.tensorCopy 3, w, p, x⟩) := by
  plain (.copy 3) (.copy 4) [after_tensorCopy_3, Nat.reduceMul, Nat.reduceAdd]

theorem st_copy_4 (hpre : Pre P L mem0) (h : RefAt P g (.copy 4) ⟨.tensorCopy 4, w, p, x⟩) :
    Succ P g (.copy 4) w ⟨0, 0, 0, 1, 0, 0⟩ (after_tensorCopy_4 L g ⟨.tensorCopy 4, w, p, x⟩) := by
  plain (.copy 4) (.copy 5) [after_tensorCopy_4, Nat.reduceMul, Nat.reduceAdd]

theorem st_copy_5 (hpre : Pre P L mem0) (h : RefAt P g (.copy 5) ⟨.tensorCopy 5, w, p, x⟩) :
    Succ P g (.copy 5) w ⟨0, 0, 0, 1, 0, 0⟩ (after_tensorCopy_5 L g ⟨.tensorCopy 5, w, p, x⟩) := by
  plain (.copy 5) (.copy 6) [after_tensorCopy_5, Nat.reduceMul, Nat.reduceAdd]

theorem st_copy_6 (hpre : Pre P L mem0) (h : RefAt P g (.copy 6) ⟨.tensorCopy 6, w, p, x⟩) :
    Succ P g (.copy 6) w ⟨0, 0, 0, 1, 0, 0⟩ (after_tensorCopy_6 L g ⟨.tensorCopy 6, w, p, x⟩) := by
  plain (.copy 6) (.copy 7) [after_tensorCopy_6, Nat.reduceMul, Nat.reduceAdd]

theorem st_copy_7 (hpre : Pre P L mem0) (h : RefAt P g (.copy 7) ⟨.tensorCopy 7, w, p, x⟩) :
    Succ P g (.copy 7) w ⟨0, 0, 0, 1, 0, 0⟩ (after_tensorCopy_7 L g ⟨.tensorCopy 7, w, p, x⟩) := by
  plain (.copy 7) (.copy 8) [after_tensorCopy_7, Nat.reduceMul, Nat.reduceAdd]

theorem st_copy_8 (hpre : Pre P L mem0) (h : RefAt P g (.copy 8) ⟨.tensorCopy 8, w, p, x⟩) :
    Succ P g (.copy 8) w ⟨0, 0, 0, 1, 0, 0⟩ (after_tensorCopy_8 L g ⟨.tensorCopy 8, w, p, x⟩) := by
  plain (.copy 8) (.copy 9) [after_tensorCopy_8, Nat.reduceMul, Nat.reduceAdd]

theorem st_copy_9 (hpre : Pre P L mem0) (h : RefAt P g (.copy 9) ⟨.tensorCopy 9, w, p, x⟩) :
    Succ P g (.copy 9) w ⟨0, 0, 0, 1, 0, 0⟩ (after_tensorCopy_9 L g ⟨.tensorCopy 9, w, p, x⟩) := by
  plain (.copy 9) (.copy 10) [after_tensorCopy_9, Nat.reduceMul, Nat.reduceAdd]

theorem st_copy_10 (hpre : Pre P L mem0) (h : RefAt P g (.copy 10) ⟨.tensorCopy 10, w, p, x⟩) :
    Succ P g (.copy 10) w ⟨0, 0, 0, 1, 0, 0⟩
      (after_tensorCopy_10 L g ⟨.tensorCopy 10, w, p, x⟩) := by
  plain (.copy 10) (.copy 11) [after_tensorCopy_10, Nat.reduceMul, Nat.reduceAdd]

theorem st_copy_11 (hpre : Pre P L mem0) (h : RefAt P g (.copy 11) ⟨.tensorCopy 11, w, p, x⟩) :
    Succ P g (.copy 11) w ⟨0, 0, 0, 1, 0, 0⟩
      (after_tensorCopy_11 L g ⟨.tensorCopy 11, w, p, x⟩) := by
  plain (.copy 11) (.copy 12) [after_tensorCopy_11, Nat.reduceMul, Nat.reduceAdd]

theorem st_copy_12 (hpre : Pre P L mem0) (h : RefAt P g (.copy 12) ⟨.tensorCopy 12, w, p, x⟩) :
    Succ P g (.copy 12) w ⟨0, 0, 0, 1, 0, 0⟩
      (after_tensorCopy_12 L g ⟨.tensorCopy 12, w, p, x⟩) := by
  plain (.copy 12) (.copy 13) [after_tensorCopy_12, Nat.reduceMul, Nat.reduceAdd]

theorem st_copy_13 (hpre : Pre P L mem0) (h : RefAt P g (.copy 13) ⟨.tensorCopy 13, w, p, x⟩) :
    Succ P g (.copy 13) w ⟨0, 0, 0, 1, 0, 0⟩
      (after_tensorCopy_13 L g ⟨.tensorCopy 13, w, p, x⟩) := by
  plain (.copy 13) (.copy 14) [after_tensorCopy_13, Nat.reduceMul, Nat.reduceAdd]

theorem st_copy_14 (hpre : Pre P L mem0) (h : RefAt P g (.copy 14) ⟨.tensorCopy 14, w, p, x⟩) :
    Succ P g (.copy 14) w ⟨0, 0, 0, 1, 0, 0⟩
      (after_tensorCopy_14 L g ⟨.tensorCopy 14, w, p, x⟩) := by
  plain (.copy 14) (.copy 15) [after_tensorCopy_14, Nat.reduceMul, Nat.reduceAdd]

theorem st_copy_15 (hpre : Pre P L mem0) (h : RefAt P g (.copy 15) ⟨.tensorCopy 15, w, p, x⟩) :
    Succ P g (.copy 15) w ⟨0, 0, 0, 1, 0, 0⟩
      (after_tensorCopy_15 L g ⟨.tensorCopy 15, w, p, x⟩) := by
  have hl : lane g = 0 := (tid_128_iff.mp h.pos.2.2.2.1).2
  plain (.copy 15) (.bar 2) [after_tensorCopy_15, Nat.reduceMul, Nat.reduceAdd, hl]

theorem st_bar_2 (hpre : Pre P L mem0) (h : RefAt P g (.bar 2) ⟨.bar 2, w, p, x⟩) :
    Succ P g (.bar 2) w ⟨1, 0, 0, 0, 0, 0⟩ (after_bar_2 L g ⟨.bar 2, w, p, x⟩) := by
  have e1 := sharedWord hpre
  plain (.bar 2) (.wait) [after_bar_2, e1]

/-- A failed poll stays at the poll. -/
theorem st_wait_no (hpre : Pre P L mem0) (h : RefAt P g .wait ⟨.mbarWait 0, w, p, x⟩) :
    ∃ pos', RefAt P g pos' (after_mbarWait_0 L g ⟨.mbarWait 0, w, p, x⟩ false) ∧
      led g pos' = led g .wait + ⟨0, 0, 0, 0, 0, 0⟩ ∧
      elects g pos' = elects g .wait + elOf .wait ∧
      leftP P g pos' (after_mbarWait_0 L g ⟨.mbarWait 0, w, p, x⟩ false).w ≤
        leftP P g .wait w :=
  ⟨.wait, ⟨rfl, h.base, h.pos⟩, by simp [led, Led.add_def], rfl, le_refl _⟩

/-- **A successful poll leaves the phase.** -/
theorem st_wait_ok (hpre : Pre P L mem0) (h : RefAt P g .wait ⟨.mbarWait 0, w, p, x⟩) :
    Exit P g (after_mbarWait_0 L g ⟨.mbarWait 0, w, p, x⟩ true) ∧
      ledExit g = led g .wait + ⟨0, 0, 0, 0, 1, 0⟩ ∧
      electsExit g = elects g .wait + elOf .wait ∧ 13 + 1 ≤ leftP P g .wait w := by
  obtain ⟨-, hb, h⟩ := h
  simp only [AtPos] at h
  exact ⟨⟨rfl, ⟨hb.tid, hb.warp, hb.offs⟩, h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩,
    by simp [led, ledExit, Led.add_def], rfl, by simp only [leftP, loopOf, pcOf]; omega⟩

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Startup
