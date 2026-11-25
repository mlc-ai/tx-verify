-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Producer.Arith
public import Kernels.FlashKdaFwd.Proof.Ref.Producer.Ledger

@[expose] public section

/-! # The reference invariant of the Producer phase is kept: the sites outside the load family

One lemma per site that is not one of the 207 tensor loads followed by another load of the same
tile body (those are generated: `StepsA.lean`, `StepsB.lean`, `StepsC.lean`): from the invariant
at the site (`RefAt`), the state that the generated transition function gives is a successor
(`Succ`): at a position of the phase with its invariant, or at the phase's exit, and the ledger
there is the ledger of the site plus the ledger of the site's event.

* `st_entry`: the `bar.sync 0` at instruction 1402. A lane other than lane 0 of the load warp
  goes to the exit; the load leader goes to the first tail poll (no tile), to the poll of the
  remainder body (one tile) or to the poll of the unrolled loop (two tiles or more).
* `st_poll_no`, `st_poll0`, `st_poll1`, `st_poll2`: a failed poll stays; a successful poll goes
  to the arrival (the leader always arrives: it is the elected lane).
* `st_arrive0`, `st_arrive1`, `st_arrive2`: the arrival goes to the first load of the body, past
  the two breakpoints of the lane-0 check; the stage-level registers of the body are computed
  here.
* `st_last0`, `st_last1`, `st_last2`: the last load of a body. After copy 0: the poll of
  copy 1. After copy 1: the loop's back edge (the poll of copy 0 at base index `u + 2`), or the
  remainder, or the tail, past the breakpoint at instruction 2075. After copy 2: the tail.
* `st_tail_no`, `st_tail0`, `st_tail1`, `st_tail2`: the three polls of the tail; the last one
  leaves the phase.

Every proof has the same parts: the facts of the old position as a conjunction of equations
(`simp only [AtPos, …] at h`), the closed forms of the launch words and of the arithmetic
(`Arith.lean`) as rewrite rules, the decided branch conditions, then `prod_pos` (unfold the
transition function, read the rewritten file at literal registers, rewrite, normalize the
32-bit arithmetic) and `prod_close` (equalities between words whose numbers are equal by linear
arithmetic). No breakpoint site is a successor: in each proof the conditions in front of the
breakpoints are decided (`%p1 = false`, `%p2 = true`, `%p87 = false`). -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Producer
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence
open PTX.Kernels.FlashKdaFwd.Proof.Ref.Startup (cu ft)

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option maxRecDepth 4000

/-- **A successor of a position**: the state `d'` is at a position of the phase with its
invariant, or at the phase's exit, and the ledger there is the ledger of `pos` plus `δ`. -/
def Succ (P : Params) (g : Nat) (pos : Pos) (δ : Led) (d' : D) : Prop :=
  (∃ pos', RefAt P g pos' d' ∧ led P g pos' = led P g pos + δ) ∨
    (Exit P g d' ∧ ledExit P g = led P g pos + δ)

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
  {w : Nat → BitVec 64} {p : Nat → Bool} {x : Nat → Value}

theorem tile_0 (u : Nat) : tile 0 u = u := rfl
theorem tile_1 (u : Nat) : tile 1 u = u + 1 := rfl
theorem tile_2 (u : Nat) : tile 2 u = u := rfl

/-- `prod_pos [lemmas]`: the register facts of the successor. -/
syntax "prod_pos" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| prod_pos [$ls,*]) => `(tactic| (
      ref_facts [AtPos, Lead, Loop, Rem, Body, LoadAt, Consts, tile, dstReg, c0Reg, dstAbs, c0Tab,
        tile_0, tile_1, tile_2, Nat.reduceMul, Nat.reduceAdd, Nat.reduceLeDiff, true_implies,
        false_implies, Bool.not_false, Bool.not_true, Bool.or_false, Bool.false_or, Bool.or_true,
        Bool.true_or, decide_true, decide_false, cmpLit, $ls,*]))

/-- `prod_close`: the goals `prod_pos` leaves: a conjunction of equations between words of
numbers that are equal by linear arithmetic, and pure facts about the indices. -/
macro "prod_close" : tactic => `(tactic| all_goals (
  (try (repeat' apply And.intro)) <;>
    (first | rfl | omega | (congr 1; omega) | (congr 2; omega))))

/-- The load leader is lane 0 of warp 4. -/
theorem tid_128_iff {g : Nat} : tid g = 128 ↔ warp g = 4 ∧ lane g = 0 := by
  unfold warp tid lane; omega

/-- The comparison `setp.lt.s32 %p, %r8, 1`: the sequence is empty. -/
theorem len_lt1 {n : Nat} (hn : n < 2 ^ 31) : scmpi .lt .s (W n) 1 = decide (n < 1) := by
  rw [scmpi_s_W _ (by decide) (by decide)]
  exact scmp_lt_W hn (by decide)

/-- The comparison `setp.lt.u32 %p, %r8, 17`: the sequence has one tile at most. -/
theorem len_lt17 {n : Nat} (hn : n < 2 ^ 31) : scmpi .lt .u (W n) 17 = decide (n < 17) := by
  rw [scmpi_lt_u_W (by omega) (by decide) (by decide)]
  rfl

/-! ### The entry -/

theorem st_entry (hpre : Pre P L mem0) (hg : g < L.threads) (hw : warp g = 4)
    (h : RefAt P g .entry ⟨.bar 5, w, p, x⟩) :
    Succ P g .entry dBar (after_bar_5 L g ⟨.bar 5, w, p, x⟩) := by
  obtain ⟨-, h⟩ := h
  simp only [AtPos, Startup.Scan] at h
  have hs := shared_lt hpre
  have e1 := sharedWord hpre
  have e2 := tidWord (g := g) hpre
  have hlen := len_le hpre g
  have htot := Startup.total_lt hpre
  have c31 : scmpi .ne .b (andi (W (tid g)) 224) 128 = false := by
    rw [tid_and224]; simp [hw]
  by_cases hl : lane g = 0
  · have ht : tid g = 128 := tid_128_iff.mpr ⟨hw, hl⟩
    have c32 : scmpi .eq .b (W 1) 0 = false := by decide
    have e2' : sreg ((L.tidOf g).get .x) = W 128 := by rw [e2, ht]
    have e3 := ctaidY hpre hg
    have e4 := tilesParam hpre
    have e5 := scaleWord hpre
    have e6 := slotBase_word hpre hg
    have e7 := totalParam hpre
    have c35 : scmpi .eq .b (andi (W 128) 31) 0 = true := by decide
    have c34 := len_lt1 (n := P.length (seqOf P g)) (by omega)
    have c36 := len_lt17 (n := P.length (seqOf P g)) (by omega)
    by_cases h0 : P.length (seqOf P g) < 1
    · have hT : tilesOf P g = 0 := by simp only [tilesOf, tiles]; omega
      refine .inl ⟨.tail 0, ⟨?_, ?_⟩, led_entry_tail ht hT⟩
      · ref_site [after_bar_5, h, hl, c31, c32, c34, h0, decide_true, Bool.not_false,
          Bool.or_false]
      · prod_pos [after_bar_5, h, hl, ht, hT, c31, c32, c34, h0, e1, i32_zero_stage, shl3,
          emptyAddr hpre, par_zero]
        prod_close
    · by_cases h17 : P.length (seqOf P g) < 17
      · have hT : tilesOf P g = 1 := by simp only [tilesOf, tiles]; omega
        refine .inl ⟨.poll 2 0, ⟨?_, ?_⟩, led_entry_poll ht 2 (by decide)⟩
        · ref_site [after_bar_5, tail_1412, h, hl, c31, c32, c34, c36, h0, h17, decide_true,
            decide_false, Bool.not_false, Bool.or_false]
        · prod_pos [after_bar_5, tail_1412, h, hl, ht, hT, c31, c32, c34, c36, h0, h17, e1, e2',
            e3, e4, e5, e6, c35, i32_zero_stage, shl3, emptyAddr hpre, par_zero]
          prod_close
      · have hT : 2 ≤ tilesOf P g := by simp only [tilesOf, tiles]; omega
        refine .inl ⟨.poll 0 0, ⟨?_, ?_⟩, led_entry_poll ht 0 (by decide)⟩
        · ref_site [after_bar_5, tail_1412, tail_1436, h, hl, c31, c32, c34, c36, h0, h17,
            decide_true, decide_false, Bool.not_false, Bool.or_false]
        · prod_pos [after_bar_5, tail_1412, tail_1436, h, hl, ht, c31, c32, c34, c36, h0, h17,
            e1, e2', e3, e4, e5, e6, e7, c35, i32_zero_stage, shl3, emptyAddr hpre, par_zero]
          prod_close
  · have ht : tid g ≠ 128 := fun h' => hl (tid_128_iff.mp h').2
    have hr := (warp_eq4_iff g).mp hw
    have c32 : scmpi .eq .b (W 0) 0 = true := by decide
    have c48 : scmpi .lt .u (W (tid g)) 128 = false := by rw [tid_lt128]; simp; omega
    have c49 : scmpi .lt .u (W (tid g)) 160 = true := by rw [tid_lt160]; simp; omega
    have c77 : scmpi .gt .u (W (tid g)) 127 = true := by
      rw [scmpi_gt_u_W (by omega) (by decide) (by decide)]; simp; omega
    refine .inr ⟨⟨?_, ?_, ?_, ?_⟩, led_entry_exit ht⟩ <;>
      file_simp [after_bar_5, h, hl, c31, c32, e2, c48, c49, c77, ↓reduceIte, Bool.false_or,
        Arith32.sel, cmpLit, Bool.false_eq_true]

/-! ### Polls and arrivals of the three copies -/

/-- A failed poll stays at the poll. -/
theorem st_poll_no (c : Fin 3) (u : Nat) {d : D} (h : RefAt P g (.poll c u) d) :
    Succ P g (.poll c u) dNone d :=
  .inl ⟨.poll c u, h, led_poll_no _⟩

theorem st_poll0 (hpre : Pre P L mem0) {u : Nat}
    (h : RefAt P g (.poll 0 u) ⟨.mbarWait 1, w, p, x⟩) :
    Succ P g (.poll 0 u) (dPoll (tile 0 u % 3))
      (after_mbarWait_1 L g ⟨.mbarWait 1, w, p, x⟩ true) := by
  obtain ⟨-, h⟩ := h
  simp only [AtPos, finVal, Lead, Loop] at h
  have e1 := sharedWord hpre
  refine .inl ⟨.arrive 0 u, ⟨?_, ?_⟩, led_poll 0 u⟩
  · ref_site [after_mbarWait_1, h]
  · prod_pos [after_mbarWait_1, h, e1, fullAddr hpre]
    prod_close

theorem st_poll1 (hpre : Pre P L mem0) {u : Nat}
    (h : RefAt P g (.poll 1 u) ⟨.mbarWait 2, w, p, x⟩) :
    Succ P g (.poll 1 u) (dPoll (tile 1 u % 3))
      (after_mbarWait_2 L g ⟨.mbarWait 2, w, p, x⟩ true) := by
  obtain ⟨-, h⟩ := h
  simp only [AtPos, finVal, Lead, Loop] at h
  have e1 := sharedWord hpre
  refine .inl ⟨.arrive 1 u, ⟨?_, ?_⟩, led_poll 1 u⟩
  · ref_site [after_mbarWait_2, h]
  · prod_pos [after_mbarWait_2, h, e1, fullAddr hpre]
    prod_close

theorem st_poll2 (hpre : Pre P L mem0) {u : Nat}
    (h : RefAt P g (.poll 2 u) ⟨.mbarWait 3, w, p, x⟩) :
    Succ P g (.poll 2 u) (dPoll (tile 2 u % 3))
      (after_mbarWait_3 L g ⟨.mbarWait 3, w, p, x⟩ true) := by
  obtain ⟨-, h⟩ := h
  simp only [AtPos, finVal, Lead, Rem] at h
  have e1 := sharedWord hpre
  refine .inl ⟨.arrive 2 u, ⟨?_, ?_⟩, led_poll 2 u⟩
  · ref_site [after_mbarWait_3, h]
  · prod_pos [after_mbarWait_3, h, e1, fullAddr hpre]
    prod_close

theorem st_arrive0 (hpre : Pre P L mem0) (hg : g < L.threads) {u : Nat}
    (h : RefAt P g (.arrive 0 u) ⟨.mbarArrive 1, w, p, x⟩) :
    Succ P g (.arrive 0 u) (dArr (tile 0 u % 3))
      (after_mbarArrive_1 L g ⟨.mbarArrive 1, w, p, x⟩) := by
  obtain ⟨-, h⟩ := h
  simp only [AtPos, finVal, Lead, Loop] at h
  have hs := shared_lt hpre
  have e1 := sharedWord hpre
  have e3 := ctaidY hpre hg
  have hsl := slotBase_lt hpre hg
  have hsr := hpre.slotsRange
  have tw := token_word hpre (g := g) (t := u) (by omega)
  refine .inl ⟨.load 0 u 0, ⟨?_, ?_⟩, led_arrive 0 u⟩
  · ref_site [after_mbarArrive_1, h, Bool.not_false]
  · prod_pos [after_mbarArrive_1, h, e1, e3, tw, shl3, fullAddr hpre, bufBase hpre]
    prod_close

theorem st_arrive1 (hpre : Pre P L mem0) (hg : g < L.threads) {u : Nat}
    (h : RefAt P g (.arrive 1 u) ⟨.mbarArrive 2, w, p, x⟩) :
    Succ P g (.arrive 1 u) (dArr (tile 1 u % 3))
      (after_mbarArrive_2 L g ⟨.mbarArrive 2, w, p, x⟩) := by
  obtain ⟨-, h⟩ := h
  simp only [AtPos, finVal, Lead, Loop] at h
  have hs := shared_lt hpre
  have e1 := sharedWord hpre
  have e3 := ctaidY hpre hg
  have hsl := slotBase_lt hpre hg
  have hsr := hpre.slotsRange
  have htk := token_lt hpre (g := g) (t := u + 1) (by omega)
  have htot := Startup.total_lt hpre
  have tw := token_word hpre (g := g) (t := u) (by omega)
  refine .inl ⟨.load 1 u 0, ⟨?_, ?_⟩, led_arrive 1 u⟩
  · ref_site [after_mbarArrive_2, h]
  · prod_pos [after_mbarArrive_2, h, e1, e3, tw, shl3, fullAddr hpre, bufBase hpre]
    prod_close

theorem st_arrive2 (hpre : Pre P L mem0) (hg : g < L.threads) {u : Nat}
    (h : RefAt P g (.arrive 2 u) ⟨.mbarArrive 3, w, p, x⟩) :
    Succ P g (.arrive 2 u) (dArr (tile 2 u % 3))
      (after_mbarArrive_3 L g ⟨.mbarArrive 3, w, p, x⟩) := by
  obtain ⟨-, h⟩ := h
  simp only [AtPos, finVal, Lead, Rem] at h
  have hs := shared_lt hpre
  have e1 := sharedWord hpre
  have e3 := ctaidY hpre hg
  have e7 := totalParam hpre
  have hsl := slotBase_lt hpre hg
  have hsr := hpre.slotsRange
  have tw := token_word hpre (g := g) (t := u) (by omega)
  refine .inl ⟨.load 2 u 0, ⟨?_, ?_⟩, led_arrive 2 u⟩
  · ref_site [after_mbarArrive_3, tail_1883, h, Bool.not_false]
  · prod_pos [after_mbarArrive_3, tail_1883, h, e1, e3, e7, tw, shl3, fullAddr hpre,
      bufBase hpre]
    prod_close

/-! ### The last load of each copy -/

set_option hygiene false in
/-- `load_facts`: the facts of a load position as a conjunction of equations. -/
macro "load_facts" : tactic => `(tactic| (
  simp only [AtPos, PTX.Kernels.FlashKdaFwd.Proof.Ref.finVal, Lead, Loop, Rem, Body, LoadAt,
    Consts, tile_0, tile_1, tile_2, dstReg, c0Reg, dstAbs, c0Tab,
    PTX.Kernels.FlashKdaFwd.Proof.Ref.getLit, Nat.reduceMul, Nat.reduceAdd, Nat.reduceLeDiff,
    true_implies, false_implies] at h))

/-- `load_step [after]`: the step of a tensor load that is followed by another load of the same
tile body (the generated lemmas of `StepsA.lean`, `StepsB.lean`, `StepsC.lean`): the transition
`after` writes the destination and the first coordinate of the next load. -/
syntax "load_step" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| load_step [$ls,*]) => `(tactic| (
      obtain ⟨-, h⟩ := h
      have hs := shared_lt hpre
      load_facts
      refine ⟨rfl, ?_⟩
      prod_pos [$ls,*, h, scale_shl3, scale_shl4, scale_shl5, scale_shl6]
      prod_close))

theorem st_last0 (hpre : Pre P L mem0) {u : Nat}
    (h : RefAt P g (.load 0 u 69) ⟨.tensorCopy 85, w, p, x⟩) :
    Succ P g (.load 0 u 69) (dIss (tile 0 u % 3))
      (after_tensorCopy_85 L g ⟨.tensorCopy 85, w, p, x⟩) := by
  obtain ⟨-, h⟩ := h
  load_facts
  refine .inl ⟨.poll 1 u, ⟨rfl, ?_⟩, led_last_0 u⟩
  prod_pos [after_tensorCopy_85, h, stage_word, par_word, shl3, emptyAddr hpre]
  prod_close

theorem st_last1 (hpre : Pre P L mem0) {u : Nat}
    (h : RefAt P g (.load 1 u 69) ⟨.tensorCopy 155, w, p, x⟩) :
    Succ P g (.load 1 u 69) (dIss (tile 1 u % 3))
      (after_tensorCopy_155 L g ⟨.tensorCopy 155, w, p, x⟩) := by
  obtain ⟨-, h⟩ := h
  load_facts
  have e1 := sharedWord hpre
  have hT := tiles_lt hpre g
  have sw : sel (scmpi .eq .b (addi (W ((u + 1) % 3)) 1) 3) (i32 0)
      (addi (W ((u + 1) % 3)) 1) = W ((u + 2) % 3) := stage_word (u + 1)
  have pw : xor32 (W (par (u + 1)))
      (sel (scmpi .eq .b (addi (W ((u + 1) % 3)) 1) 3) (i32 1) (i32 0)) = W (par (u + 2)) :=
    par_word (u + 1)
  have a2 := Startup.addi2 (a := u) (by omega)
  have mx := maxTiles (T := tilesOf P g) (by omega) hT
  have ev := evenTiles hT
  have od := oddTiles hT
  have c40 := Startup.cmp_ne (a := u + 2) (b := tilesOf P g - tilesOf P g % 2) (by omega)
    (by omega)
  have c41 := Startup.cmp_ne0 (a := tilesOf P g % 2) (by omega)
  by_cases hne : u + 2 ≠ tilesOf P g - tilesOf P g % 2
  · have c40t := c40.trans (decide_eq_true hne)
    refine .inl ⟨.poll 0 (u + 2), ⟨?_, ?_⟩, led_last_1 0 (by decide) u⟩
    · ref_site [after_tensorCopy_155, h, a2, mx, ev, c40t]
    · prod_pos [after_tensorCopy_155, h, e1, sw, pw, a2, mx, ev, c40t, shl3, emptyAddr hpre]
      prod_close
  · have c40f := c40.trans (decide_eq_false hne)
    by_cases hodd : tilesOf P g % 2 ≠ 0
    · have c41t := c41.trans (decide_eq_true hodd)
      refine .inl ⟨.poll 2 (u + 2), ⟨?_, ?_⟩, led_last_1 2 (by decide) u⟩
      · ref_site [after_tensorCopy_155, h, a2, mx, ev, od, c40f, c41t, Bool.not_true]
      · prod_pos [after_tensorCopy_155, h, e1, sw, pw, a2, mx, ev, od, c40f, c41t, shl3,
          emptyAddr hpre]
        prod_close
    · have c41f := c41.trans (decide_eq_false hodd)
      have heq : u + 2 = tilesOf P g - tilesOf P g % 2 := not_not.mp hne
      have hev : tilesOf P g % 2 = 0 := not_not.mp hodd
      have hTu : tilesOf P g = u + 2 := by omega
      refine .inl ⟨.tail 0, ⟨?_, ?_⟩, led_last_1_tail u hTu⟩
      · ref_site [after_tensorCopy_155, h, a2, mx, ev, od, c40f, c41f, Bool.not_false]
      · prod_pos [after_tensorCopy_155, h, e1, sw, pw, a2, mx, ev, od, c40f, c41f, shl3,
          emptyAddr hpre]
        prod_close

theorem st_last2 (hpre : Pre P L mem0) {u : Nat}
    (h : RefAt P g (.load 2 u 69) ⟨.tensorCopy 225, w, p, x⟩) :
    Succ P g (.load 2 u 69) (dIss (tile 2 u % 3))
      (after_tensorCopy_225 L g ⟨.tensorCopy 225, w, p, x⟩) := by
  obtain ⟨-, h⟩ := h
  load_facts
  have e1 := sharedWord hpre
  have hTu : tilesOf P g = u + 1 := by omega
  refine .inl ⟨.tail 0, ⟨?_, ?_⟩, led_last_2 u hTu⟩
  · ref_site [after_tensorCopy_225, h, Bool.not_false]
  · prod_pos [after_tensorCopy_225, h, e1, stage_word, par_word, shl3, emptyAddr hpre]
    prod_close

/-! ### The tail -/

/-- A failed poll of the tail stays at the poll. -/
theorem st_tail_no (j : Fin 3) {d : D} (h : RefAt P g (.tail j) d) :
    Succ P g (.tail j) dNone d :=
  .inl ⟨.tail j, h, led_poll_no _⟩

theorem st_tail0 (hpre : Pre P L mem0) (h : RefAt P g (.tail 0) ⟨.mbarWait 4, w, p, x⟩) :
    Succ P g (.tail 0) (dPoll ((tilesOf P g + 0) % 3))
      (after_mbarWait_4 L g ⟨.mbarWait 4, w, p, x⟩ true) := by
  obtain ⟨-, h⟩ := h
  simp only [AtPos, finVal] at h
  refine .inl ⟨.tail 1, ⟨rfl, ?_⟩, led_tail 0 (by decide)⟩
  prod_pos [after_mbarWait_4, h, stage_word, par_word, shl3, emptyAddr hpre]
  prod_close

theorem st_tail1 (hpre : Pre P L mem0) (h : RefAt P g (.tail 1) ⟨.mbarWait 5, w, p, x⟩) :
    Succ P g (.tail 1) (dPoll ((tilesOf P g + 1) % 3))
      (after_mbarWait_5 L g ⟨.mbarWait 5, w, p, x⟩ true) := by
  obtain ⟨-, h⟩ := h
  simp only [AtPos, finVal] at h
  have sw : sel (scmpi .eq .b (addi (W ((tilesOf P g + 1) % 3)) 1) 3) (i32 0)
      (addi (W ((tilesOf P g + 1) % 3)) 1) = W ((tilesOf P g + 2) % 3) :=
    stage_word (tilesOf P g + 1)
  have pw : xor32 (W (par (tilesOf P g + 1)))
      (sel (scmpi .eq .b (addi (W ((tilesOf P g + 1) % 3)) 1) 3) (i32 1) (i32 0)) =
      W (par (tilesOf P g + 2)) := par_word (tilesOf P g + 1)
  refine .inl ⟨.tail 2, ⟨rfl, ?_⟩, led_tail 1 (by decide)⟩
  prod_pos [after_mbarWait_5, h, sw, pw, shl3, emptyAddr hpre]
  prod_close

/-- **The last poll of the tail leaves the phase.** -/
theorem st_tail2 (hpre : Pre P L mem0) (h : RefAt P g (.tail 2) ⟨.mbarWait 6, w, p, x⟩) :
    Succ P g (.tail 2) (dPoll ((tilesOf P g + 2) % 3))
      (after_mbarWait_6 L g ⟨.mbarWait 6, w, p, x⟩ true) := by
  obtain ⟨-, h⟩ := h
  simp only [AtPos, finVal] at h
  have ht := h.1
  have hl : lane g = 0 := (tid_128_iff.mp ht).2
  have e2 : sreg ((L.tidOf g).get .x) = W 128 := by rw [tidWord hpre, ht]
  have c48 : scmpi .lt .u (W 128) 128 = false := by decide
  have c49 : scmpi .lt .u (W 128) 160 = true := by decide
  have c77 : scmpi .gt .u (W 128) 127 = true := by decide
  refine .inr ⟨⟨?_, ?_, ?_, ?_⟩, led_tail_exit ht⟩ <;>
    file_simp [after_mbarWait_6, h, hl, ht, e2, c48, c49, c77, ↓reduceIte, Arith32.sel, cmpLit,
      Bool.false_eq_true]

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Producer
