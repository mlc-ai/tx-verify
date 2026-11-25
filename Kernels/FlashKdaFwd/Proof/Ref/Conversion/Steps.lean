-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Conversion.Arith

@[expose] public section

/-! # The reference invariant of the Conversion phase is kept: one lemma per site

For each of the 23 sites of the phase: from the invariant at the site (`RefAt`), the state
that the generated transition function gives is at a position of the phase with its invariant,
its ledger is the ledger of the site plus what the site's event counts, and it has one more
event of the phase behind it (`Succ`); for the second `bar.sync 0` the successor satisfies the
exit condition (`st_bar_1`).

* A **load** (`st_ld_j`): the transition takes the loaded value `v`; its successor is the store
  of the same element, whose address `shared_mem + 2 e` is computed here, and the register the
  store writes holds the narrowed value of `v` (the second part of the statement, which the
  invariant's `Link` records).
* A **store** (`st_st_j`): the successor is the next load. The local code computes the next
  element index (`pair_words`), and the pointer code moves the loop's base pointer by four
  times the index and by 32768 and swizzles it. The pointer code continues only under its
  condition; the lemmas `tail_<pc>_at` evaluate it on the base pointer `sptr g S`
  (`Lib.lean: word_run`, `cvta_shared`), so the statement is "the transition's outcome **is** a
  state": no pointer leaves the window, the thread is not dead.
* The two back edges: `st_st_1` (first loop: the exit test compares the round counter with
  `head g`) and `st_st_9` (second loop: the test `pair index < 232` holds in the first nine
  rounds); the first loop exits into the second, the second to the first `bar.sync 0`.
* `st_bar_1`: the local code after the second `bar.sync 0` builds the base pointer of the
  carry loads (`cvta.shared.u64`, one move by a word), clears the 128 carry registers (a run
  of 127 register moves, `r633_ok`) and, in a compute thread, computes the address of the
  first carry load. -/

namespace PTX.Kernels.FlashKdaFwd.Proof.Ref.Conversion
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32
open PTX.Kernels.FlashKdaFwd PTX.Kernels.FlashKdaFwd.Proof.Thread
open PTX.Kernels.FlashKdaFwd.Proof.Ref PTX.Kernels.FlashKdaFwd.Recurrence

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
  {w : Nat → BitVec 64} {p : Nat → Bool} {x : Nat → Value} {site : Site}

/-! ### Successors and the carried registers -/

/-- The ledger of an event that the ledger does not count. -/
abbrev led0 : Startup.Led := ⟨0, 0, 0, 0, 0, 0⟩

/-- The ledger of a `bar.sync 0`. -/
abbrev ledBar : Startup.Led := ⟨1, 0, 0, 0, 0, 0⟩

/-- **A successor inside the phase** of a position that is no load: the state `d'` is at a
position with its invariant, that position's ledger is the ledger of `pos` plus `δ`, it has
one more event before it, and it is no store (only a load leads to a store). -/
def Succ (P : Params) (g : Nat) (pos : Pos) (δ : Startup.Led) (d' : D) : Prop :=
  ∃ pos', RefAt P g pos' d' ∧ led g pos' = led g pos + δ ∧ done g pos' = done g pos + 1 ∧
    ∀ j u, pos' ≠ .st j u

/-- The word registers of `Keep` are the same in two files. -/
def SameW (w' w : Nat → BitVec 64) : Prop :=
  w' 307 = w 307 ∧ w' 308 = w 308 ∧ w' 2247 = w 2247 ∧ w' 352 = w 352 ∧ w' 314 = w 314 ∧
    w' 315 = w 315 ∧ w' 2099 = w 2099 ∧ w' 2248 = w 2248 ∧ w' 486 = w 486

/-- The six role flags are the same in two files. -/
def SameP (p' p : Nat → Bool) : Prop :=
  p' 83 = p 83 ∧ p' 84 = p 84 ∧ p' 85 = p 85 ∧ p' 86 = p 86 ∧ p' 87 = p 87 ∧ p' 88 = p 88

/-- The carried registers are kept by a transition that does not write them. -/
theorem Keep.of_frame {d d' : D} (h : Keep P g d) (hw : SameW d'.w d.w) (hp : SameP d'.p d.p) :
    Keep P g d' := by
  obtain ⟨⟨b1, b2, b3⟩, hf, hr, ⟨s1, s2, s3, s4⟩, he⟩ := h
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9⟩ := hw
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hp
  refine ⟨⟨w1.trans b1, w2.trans b2, w3.trans b3⟩, ?_, w4.trans hr,
    ⟨w5.trans s1, w6.trans s2, w7.trans s3, w8.trans s4⟩, w9.trans he⟩
  simp only [Startup.Flags, Startup.flagsOf, p1, p2, p3, p4, p5, p6] at hf ⊢
  exact hf

/-- `keep hk`: the carried registers of the successor, from those of the state (`hk`), when
the transition writes none of them. -/
macro "keep " hk:term : tactic => `(tactic|
  exact Keep.of_frame $hk ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

/-- From the evaluated outcome of a transition to "the outcome is a state with `Q`". -/
theorem ex_of_eq {o : Option (Option D)} {d0 : D} {Q : D → Prop} (h : o = some (some d0))
    (hQ : Q d0) : ∃ d', o = some (some d') ∧ Q d' := ⟨d0, h, hQ⟩

/-! ### The pointer code behind the stores, evaluated -/

/-- `word_tail run tail rb rw`: the proof of a lemma `tail_<pc>_at` (the names `hx`, `hw`,
`hab` are the lemma's hypotheses): the pointer run `run` behind the cut point `tail`, from the
base pointer in slot `rb` and the word register `rw`. -/
syntax "word_tail " ident ident num num : tactic
set_option hygiene false in
macro_rules
  | `(tactic| word_tail $run $tail $rb $rw) => `(tactic| (
      have hV : valueOf ⟨site, w, p, x⟩ $rb = sptr g a := by rw [valueOf_opaque rfl]; exact hx
      have hW : valueOf ⟨site, w, p, x⟩ $rw = .bits 64 (W b) := by
        have hk : kind $rw = .word 64 := rfl
        simp only [valueOf, hk, hw]
      obtain ⟨hc, hf⟩ := word_run (fun h1 h2 h3 h4 => $run h1 h2 h3 h4) hV hW hab
      rw [$tail:ident, across_pos hc, hf]))

variable {a b : Nat}

theorem tail_421_at (hx : x 2294 = sptr g a) (hw : w 2292 = W b)
    (hab : a + b + 32768 < 2 ^ 32) :
    tail_421 L g ⟨site, w, p, x⟩ =
      some (some ⟨.load 21, w, p, valueEx x [(2299, sptr g (swzN (a + b + 32768)))]⟩) := by
  word_tail r421_ptr tail_421 2294 2292

theorem tail_438_at (hx : x 2294 = sptr g a) (hw : w 2300 = W b)
    (hab : a + b + 32768 < 2 ^ 32) :
    tail_438 L g ⟨site, w, p, x⟩ =
      some (some ⟨.load 22, w, p, valueEx x [(2305, sptr g (swzN (a + b + 32768)))]⟩) := by
  word_tail r438_ptr tail_438 2294 2300

theorem tail_468_at (hx : x 2308 = sptr g a) (hw : w 2306 = W b)
    (hab : a + b + 32768 < 2 ^ 32) :
    tail_468 L g ⟨site, w, p, x⟩ =
      some (some ⟨.load 23, w, p, valueEx x [(2313, sptr g (swzN (a + b + 32768)))]⟩) := by
  word_tail r468_ptr tail_468 2308 2306

theorem tail_485_at (hx : x 2308 = sptr g a) (hw : w 2314 = W b)
    (hab : a + b + 32768 < 2 ^ 32) :
    tail_485 L g ⟨site, w, p, x⟩ =
      some (some ⟨.load 24, w, p, valueEx x [(2319, sptr g (swzN (a + b + 32768)))]⟩) := by
  word_tail r485_ptr tail_485 2308 2314

theorem tail_508_at (hx : x 2308 = sptr g a) (hw : w 2320 = W b)
    (hab : a + b + 32768 < 2 ^ 32) :
    tail_508 L g ⟨site, w, p, x⟩ =
      some (some ⟨.load 25, w, p, valueEx x [(2325, sptr g (swzN (a + b + 32768)))]⟩) := by
  word_tail r508_ptr tail_508 2308 2320

theorem tail_525_at (hx : x 2308 = sptr g a) (hw : w 2326 = W b)
    (hab : a + b + 32768 < 2 ^ 32) :
    tail_525 L g ⟨site, w, p, x⟩ =
      some (some ⟨.load 26, w, p, valueEx x [(2331, sptr g (swzN (a + b + 32768)))]⟩) := by
  word_tail r525_ptr tail_525 2308 2326

theorem tail_548_at (hx : x 2308 = sptr g a) (hw : w 2332 = W b)
    (hab : a + b + 32768 < 2 ^ 32) :
    tail_548 L g ⟨site, w, p, x⟩ =
      some (some ⟨.load 27, w, p, valueEx x [(2337, sptr g (swzN (a + b + 32768)))]⟩) := by
  word_tail r548_ptr tail_548 2308 2332

theorem tail_565_at (hx : x 2308 = sptr g a) (hw : w 2338 = W b)
    (hab : a + b + 32768 < 2 ^ 32) :
    tail_565 L g ⟨site, w, p, x⟩ =
      some (some ⟨.load 28, w, p, valueEx x [(2343, sptr g (swzN (a + b + 32768)))]⟩) := by
  word_tail r565_ptr tail_565 2308 2338

theorem tail_588_at (hx : x 2308 = sptr g a) (hw : w 2344 = W b)
    (hab : a + b + 32768 < 2 ^ 32) :
    tail_588 L g ⟨site, w, p, x⟩ =
      some (some ⟨.load 29, w, p, valueEx x [(2349, sptr g (swzN (a + b + 32768)))]⟩) := by
  word_tail r588_ptr tail_588 2308 2344

theorem tail_605_at (hx : x 2308 = sptr g a) (hw : w 2350 = W b)
    (hab : a + b + 32768 < 2 ^ 32) :
    tail_605 L g ⟨site, w, p, x⟩ =
      some (some ⟨.load 30, w, p, valueEx x [(2355, sptr g (swzN (a + b + 32768)))]⟩) := by
  word_tail r605_ptr tail_605 2308 2350

/-- The head of the first loop: `cvta.shared.u64` of the shared base (in the word register
`%rd47`), then the pointer run of the first load. -/
theorem tail_420_at (hpre : Pre P L mem0) (hg : g < L.threads) (hs : w 2293 = W a)
    (hw : w 2292 = W b) (hab : a + b + 32768 < 2 ^ 32) :
    tail_420 L g ⟨site, w, p, x⟩ =
      some (some ⟨.load 21, w, p,
        valueEx (valueEx x [(2294, sptr g a)]) [(2299, sptr g (swzN (a + b + 32768)))]⟩) := by
  have hV : valueOf ⟨site, w, p, x⟩ 2293 = .bits 64 (W a) := by
    have hk : kind 2293 = .word 64 := rfl
    simp only [valueOf, hk, hs]
  obtain ⟨hc, hv⟩ := cvta_shared hpre hg hV (by omega)
  rw [tail_420, under_pos hc, hv]
  exact tail_421_at rfl hw hab

/-- The head of the second loop (`%rd61`, `%rd62`). -/
theorem tail_467_at (hpre : Pre P L mem0) (hg : g < L.threads) (hs : w 2307 = W a)
    (hw : w 2306 = W b) (hab : a + b + 32768 < 2 ^ 32) :
    tail_467 L g ⟨site, w, p, x⟩ =
      some (some ⟨.load 23, w, p,
        valueEx (valueEx x [(2308, sptr g a)]) [(2313, sptr g (swzN (a + b + 32768)))]⟩) := by
  have hV : valueOf ⟨site, w, p, x⟩ 2307 = .bits 64 (W a) := by
    have hk : kind 2307 = .word 64 := rfl
    simp only [valueOf, hk, hs]
  obtain ⟨hc, hv⟩ := cvta_shared hpre hg hV (by omega)
  rw [tail_467, under_pos hc, hv]
  exact tail_468_at rfl hw hab

/-! ### The entry -/

/-- The state at the entry of the phase is at the position `fence`. -/
theorem entry_at {d : D} (h : Entry P g d) : RefAt P g .fence d :=
  ⟨h.site, Keep.of_exit h, trivial⟩

theorem st_fence (hpre : Pre P L mem0) (hg : g < L.threads)
    (h : RefAt P g .fence ⟨.fenceProxy 0, w, p, x⟩) :
    ∃ d', after_fenceProxy_0 L g ⟨.fenceProxy 0, w, p, x⟩ = some (some d') ∧
      Succ P g .fence led0 d' := by
  obtain ⟨-, hk, -⟩ := h
  have hs := shared_lt hpre
  have h307 : w 307 = W (tid g) := hk.base.tid
  have h308 : w 308 = W (warp g) := hk.base.warp
  obtain ⟨l1, l2, l3⟩ := lane_words g
  have hhd := head_le g
  have hp0 : 0 < pairs g := by unfold pairs; omega
  have e0 : pairIx g 0 = warp g := by simp [pairIx]
  obtain ⟨q1, q2, q3, q4, q5⟩ := pair_words hp0
  rw [e0] at q1 q2
  have eS := sharedWord hpre
  have eZ := zext_W (a := P.sharedBase) (by omega)
  simp only [after_fenceProxy_0, h307, h308, l1, l2, l3, rem_word g, rem_test g, rem_zext g,
    Bool.false_eq_true, ↓reduceIte, q1, q2, q4, eS, eZ]
  refine ex_of_eq (tail_420_at (a := ?_) (b := ?_) hpre hg ?_ ?_ ?_) ?_
  rotate_left 2
  · rfl
  · rfl
  · have := slot0_lt hp0
    omega
  refine ⟨.ld 0 0, ⟨rfl, ?_, ?_⟩, rfl, ?_, nofun⟩
  · keep hk
  · simp only [AtPos, finVal, LaneW, First]
    refine ⟨⟨rfl, rfl, rfl⟩, ⟨by omega, (show i32 0 = W 0 by decide), rfl, ?_⟩, rfl, rfl, rfl,
      rfl, congrArg (sptr g) (rd_norm P _)⟩
    show W (warp g) = W (pairIx g 0)
    rw [e0]
  · simp only [done, elemIx, qOf, finVal, getLit]

/-! ### The loads -/

/-- `ld_fin`: the equation between the numbers of events before two positions. -/
syntax "ld_fin" : tactic
macro_rules
  | `(tactic| ld_fin) => `(tactic| (first
      | rfl
      | (simp only [done, elemIx, qOf, finVal, getLit]; omega)))

theorem st_ld_0 (hpre : Pre P L mem0) {u : Nat} (v : Value)
    (h : RefAt P g (.ld 0 u) ⟨.load 21, w, p, x⟩) :
    RefAt P g (.st 0 u) (after_load_21 L g ⟨.load 21, w, p, x⟩ v) ∧
      (after_load_21 L g ⟨.load 21, w, p, x⟩ v).x 96 =
        okVal (.bits 32 0) (Rules.narrowE [v]) := by
  obtain ⟨-, hk, h⟩ := h
  simp only [AtPos, finVal, LaneW, First] at h
  obtain ⟨hl, hf, h548, h551, h552, h2294, h2299⟩ := h
  have hhd := head_le g
  have hup : u < pairs g := by unfold pairs; omega
  have e1 := wr_word hpre (e := slot0 g u) (by have := slot0_lt hup; omega)
  refine ⟨⟨rfl, ?_, ?_⟩, rfl⟩
  · keep hk
  · simp only [AtPos, finVal, LaneW, First]
    refine ⟨hl, hf, h548, h552, h2294, ?_⟩
    show add32 (w 552) (shl (w 551) 1) = _
    rw [h552, h551]
    exact e1

theorem st_ld_1 (hpre : Pre P L mem0) {u : Nat} (v : Value)
    (h : RefAt P g (.ld 1 u) ⟨.load 22, w, p, x⟩) :
    RefAt P g (.st 1 u) (after_load_22 L g ⟨.load 22, w, p, x⟩ v) ∧
      (after_load_22 L g ⟨.load 22, w, p, x⟩ v).x 97 =
        okVal (.bits 32 0) (Rules.narrowE [v]) := by
  obtain ⟨-, hk, h⟩ := h
  simp only [AtPos, finVal, LaneW, First] at h
  obtain ⟨hl, hf, h560, h552, h2305⟩ := h
  have hhd := head_le g
  have hup : u < pairs g := by unfold pairs; omega
  have e1 := wr_word hpre (e := slot0 g u + 1) (slot0_lt hup)
  refine ⟨⟨rfl, ?_, ?_⟩, rfl⟩
  · keep hk
  · simp only [AtPos, finVal, LaneW, First]
    refine ⟨hl, hf, ?_⟩
    show add32 (w 552) (shl (w 560) 1) = _
    rw [h552, h560]
    exact e1

/-- A round of the second loop has its pairs among the thread's. -/
theorem second_lt {u : Nat} {d : D} (h : Second g u d) : u + 3 < pairs g := by
  obtain ⟨⟨m, hm, rfl⟩, -⟩ := h
  unfold pairs
  omega

theorem st_ld_2 (hpre : Pre P L mem0) {u : Nat} (v : Value)
    (h : RefAt P g (.ld 2 u) ⟨.load 23, w, p, x⟩) :
    RefAt P g (.st 2 u) (after_load_23 L g ⟨.load 23, w, p, x⟩ v) ∧
      (after_load_23 L g ⟨.load 23, w, p, x⟩ v).x 98 =
        okVal (.bits 32 0) (Rules.narrowE [v]) := by
  obtain ⟨-, hk, h⟩ := h
  simp only [AtPos, finVal, LaneW] at h
  obtain ⟨hl, hf, h579, h582, h583, h2308, h2313⟩ := h
  have hup := second_lt hf
  have e1 := wr_word hpre (e := slot0 g u)
    (by have := slot0_lt (g := g) (u := u) (by omega); omega)
  refine ⟨⟨rfl, ?_, ?_⟩, rfl⟩
  · keep hk
  · simp only [AtPos, finVal, LaneW]
    refine ⟨hl, hf, h579, h583, h2308, ?_⟩
    show add32 (w 583) (shl (w 582) 1) = _
    rw [h583, h582]
    exact e1

theorem st_ld_3 (hpre : Pre P L mem0) {u : Nat} (v : Value)
    (h : RefAt P g (.ld 3 u) ⟨.load 24, w, p, x⟩) :
    RefAt P g (.st 3 u) (after_load_24 L g ⟨.load 24, w, p, x⟩ v) ∧
      (after_load_24 L g ⟨.load 24, w, p, x⟩ v).x 99 =
        okVal (.bits 32 0) (Rules.narrowE [v]) := by
  obtain ⟨-, hk, h⟩ := h
  simp only [AtPos, finVal, LaneW] at h
  obtain ⟨hl, hf, h591, h583, h2308, h2319⟩ := h
  have hup := second_lt hf
  have e1 := wr_word hpre (e := slot0 g u + 1) (slot0_lt (by omega))
  refine ⟨⟨rfl, ?_, ?_⟩, rfl⟩
  · keep hk
  · simp only [AtPos, finVal, LaneW]
    refine ⟨hl, hf, h583, h2308, ?_⟩
    show add32 (w 583) (shl (w 591) 1) = _
    rw [h583, h591]
    exact e1

theorem st_ld_4 (hpre : Pre P L mem0) {u : Nat} (v : Value)
    (h : RefAt P g (.ld 4 u) ⟨.load 25, w, p, x⟩) :
    RefAt P g (.st 4 u) (after_load_25 L g ⟨.load 25, w, p, x⟩ v) ∧
      (after_load_25 L g ⟨.load 25, w, p, x⟩ v).x 100 =
        okVal (.bits 32 0) (Rules.narrowE [v]) := by
  obtain ⟨-, hk, h⟩ := h
  simp only [AtPos, finVal, LaneW] at h
  obtain ⟨hl, hf, h594, h602, h605, h583, h2308, h2325⟩ := h
  have hup := second_lt hf
  have e1 := wr_word hpre (e := slot0 g (u + 1))
    (by have := slot0_lt (g := g) (u := u + 1) (by omega); omega)
  refine ⟨⟨rfl, ?_, ?_⟩, rfl⟩
  · keep hk
  · simp only [AtPos, finVal, LaneW]
    refine ⟨hl, hf, h594, h602, h583, h2308, ?_⟩
    show add32 (w 583) (shl (w 605) 1) = _
    rw [h583, h605]
    exact e1

theorem st_ld_5 (hpre : Pre P L mem0) {u : Nat} (v : Value)
    (h : RefAt P g (.ld 5 u) ⟨.load 26, w, p, x⟩) :
    RefAt P g (.st 5 u) (after_load_26 L g ⟨.load 26, w, p, x⟩ v) ∧
      (after_load_26 L g ⟨.load 26, w, p, x⟩ v).x 101 =
        okVal (.bits 32 0) (Rules.narrowE [v]) := by
  obtain ⟨-, hk, h⟩ := h
  simp only [AtPos, finVal, LaneW] at h
  obtain ⟨hl, hf, h613, h583, h2308, h2331⟩ := h
  have hup := second_lt hf
  have e1 := wr_word hpre (e := slot0 g (u + 1) + 1) (slot0_lt (by omega))
  refine ⟨⟨rfl, ?_, ?_⟩, rfl⟩
  · keep hk
  · simp only [AtPos, finVal, LaneW]
    refine ⟨hl, hf, h583, h2308, ?_⟩
    show add32 (w 583) (shl (w 613) 1) = _
    rw [h583, h613]
    exact e1

theorem st_ld_6 (hpre : Pre P L mem0) {u : Nat} (v : Value)
    (h : RefAt P g (.ld 6 u) ⟨.load 27, w, p, x⟩) :
    RefAt P g (.st 6 u) (after_load_27 L g ⟨.load 27, w, p, x⟩ v) ∧
      (after_load_27 L g ⟨.load 27, w, p, x⟩ v).x 102 =
        okVal (.bits 32 0) (Rules.narrowE [v]) := by
  obtain ⟨-, hk, h⟩ := h
  simp only [AtPos, finVal, LaneW] at h
  obtain ⟨hl, hf, h616, h624, h627, h583, h2308, h2337⟩ := h
  have hup := second_lt hf
  have e1 := wr_word hpre (e := slot0 g (u + 2))
    (by have := slot0_lt (g := g) (u := u + 2) (by omega); omega)
  refine ⟨⟨rfl, ?_, ?_⟩, rfl⟩
  · keep hk
  · simp only [AtPos, finVal, LaneW]
    refine ⟨hl, hf, h616, h624, h583, h2308, ?_⟩
    show add32 (w 583) (shl (w 627) 1) = _
    rw [h583, h627]
    exact e1

theorem st_ld_7 (hpre : Pre P L mem0) {u : Nat} (v : Value)
    (h : RefAt P g (.ld 7 u) ⟨.load 28, w, p, x⟩) :
    RefAt P g (.st 7 u) (after_load_28 L g ⟨.load 28, w, p, x⟩ v) ∧
      (after_load_28 L g ⟨.load 28, w, p, x⟩ v).x 103 =
        okVal (.bits 32 0) (Rules.narrowE [v]) := by
  obtain ⟨-, hk, h⟩ := h
  simp only [AtPos, finVal, LaneW] at h
  obtain ⟨hl, hf, h635, h583, h2308, h2343⟩ := h
  have hup := second_lt hf
  have e1 := wr_word hpre (e := slot0 g (u + 2) + 1) (slot0_lt (by omega))
  refine ⟨⟨rfl, ?_, ?_⟩, rfl⟩
  · keep hk
  · simp only [AtPos, finVal, LaneW]
    refine ⟨hl, hf, h583, h2308, ?_⟩
    show add32 (w 583) (shl (w 635) 1) = _
    rw [h583, h635]
    exact e1

theorem st_ld_8 (hpre : Pre P L mem0) {u : Nat} (v : Value)
    (h : RefAt P g (.ld 8 u) ⟨.load 29, w, p, x⟩) :
    RefAt P g (.st 8 u) (after_load_29 L g ⟨.load 29, w, p, x⟩ v) ∧
      (after_load_29 L g ⟨.load 29, w, p, x⟩ v).x 104 =
        okVal (.bits 32 0) (Rules.narrowE [v]) := by
  obtain ⟨-, hk, h⟩ := h
  simp only [AtPos, finVal, LaneW] at h
  obtain ⟨hl, hf, h638, h646, h649, h583, h2308, h2349⟩ := h
  have hup := second_lt hf
  have e1 := wr_word hpre (e := slot0 g (u + 3))
    (by have := slot0_lt (g := g) (u := u + 3) (by omega); omega)
  refine ⟨⟨rfl, ?_, ?_⟩, rfl⟩
  · keep hk
  · simp only [AtPos, finVal, LaneW]
    refine ⟨hl, hf, h638, h646, h583, h2308, ?_⟩
    show add32 (w 583) (shl (w 649) 1) = _
    rw [h583, h649]
    exact e1

theorem st_ld_9 (hpre : Pre P L mem0) {u : Nat} (v : Value)
    (h : RefAt P g (.ld 9 u) ⟨.load 30, w, p, x⟩) :
    RefAt P g (.st 9 u) (after_load_30 L g ⟨.load 30, w, p, x⟩ v) ∧
      (after_load_30 L g ⟨.load 30, w, p, x⟩ v).x 105 =
        okVal (.bits 32 0) (Rules.narrowE [v]) := by
  obtain ⟨-, hk, h⟩ := h
  simp only [AtPos, finVal, LaneW] at h
  obtain ⟨hl, hf, h657, h583, h2355⟩ := h
  have hup := second_lt hf
  have e1 := wr_word hpre (e := slot0 g (u + 3) + 1) (slot0_lt (by omega))
  refine ⟨⟨rfl, ?_, ?_⟩, rfl⟩
  · keep hk
  · simp only [AtPos, finVal, LaneW]
    refine ⟨hl, hf, ?_⟩
    show add32 (w 583) (shl (w 657) 1) = _
    rw [h583, h657]
    exact e1

/-! ### The stores of the first loop -/

theorem st_st_0 (hpre : Pre P L mem0) (hg : g < L.threads) {u : Nat}
    (h : RefAt P g (.st 0 u) ⟨.store 0, w, p, x⟩) :
    ∃ d', after_store_0 L g ⟨.store 0, w, p, x⟩ = some (some d') ∧
      Succ P g (.st 0 u) led0 d' := by
  obtain ⟨-, hk, h⟩ := h
  have hs := shared_lt hpre
  simp only [AtPos, finVal, LaneW, First] at h
  obtain ⟨⟨h316, h317, h318⟩, ⟨hu, h2100, h319, h2101⟩, h548, h552, h2294, h554⟩ := h
  have hhd := head_le g
  have hup : u < pairs g := by unfold pairs; omega
  obtain ⟨q1, q2, q3, q4, q5⟩ := pair_words hup
  simp only [after_store_0, h2101, h548, h316, q3, q5]
  refine ex_of_eq (tail_438_at (b := ?_) h2294 ?_ ?_) ?_
  rotate_left 1
  · rfl
  · have := slot0_lt hup
    omega
  refine ⟨.ld 1 u, ⟨rfl, ?_, ?_⟩, rfl, by ld_fin, nofun⟩
  · keep hk
  · simp only [AtPos, finVal, LaneW, First]
    exact ⟨⟨h316, h317, h318⟩, ⟨hu, h2100, h319, h2101⟩, rfl, h552,
      congrArg (sptr g) (rd_norm P _)⟩

theorem st_st_1 (hpre : Pre P L mem0) (hg : g < L.threads) {u : Nat}
    (h : RefAt P g (.st 1 u) ⟨.store 1, w, p, x⟩) :
    ∃ d', after_store_1 L g ⟨.store 1, w, p, x⟩ = some (some d') ∧
      Succ P g (.st 1 u) led0 d' := by
  obtain ⟨-, hk, h⟩ := h
  have hs := shared_lt hpre
  simp only [AtPos, finVal, LaneW, First] at h
  obtain ⟨⟨h316, h317, h318⟩, ⟨hu, h2100, h319, h2101⟩, h562⟩ := h
  have hhd := head_le g
  have hup : u < pairs g := by unfold pairs; omega
  have hup1 : u + 1 < pairs g := by unfold pairs; omega
  obtain ⟨i1, -, -, -⟩ := pairIx_words hup
  have c1 := cnt_word (u := u) (by omega)
  have t1 := first_test hu
  obtain ⟨q1, q2, q3, q4, q5⟩ := pair_words hup1
  have eS := sharedWord hpre
  have eZ := zext_W (a := P.sharedBase) (by omega)
  have hsl := slot0_lt hup1
  by_cases hne : u + 1 ≠ head g
  · have t1' := t1.trans (decide_eq_true hne)
    simp only [after_store_1, h2101, h2100, h319, h318, h317, i1, c1, t1', ↓reduceIte, q1, q2,
      q4, eS, eZ]
    refine ex_of_eq (tail_420_at (a := ?_) (b := ?_) hpre hg ?_ ?_ ?_) ?_
    rotate_left 2
    · rfl
    · rfl
    · omega
    refine ⟨.ld 0 (u + 1), ⟨rfl, ?_, ?_⟩, rfl, by ld_fin, nofun⟩
    · keep hk
    · simp only [AtPos, finVal, LaneW, First]
      exact ⟨⟨h316, h317, h318⟩, ⟨by omega, rfl, h319, rfl⟩, rfl, rfl, rfl, rfl,
        congrArg (sptr g) (rd_norm P _)⟩
  · have t1' := t1.trans (decide_eq_false hne)
    simp only [after_store_1, h2101, h2100, h319, h318, h317, i1, c1, t1', Bool.false_eq_true,
      ↓reduceIte, q1, q2, q4, eS, eZ]
    refine ex_of_eq (tail_467_at (a := ?_) (b := ?_) hpre hg ?_ ?_ ?_) ?_
    rotate_left 2
    · rfl
    · rfl
    · omega
    refine ⟨.ld 2 (u + 1), ⟨rfl, ?_, ?_⟩, rfl, by ld_fin, nofun⟩
    · keep hk
    · simp only [AtPos, finVal, LaneW, Second]
      exact ⟨⟨h316, h317, h318⟩, ⟨⟨0, by decide, by omega⟩, rfl⟩, rfl, rfl, rfl, rfl,
        congrArg (sptr g) (rd_norm P _)⟩

/-! ### The stores of the second loop -/

theorem st_st_2 (hpre : Pre P L mem0) (hg : g < L.threads) {u : Nat}
    (h : RefAt P g (.st 2 u) ⟨.store 2, w, p, x⟩) :
    ∃ d', after_store_2 L g ⟨.store 2, w, p, x⟩ = some (some d') ∧
      Succ P g (.st 2 u) led0 d' := by
  obtain ⟨-, hk, h⟩ := h
  have hs := shared_lt hpre
  simp only [AtPos, finVal, LaneW] at h
  obtain ⟨⟨h316, h317, h318⟩, hf, h579, h583, h2308, h585⟩ := h
  have hup := second_lt hf
  obtain ⟨q1, q2, q3, q4, q5⟩ := pair_words (g := g) (r := u) (by omega)
  have h2101 : w 2101 = W (pairIx g u) := hf.2
  simp only [after_store_2, h2101, h579, h316, q3, q5]
  refine ex_of_eq (tail_485_at (b := ?_) h2308 ?_ ?_) ?_
  rotate_left 1
  · rfl
  · have := slot0_lt (g := g) (u := u) (by omega)
    omega
  refine ⟨.ld 3 u, ⟨rfl, ?_, ?_⟩, rfl, by ld_fin, nofun⟩
  · keep hk
  · simp only [AtPos, finVal, LaneW]
    exact ⟨⟨h316, h317, h318⟩, hf, rfl, h583, h2308, congrArg (sptr g) (rd_norm P _)⟩

theorem st_st_3 (hpre : Pre P L mem0) (hg : g < L.threads) {u : Nat}
    (h : RefAt P g (.st 3 u) ⟨.store 3, w, p, x⟩) :
    ∃ d', after_store_3 L g ⟨.store 3, w, p, x⟩ = some (some d') ∧
      Succ P g (.st 3 u) led0 d' := by
  obtain ⟨-, hk, h⟩ := h
  have hs := shared_lt hpre
  simp only [AtPos, finVal, LaneW] at h
  obtain ⟨⟨h316, h317, h318⟩, hf, h583, h2308, h593⟩ := h
  have hup := second_lt hf
  obtain ⟨i1, i2, i3, i4⟩ := pairIx_words (g := g) (u := u) (by omega)
  obtain ⟨q1, q2, q3, q4, q5⟩ := pair_words (g := g) (r := u + 1) (by omega)
  have h2101 : w 2101 = W (pairIx g u) := hf.2
  simp only [after_store_3, h2101, h318, h317, i1, q1, q2, q4]
  refine ex_of_eq (tail_508_at (b := ?_) h2308 ?_ ?_) ?_
  rotate_left 1
  · rfl
  · have := slot0_lt (g := g) (u := u + 1) (by omega)
    omega
  refine ⟨.ld 4 u, ⟨rfl, ?_, ?_⟩, rfl, by ld_fin, nofun⟩
  · keep hk
  · simp only [AtPos, finVal, LaneW]
    exact ⟨⟨h316, h317, h318⟩, hf, rfl, rfl, rfl, h583, h2308,
      congrArg (sptr g) (rd_norm P _)⟩

theorem st_st_4 (hpre : Pre P L mem0) (hg : g < L.threads) {u : Nat}
    (h : RefAt P g (.st 4 u) ⟨.store 4, w, p, x⟩) :
    ∃ d', after_store_4 L g ⟨.store 4, w, p, x⟩ = some (some d') ∧
      Succ P g (.st 4 u) led0 d' := by
  obtain ⟨-, hk, h⟩ := h
  have hs := shared_lt hpre
  simp only [AtPos, finVal, LaneW] at h
  obtain ⟨⟨h316, h317, h318⟩, hf, h594, h602, h583, h2308, h607⟩ := h
  have hup := second_lt hf
  obtain ⟨q1, q2, q3, q4, q5⟩ := pair_words (g := g) (r := u + 1) (by omega)
  simp only [after_store_4, h594, h602, h316, q3, q5]
  refine ex_of_eq (tail_525_at (b := ?_) h2308 ?_ ?_) ?_
  rotate_left 1
  · rfl
  · have := slot0_lt (g := g) (u := u + 1) (by omega)
    omega
  refine ⟨.ld 5 u, ⟨rfl, ?_, ?_⟩, rfl, by ld_fin, nofun⟩
  · keep hk
  · simp only [AtPos, finVal, LaneW]
    exact ⟨⟨h316, h317, h318⟩, hf, rfl, h583, h2308, congrArg (sptr g) (rd_norm P _)⟩

theorem st_st_5 (hpre : Pre P L mem0) (hg : g < L.threads) {u : Nat}
    (h : RefAt P g (.st 5 u) ⟨.store 5, w, p, x⟩) :
    ∃ d', after_store_5 L g ⟨.store 5, w, p, x⟩ = some (some d') ∧
      Succ P g (.st 5 u) led0 d' := by
  obtain ⟨-, hk, h⟩ := h
  have hs := shared_lt hpre
  simp only [AtPos, finVal, LaneW] at h
  obtain ⟨⟨h316, h317, h318⟩, hf, h583, h2308, h615⟩ := h
  have hup := second_lt hf
  obtain ⟨i1, i2, i3, i4⟩ := pairIx_words (g := g) (u := u) (by omega)
  obtain ⟨q1, q2, q3, q4, q5⟩ := pair_words (g := g) (r := u + 2) (by omega)
  have h2101 : w 2101 = W (pairIx g u) := hf.2
  simp only [after_store_5, h2101, h318, h317, i2, q1, q2, q4]
  refine ex_of_eq (tail_548_at (b := ?_) h2308 ?_ ?_) ?_
  rotate_left 1
  · rfl
  · have := slot0_lt (g := g) (u := u + 2) (by omega)
    omega
  refine ⟨.ld 6 u, ⟨rfl, ?_, ?_⟩, rfl, by ld_fin, nofun⟩
  · keep hk
  · simp only [AtPos, finVal, LaneW]
    exact ⟨⟨h316, h317, h318⟩, hf, rfl, rfl, rfl, h583, h2308,
      congrArg (sptr g) (rd_norm P _)⟩

theorem st_st_6 (hpre : Pre P L mem0) (hg : g < L.threads) {u : Nat}
    (h : RefAt P g (.st 6 u) ⟨.store 6, w, p, x⟩) :
    ∃ d', after_store_6 L g ⟨.store 6, w, p, x⟩ = some (some d') ∧
      Succ P g (.st 6 u) led0 d' := by
  obtain ⟨-, hk, h⟩ := h
  have hs := shared_lt hpre
  simp only [AtPos, finVal, LaneW] at h
  obtain ⟨⟨h316, h317, h318⟩, hf, h616, h624, h583, h2308, h629⟩ := h
  have hup := second_lt hf
  obtain ⟨q1, q2, q3, q4, q5⟩ := pair_words (g := g) (r := u + 2) (by omega)
  simp only [after_store_6, h616, h624, h316, q3, q5]
  refine ex_of_eq (tail_565_at (b := ?_) h2308 ?_ ?_) ?_
  rotate_left 1
  · rfl
  · have := slot0_lt (g := g) (u := u + 2) (by omega)
    omega
  refine ⟨.ld 7 u, ⟨rfl, ?_, ?_⟩, rfl, by ld_fin, nofun⟩
  · keep hk
  · simp only [AtPos, finVal, LaneW]
    exact ⟨⟨h316, h317, h318⟩, hf, rfl, h583, h2308, congrArg (sptr g) (rd_norm P _)⟩

theorem st_st_7 (hpre : Pre P L mem0) (hg : g < L.threads) {u : Nat}
    (h : RefAt P g (.st 7 u) ⟨.store 7, w, p, x⟩) :
    ∃ d', after_store_7 L g ⟨.store 7, w, p, x⟩ = some (some d') ∧
      Succ P g (.st 7 u) led0 d' := by
  obtain ⟨-, hk, h⟩ := h
  have hs := shared_lt hpre
  simp only [AtPos, finVal, LaneW] at h
  obtain ⟨⟨h316, h317, h318⟩, hf, h583, h2308, h637⟩ := h
  have hup := second_lt hf
  obtain ⟨i1, i2, i3, i4⟩ := pairIx_words (g := g) (u := u) (by omega)
  obtain ⟨q1, q2, q3, q4, q5⟩ := pair_words (g := g) (r := u + 3) (by omega)
  have h2101 : w 2101 = W (pairIx g u) := hf.2
  simp only [after_store_7, h2101, h318, h317, i3, q1, q2, q4]
  refine ex_of_eq (tail_588_at (b := ?_) h2308 ?_ ?_) ?_
  rotate_left 1
  · rfl
  · have := slot0_lt (g := g) (u := u + 3) (by omega)
    omega
  refine ⟨.ld 8 u, ⟨rfl, ?_, ?_⟩, rfl, by ld_fin, nofun⟩
  · keep hk
  · simp only [AtPos, finVal, LaneW]
    exact ⟨⟨h316, h317, h318⟩, hf, rfl, rfl, rfl, h583, h2308,
      congrArg (sptr g) (rd_norm P _)⟩

theorem st_st_8 (hpre : Pre P L mem0) (hg : g < L.threads) {u : Nat}
    (h : RefAt P g (.st 8 u) ⟨.store 8, w, p, x⟩) :
    ∃ d', after_store_8 L g ⟨.store 8, w, p, x⟩ = some (some d') ∧
      Succ P g (.st 8 u) led0 d' := by
  obtain ⟨-, hk, h⟩ := h
  have hs := shared_lt hpre
  simp only [AtPos, finVal, LaneW] at h
  obtain ⟨⟨h316, h317, h318⟩, hf, h638, h646, h583, h2308, h651⟩ := h
  have hup := second_lt hf
  obtain ⟨q1, q2, q3, q4, q5⟩ := pair_words (g := g) (r := u + 3) (by omega)
  simp only [after_store_8, h638, h646, h316, q3, q5]
  refine ex_of_eq (tail_605_at (b := ?_) h2308 ?_ ?_) ?_
  rotate_left 1
  · rfl
  · have := slot0_lt (g := g) (u := u + 3) (by omega)
    omega
  refine ⟨.ld 9 u, ⟨rfl, ?_, ?_⟩, rfl, by ld_fin, nofun⟩
  · keep hk
  · simp only [AtPos, finVal, LaneW]
    exact ⟨⟨h316, h317, h318⟩, hf, rfl, h583, congrArg (sptr g) (rd_norm P _)⟩

set_option maxRecDepth 8000 in
theorem st_st_9 (hpre : Pre P L mem0) (hg : g < L.threads) {u : Nat}
    (h : RefAt P g (.st 9 u) ⟨.store 9, w, p, x⟩) :
    ∃ d', after_store_9 L g ⟨.store 9, w, p, x⟩ = some (some d') ∧
      Succ P g (.st 9 u) led0 d' := by
  obtain ⟨-, hk, h⟩ := h
  have hs := shared_lt hpre
  simp only [AtPos, finVal, LaneW] at h
  obtain ⟨⟨h316, h317, h318⟩, hf, h659⟩ := h
  have hup := second_lt hf
  obtain ⟨⟨m, hm, hum⟩, h2101'⟩ := hf
  have h2101 : w 2101 = W (pairIx g u) := h2101'
  obtain ⟨i1, i2, i3, i4⟩ := pairIx_words (g := g) (u := u) (by omega)
  have t1 := second_test (g := g) (u := u) (by omega)
  have hiff := second_iff hm hum
  have eS := sharedWord hpre
  have eZ := zext_W (a := P.sharedBase) (by omega)
  have h307 : w 307 = W (tid g) := hk.base.tid
  by_cases hlt : m < 9
  · have t1' := t1.trans (decide_eq_true (hiff.mpr hlt))
    have hup4 : u + 4 < pairs g := by unfold pairs; omega
    obtain ⟨q1, q2, q3, q4, q5⟩ := pair_words hup4
    simp only [after_store_9, h2101, h318, h317, i4, t1', ↓reduceIte, q1, q2, q4, eS, eZ]
    refine ex_of_eq (tail_467_at (a := ?_) (b := ?_) hpre hg ?_ ?_ ?_) ?_
    rotate_left 2
    · rfl
    · rfl
    · have := slot0_lt hup4
      omega
    refine ⟨.ld 2 (u + 4), ⟨rfl, ?_, ?_⟩, rfl, by ld_fin, nofun⟩
    · keep hk
    · simp only [AtPos, finVal, LaneW, Second]
      exact ⟨⟨h316, h317, h318⟩, ⟨⟨m + 1, by omega, by omega⟩, rfl⟩, rfl, rfl, rfl, rfl,
        congrArg (sptr g) (rd_norm P _)⟩
  · have t1' := t1.trans (decide_eq_false (fun h => hlt (hiff.mp h)))
    simp only [after_store_9, h2101, h307, t1', Bool.false_eq_true, ↓reduceIte, tid_gt127 g]
    refine ⟨_, rfl, .bar 0, ⟨rfl, ?_, ?_⟩, rfl, ?_, nofun⟩
    · keep hk
    · simp only [AtPos]
      exact ⟨h317, rfl⟩
    · simp only [done, elemIx, qOf, finVal, getLit, pairs]
      omega

/-! ### The two `bar.sync 0` -/

theorem st_bar_0 (h : RefAt P g (.bar 0) ⟨.bar 3, w, p, x⟩) :
    Succ P g (.bar 0) ledBar (after_bar_3 L g ⟨.bar 3, w, p, x⟩) := by
  obtain ⟨-, hk, h⟩ := h
  refine ⟨.bar 1, ⟨rfl, ?_, h⟩, rfl, rfl, nofun⟩
  keep hk

/-- A run of moves from one register is no fault when the register holds a 4-byte value. -/
theorem mov_cond {s : Nat} : ∀ (ds : List Nat) (V : Nat → Value), s ∉ ds → (V s).bytes = 4 →
    xCond V (ds.map fun d => XItem.base (.mov d s))
  | [], _, _, _ => trivial
  | d :: ds, V, hs, hV => by
    refine ⟨hV, mov_cond ds _ (fun h => hs (List.mem_cons_of_mem _ h)) ?_⟩
    have hd : s ≠ d := fun h => hs (h ▸ List.mem_cons_self ..)
    simp [XItem.upd, XItem.vals, OItem.vals, Function.update, hd, hV]

/-- **The clearing of the 128 carry registers** (`mov.b32 %r1812, 0f00000000` and the 127
moves of the instructions 633 to 759) is no fault. -/
theorem r633_ok {V : Nat → Value} (h : (V 2118).bytes = 4) : Run.r633_cond V := by
  refine ⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact mov_cond (List.range' 2119 16) _ (by decide) h
  · exact mov_cond (List.range' 2135 16) _ (by decide) h
  · exact mov_cond (List.range' 2151 16) _ (by decide) h
  · exact mov_cond (List.range' 2167 16) _ (by decide) h
  · exact mov_cond (List.range' 2183 16) _ (by decide) h
  · exact mov_cond (List.range' 2199 16) _ (by decide) h
  · exact mov_cond (List.range' 2215 16) _ (by decide) h
  · exact mov_cond (List.range' 2231 15) _ (by decide) h

/-- The slots after the local code of the instructions 630 to 759: the pointer of
`cvta.shared.u64`, the base pointer of the carry loads, the cleared carry registers. -/
def clearX (site : Site) (g a b : Nat) (w : Nat → BitVec 64) (p : Nat → Bool)
    (x : Nat → Value) : Nat → Value :=
  let x3 := valueEx (valueEx (valueEx x [(2358, sptr g a)]) [(2250, sptr g (a + b))])
    [(2118, .bits 32 (BitVec.ofNat 64 0))]
  valueEx x3 (Run.r633_facts8 (valueOf ⟨site, w, p, x3⟩))

/-- The base pointer of the carry loads survives the clearing of the carry registers. -/
theorem clearX_base (site : Site) (g a b : Nat) (w : Nat → BitVec 64) (p : Nat → Bool)
    (x : Nat → Value) : clearX site g a b w p x 2250 = sptr g (a + b) := rfl

/-- The pointer run of the first carry load (instructions 761 to 764). -/
theorem tail_761_at (hx : x 2250 = sptr g a) (ha : a + 32768 < 2 ^ 32) :
    tail_761 L g ⟨site, w, p, x⟩ =
      some (some ⟨.load 31, w, p, valueEx x [(2362, sptr g (swzN (a + 32768)))]⟩) := by
  have hV : valueOf ⟨site, w, p, x⟩ 2250 = sptr g a := by rw [valueOf_opaque rfl]; exact hx
  obtain ⟨hc, hf⟩ := const_run 32768 (fun h1 h2 => r761_ptr h1 h2) hV ha
  rw [tail_761, across_pos hc, hf]

/-- The clearing run (instructions 632 to 759), then the branch on `%p30`. -/
theorem tail_632_at :
    tail_632 L g ⟨site, w, p, x⟩ =
      tail_760 L g ⟨site, w, p, valueEx (valueEx x [(2118, .bits 32 (BitVec.ofNat 64 0))])
        (Run.r633_facts8 (valueOf ⟨site, w, p,
          valueEx x [(2118, .bits 32 (BitVec.ofNat 64 0))]⟩))⟩ := by
  have hc : Run.r633_cond (valueOf ⟨site, w, p,
      valueEx x [(2118, .bits 32 (BitVec.ofNat 64 0))]⟩) :=
    r633_ok (by rw [valueOf_opaque rfl]; rfl)
  rw [tail_632, tail_633, under_pos hc]

/-- The move of the pointer `%rd112` by the word `%rd110` (instruction 631). -/
theorem tail_631_at (hx : x 2358 = sptr g a) (hw : w 2356 = W b) (hab : a + b < 2 ^ 32) :
    tail_631 L g ⟨site, w, p, x⟩ =
      tail_632 L g ⟨site, w, p, valueEx x [(2250, sptr g (a + b))]⟩ := by
  have hV : valueOf ⟨site, w, p, x⟩ 2358 = sptr g a := by rw [valueOf_opaque rfl]; exact hx
  have hW : valueOf ⟨site, w, p, x⟩ 2356 = .bits 64 (W b) := by
    have hk : kind 2356 = .word 64 := rfl
    simp only [valueOf, hk, hw]
  obtain ⟨e1, m1⟩ := movedBy_W (a := a) (b := b) (by omega) hab
  obtain ⟨hc, hf⟩ := r631_ptr hV hW m1
  rw [e1] at hf
  rw [tail_631, under_pos hc, hf]
  rfl

/-- **The local code after the second `bar.sync 0`**, from the cut point at the
`cvta.shared.u64` (instruction 630): the base pointer `%rd4` at address `a + b` (the shared
base `a` in the word register `%rd111`, the offset `b` in `%rd110`), the clearing run, the
branch on "no compute thread" (`%p30`), and for a compute thread the address of the first
carry load. -/
theorem tail_630_at (hpre : Pre P L mem0) (hg : g < L.threads) (hs : w 2357 = W a)
    (hw : w 2356 = W b) (hab : a + b + 32768 < 2 ^ 32) :
    tail_630 L g ⟨site, w, p, x⟩ = some (some (if p 30 = true
      then ⟨.fenceProxy 1, w, p, clearX site g a b w p x⟩
      else ⟨.load 31, w, p,
        valueEx (clearX site g a b w p x) [(2362, sptr g (swzN (a + b + 32768)))]⟩)) := by
  have hV : valueOf ⟨site, w, p, x⟩ 2357 = .bits 64 (W a) := by
    have hk : kind 2357 = .word 64 := rfl
    simp only [valueOf, hk, hs]
  obtain ⟨hc, hv⟩ := cvta_shared hpre hg hV (by omega)
  rw [tail_630, under_pos hc, hv]
  refine (tail_631_at (a := a) (b := b) rfl hw (by omega)).trans (tail_632_at.trans ?_)
  show tail_760 L g ⟨site, w, p, clearX site g a b w p x⟩ = _
  by_cases hp : p 30 = true
  · simp only [tail_760, hp, ↓reduceIte]
  · simp only [tail_760, hp, Bool.false_eq_true, ↓reduceIte]
    exact tail_761_at (clearX_base site g a b w p x) hab

theorem st_bar_1 (hpre : Pre P L mem0) (hg : g < L.threads)
    (h : RefAt P g (.bar 1) ⟨.bar 4, w, p, x⟩) :
    ∃ d', after_bar_4 L g ⟨.bar 4, w, p, x⟩ = some (some d') ∧ Exit P g d' := by
  obtain ⟨-, hk, h⟩ := h
  have hs := shared_lt hpre
  simp only [AtPos] at h
  obtain ⟨h317, h30⟩ := h
  have h307 : w 307 = W (tid g) := hk.base.tid
  have h308 : w 308 = W (warp g) := hk.base.warp
  have eS := sharedWord hpre
  have eZ := zext_W (a := P.sharedBase) (by omega)
  have hw := warp_lt g
  have hl := lane_lt g
  simp only [after_bar_4, h307, h308, h317, carry_word g, carry_quad g, eS, eZ]
  refine ex_of_eq (tail_630_at (a := ?_) (b := ?_) hpre hg ?_ ?_ ?_) ?_
  rotate_left 2
  · rfl
  · rfl
  · omega
  by_cases hc : tid g < 128
  · have hp : p 30 = false := by rw [h30]; exact decide_eq_false (by omega)
    have hp' : setP ([] : List (Nat × Bool)) p 30 = false := hp
    simp only [hp, Bool.false_eq_true, ↓reduceIte]
    refine ⟨?_, ?_, fun _ => rfl, fun _ => rfl⟩
    · keep hk
    · simp only [hc, ↓reduceIte]
  · have hp : p 30 = true := by rw [h30]; exact decide_eq_true (by omega)
    simp only [hp, ↓reduceIte]
    refine ⟨?_, ?_, fun h => absurd h hc, fun h => absurd h hc⟩
    · keep hk
    · simp only [hc, ↓reduceIte]

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Conversion
