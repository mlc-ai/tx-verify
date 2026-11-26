-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashKdaFwd.Proof.Ref.Store.Arith

@[expose] public section

/-! # Store phase: the reference invariant is kept

One lemma per site (`st_<position>`): from the invariant at the site (`RefAt`), the state that
the generated transition function gives is at a position of the phase with its invariant, the
ledger of that position is the ledger of the site plus what the site's event counts, and the
position is a successor position of the site's (`Succ`, with the explicit successor relation
`Step` of the positions); or it is the exit of the phase with the exit ledger (`Done`).

The transition functions of the phase share three pieces of local code, each with a lemma of
its own: the head of the tile loop (`head_at`: the role check and the address of the "store
full" mbarrier), the start of a chunk row of a partial tile (`tail_2997_at`: the shared and
global addresses of the row) and the role check before the bulk-group wait (`role66`).

Every proof first rewrites the branch conditions of the transition function to `true` or
`false` (from the closed forms of the registers they read), so that the `if`s are gone before
the register file is read (`file_simp` of `Ref/Lib.lean`); the registers of the successor are
then normalized from the code's 32-bit and 64-bit operations to words of numbers (`wn`), and
equalities of words are closed by `omega` on the numbers (`wfin`). -/

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

/-! ### What an event adds to the ledger -/

/-- Nothing counted. -/
def dZero : Led := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
/-- A `bar.sync 0`. -/
def dBar : Led := ⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
/-- A successful poll of the "store full" mbarrier of stage `o`. -/
def dPoll (o : Nat) : Led :=
  ⟨0, 0, if o = 0 then 1 else 0, if o = 0 then 0 else 1, 0, 0, 0, 0, 0, 0⟩
/-- An arrival on the "store empty" mbarrier of stage `o`. -/
def dArr (o : Nat) : Led :=
  ⟨0, 0, 0, 0, if o = 0 then 1 else 0, if o = 0 then 0 else 1, 0, 0, 0, 0⟩
/-- A tensor store, a bulk-group commit, a bulk-group wait, a global write. -/
def dTs : Led := ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩
def dCommit : Led := ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩
def dWait : Led := ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩
def dGst : Led := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩

/-- **The successor relation of the positions** of a thread whose sequence has `len` tokens:
which position can follow which. After the entry, the poll of tile 0; a poll is repeated
(`retry`: it failed) or followed by the first tensor store of a full tile or by the vector load
of chunk 0 of row 0 of a partial tile; the sixteen tensor stores, the commit and the group
wait; the four element reads and the eight global stores of a chunk, then the next chunk of
the row, the next row, or (after the last live row) the group wait; the arrival; the poll of
the next tile. The exit of the phase is not a position (`Done`). -/
inductive Step (len : Nat) : Pos → Pos → Prop
  | entry : Step len .entry (.wait 0)
  | retry (t : Nat) : Step len (.wait t) (.wait t)
  | full (t : Nat) (h : 16 * t + 16 ≤ len) : Step len (.wait t) (.ts t 0)
  | part (t : Nat) (h : len < 16 * t + 16) : Step len (.wait t) (.ld0 t 0 0)
  | ts (t : Nat) (i i' : Fin 16) (h : i'.val = i.val + 1) : Step len (.ts t i) (.ts t i')
  | commit (t : Nat) : Step len (.ts t 15) (.commit t)
  | cwait (t : Nat) (h : 16 * t + 16 ≤ len) : Step len (.commit t) (.bwait t)
  | ld0 (t row c : Nat) (v : Value) : Step len (.ld0 t row c) (.ld1 t row c v)
  | ld1 (t row c : Nat) (v0 v : Value) : Step len (.ld1 t row c v0) (.ld2 t row c v0 v)
  | ld2 (t row c : Nat) (v0 v1 v : Value) :
    Step len (.ld2 t row c v0 v1) (.ld3 t row c v0 v1 v)
  | ld3 (t row c : Nat) (v0 v1 v2 : Value) : Step len (.ld3 t row c v0 v1 v2) (.gst t row c 0)
  | gst (t row c : Nat) (j j' : Fin 8) (h : j'.val = j.val + 1) :
    Step len (.gst t row c j) (.gst t row c j')
  | chunk (t row c : Nat) (h : c + 1 < 16) : Step len (.gst t row c 7) (.ld0 t row (c + 1))
  | row (t row c : Nat) (hc : c + 1 = 16) (h : row + 1 < len - 16 * t) :
    Step len (.gst t row c 7) (.ld0 t (row + 1) 0)
  | last (t row c : Nat) (hc : c + 1 = 16) (h : row + 1 = len - 16 * t)
    (hp : len < 16 * t + 16) : Step len (.gst t row c 7) (.bwait t)
  | bwait (t : Nat) : Step len (.bwait t) (.arrive t)
  | next (t : Nat) (h : t + 1 < tiles len) : Step len (.arrive t) (.wait (t + 1))

/-- **A successor inside the phase**: the state `d'` is at a position with its invariant, that
position's ledger is the ledger of `pos` plus `δ`, and it is a successor position of `pos`. -/
def Succ (P : Params) (g : Nat) (pos : Pos) (δ : Led) (d' : D) : Prop :=
  ∃ pos', RefAt P g pos' d' ∧
    led (P.length (seqOf P g)) pos' = led (P.length (seqOf P g)) pos + δ ∧
    Step (P.length (seqOf P g)) pos pos'

/-- **The exit as a successor**: the state `d'` is the exit state, and the exit ledger is the
ledger of `pos` plus `δ`. -/
def Done (P : Params) (g : Nat) (pos : Pos) (δ : Led) (d' : D) : Prop :=
  Exit P g d' ∧ ledExit P g = led (P.length (seqOf P g)) pos + δ

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
  {w : Nat → BitVec 64} {p : Nat → Bool} {x : Nat → Value}

theorem Keep.of_w {d d' : D} (hk : Keep P g d) (h1 : d'.w 307 = d.w 307)
    (h2 : d'.w 314 = d.w 314) (h3 : d'.w 315 = d.w 315) (h4 : d'.w 352 = d.w 352)
    (h5 : d'.w 486 = d.w 486) (h6 : d'.w 2248 = d.w 2248) : Keep P g d' :=
  ⟨hk.store, h1.trans hk.tid, h2.trans hk.len, h3.trans hk.tiles, h4.trans hk.rank,
    h5.trans hk.elected, h6.trans hk.first⟩

/-- `wn [lemmas]`: normalize the code's operations on words of numbers (`w32_norm` with the
words of `Arith.lean`). -/
syntax "wn" (" [" Lean.Parser.Tactic.simpLemma,* "]")? (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| wn $[$loc]?) => `(tactic| wn [] $[$loc]?)
  | `(tactic| wn [$ls,*] $[$loc]?) => `(tactic|
      w32_norm [shl3_W, shl4_W, shl12_W, max32_W, low32_W, r64_W, zext_W, sext_W, add64_W,
        addi64_W, shl64_8, mulWide_256, addi_neg16, xor_bit, Nat.mul_zero, Nat.mul_one,
        Nat.zero_mod, $ls,*] $[$loc]?)

/-- `wfin`: close an equality of words by `omega` on the numbers, or a closed fact. -/
macro "wfin" : tactic => `(tactic| first
  | with_reducible rfl | with_reducible assumption | omega | (apply congrArg W; omega)
  | decide)

/-- `keep_of hk [lemmas]`: the inherited registers are not written. -/
syntax "keep_of " term:max " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| keep_of $hk [$ls,*]) => `(tactic| (
      refine Keep.of_w $hk ?_ ?_ ?_ ?_ ?_ ?_ <;>
        first | rfl | (file_simp [Bool.false_eq_true, ↓reduceIte, $ls,*]; done)))

/-! ### The role of the thread -/

theorem role_eq : scmpi .eq .b (i32 2) 2 = true := by decide
theorem role_gt : scmpi .gt .u (i32 2) 1 = true := by decide

/-- A thread of the store warp is no compute thread and no load thread. -/
theorem role63 (hpre : Pre P L mem0) (h : warp g = 5) :
    scmpi .lt .u (sreg ((L.tidOf g).get .x)) 128 = false ∧
    scmpi .lt .u (sreg ((L.tidOf g).get .x)) 160 = false ∧
    scmpi .gt .u (sreg ((L.tidOf g).get .x)) 127 = true := by
  have ht := (warp_eq5_iff g).mp h
  have hlt := tid_lt g
  rw [tidWord hpre, tid_lt128, tid_lt160, scmpi_gt_u_W (by omega) (by decide) (by decide)]
  refine ⟨?_, ?_, ?_⟩ <;> simp <;> omega

/-- The lengths of the thread's sequence and what the precondition bounds. -/
theorem len_facts (hpre : Pre P L mem0) (g : Nat) :
    firstToken P.length (seqOf P g) + P.length (seqOf P g) + 15 < 2 ^ 31 ∧
      tiles (P.length (seqOf P g)) * 16 < P.length (seqOf P g) + 16 ∧
      P.length (seqOf P g) ≤ tiles (P.length (seqOf P g)) * 16 := by
  have h1 := tok_le hpre g
  have h2 := Startup.total_lt hpre
  unfold tiles
  omega

/-- `rd [lemmas]`: unfold a transition function and read the register file, with the branch
conditions and register facts given as `lemmas`. -/
syntax "rd" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| rd [$ls,*]) => `(tactic|
      file_simp [Bool.false_eq_true, ↓reduceIte, Arith32.sel, role_eq, role_gt, Pos.site,
        Bool.or_true, Bool.true_or, Bool.or_false, Bool.false_or, $ls,*])

/-! ### The entry: the transition of `bar_5` -/

/-- The local code from instruction 2949 leads the store leader of a nonempty sequence to the
poll of tile 0. -/
theorem tail_2949_at (hpre : Pre P L mem0) {d : D} (hk : Keep P g d) (hl : lane g = 0)
    (hlen : 1 ≤ P.length (seqOf P g)) : RefAt P g (.wait 0) (tail_2949 L g d) := by
  obtain ⟨r1, r2, -⟩ := role63 hpre hk.store
  obtain ⟨b1, b2, b3⟩ := len_facts hpre g
  have hs := shared_lt hpre
  have k314 := hk.len
  have k315 := hk.tiles
  refine ⟨?_, ?_, ?_⟩
  · rd [tail_2949, r1, r2]
  · keep_of hk [tail_2949, r1, r2, Arith32.sel, role_eq, role_gt]
  · simp only [AtPos, Tile, Mult]
    refine ⟨⟨hl, by omega, ?_⟩, ?_⟩ <;> (repeat' apply And.intro) <;>
      (rd [tail_2949, r1, r2, k314, k315, scaleOut hpre, sharedWord hpre]) <;>
      (try wn) <;> wfin

/-- **The entry**: after the fifth `bar.sync 0` the store leader of a nonempty sequence polls
for tile 0; every other thread of the store warp is at the exit. -/
theorem st_entry (hpre : Pre P L mem0) (h : RefAt P g .entry ⟨.bar 5, w, p, x⟩) :
    Succ P g .entry dBar (after_bar_5 L g ⟨.bar 5, w, p, x⟩) ∨
      Done P g .entry dBar (after_bar_5 L g ⟨.bar 5, w, p, x⟩) := by
  obtain ⟨-, hk, -⟩ := h
  have hw := hk.store
  have k307 : w 307 = W (tid g) := hk.tid
  have k314 : w 314 = W (P.length (seqOf P g)) := hk.len
  have k486 : w 486 = W (if lane g = 0 then 1 else 0) := hk.elected
  obtain ⟨r1, r2, r3⟩ := role63 hpre hw
  obtain ⟨b1, b2, b3⟩ := len_facts hpre g
  have c31 : scmpi .ne .b (andi (w 307) 224) 128 = true := by
    rw [k307, tid_and224]
    simp [hw]
  have c53 : scmpi .lt .s (w 314) 1 = decide (P.length (seqOf P g) < 1) := by
    rw [k314]
    wn
  have hexit : ∀ c52 c53' : Bool, (c52 || c53') = true →
      scmpi .eq .b (w 486) 0 = c52 → scmpi .lt .s (w 314) 1 = c53' →
      ¬ (lane g = 0 ∧ 1 ≤ P.length (seqOf P g)) →
      Done P g .entry dBar (after_bar_5 L g ⟨.bar 5, w, p, x⟩) := by
    intro c52 c53' hor h52 h53 hno
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · rd [after_bar_5, c31, r1, r2, h52, h53, hor]
    · keep_of hk [after_bar_5, c31, r1, r2, h52, h53, hor, Arith32.sel, role_eq,
        Bool.true_or]
    · rd [after_bar_5, c31, r1, r2, h52, h53, hor]
      exact tidWord hpre
    · rd [after_bar_5, c31, r1, r2, h52, h53, hor, r3]
    · simp [ledExit, led, ledEntry, dBar, Led.add_def, hno]
  by_cases hl : lane g = 0
  · have c52 : scmpi .eq .b (w 486) 0 = false := by
      rw [k486]
      simp only [hl, ↓reduceIte]
      decide
    by_cases hlen : P.length (seqOf P g) < 1
    · exact .inr (hexit false true rfl c52 (by rw [c53]; simp [hlen]) (by omega))
    · have c53' : scmpi .lt .s (w 314) 1 = false := by
        rw [c53]
        simp [hlen]
      have e : after_bar_5 L g ⟨.bar 5, w, p, x⟩ = tail_2949 L g ⟨.bar 5, w, p, x⟩ := by
        rd [after_bar_5, c31, r1, r2, c52, c53']
      rw [e]
      exact .inl ⟨.wait 0, tail_2949_at hpre hk hl (by omega),
        (by simp [led, ledEntry, dBar, Led.add_def]), Step.entry⟩
  · have c52 : scmpi .eq .b (w 486) 0 = true := by
      rw [k486]
      simp only [hl, ↓reduceIte]
      decide
    exact .inr (hexit true (scmpi .lt .s (w 314) 1) (by simp) c52 rfl (by tauto))

/-! ### The poll and the start of a row -/

/-- The address `%rd1168` of an output row, from the words of its parts: the output pointer,
`256 * head`, and the product of the number of heads with the token `b`. -/
theorem rowAddr (hpre : Pre P L mem0) (hg : g < L.threads) {b tok : Nat}
    (hb : b = firstToken P.length (seqOf P g) + tok) (htok : tok < P.length (seqOf P g)) :
    addi64 (add64 (W (256 * headOf P g + P.outputBase))
      (shl64 (mul64 (W P.heads) (W b)) 8)) 8 =
    W (P.outputBase + 256 * ((firstToken P.length (seqOf P g) + tok) * P.heads + headOf P g)
      + 16 * 0 + 8) := by
  subst hb
  have h1 := tok_le hpre g
  have h2 := Startup.total_lt hpre
  have hh := headOf_lt hpre hg
  have hH := hpre.headsLt
  have ho := out_le hpre (tok := firstToken P.length (seqOf P g) + tok) (h := headOf P g)
    (by omega) hh
  have e1 : mul64 (W P.heads) (W (firstToken P.length (seqOf P g) + tok)) =
      W ((firstToken P.length (seqOf P g) + tok) * P.heads) := by
    rw [mul64_W (by rw [Nat.mul_comm]; omega) (by omega) (by omega), Nat.mul_comm]
  have h8 : (8 : Int).toNat = 8 := rfl
  rw [e1, shl64_8 (by omega), add64_W (by omega), addi64_W (by decide) (by omega)]
  apply congrArg W
  omega

/-- **The start of a chunk row**: the local code from instruction 2997 leads the store leader
to the vector load of chunk 0 of row `row` of the partial tile `t`. -/
theorem tail_2997_at (hpre : Pre P L mem0) (hg : g < L.threads) {d : D} {t row : Nat}
    (hk : Keep P g d) (hT : Tile P g t d) (hpart : P.length (seqOf P g) < 16 * t + 16)
    (hrow : row < P.length (seqOf P g) - 16 * t) (h2115 : d.w 2115 = W row) :
    RefAt P g (.ld0 t row 0) (tail_2997 L g d) := by
  have hT' := hT
  simp only [Tile, Mult] at hT'
  obtain ⟨b1, b2, b3⟩ := len_facts hpre g
  have hs := shared_lt hpre
  have k2248 := hk.first
  have hh := headOf_lt hpre hg
  have hH := hpre.headsLt
  have h1 := tok_le hpre g
  have ho := out_le hpre (tok := firstToken P.length (seqOf P g) + (16 * t + row))
    (h := headOf P g) (by omega) hh
  refine ⟨?_, ?_, ?_⟩
  · rd [tail_2997]
  · keep_of hk [tail_2997]
  · simp only [AtPos, Tile, Mult, Row]
    refine ⟨?_, hpart, hrow, by omega, ?_, ?_, ?_, ?_⟩
    · refine ⟨hT'.1, hT'.2.1, ?_⟩
      (repeat' apply And.intro) <;> rd [tail_2997, hT']
    · rd [tail_2997, h2115]
    · rd [tail_2997, h2115, hT', sharedWord hpre]
      wn
      try wfin
    · rd [tail_2997]
      wn
      try wfin
    · rd [tail_2997, h2115, hT', k2248, ctaidY hpre hg, outWord hpre, Startup.headsWord hpre]
      wn
      rw [rowAddr hpre hg (tok := 16 * t + row) (by omega) (by omega)]

/-- `pos_facts [unfold] [facts]`: the register facts of the successor position. One `rd` call
unfolds the transition function (with the decided branch conditions and the facts that are not
about registers, `unfold`) and reads the file for all facts at once; then the facts of the old
position and the launch words (`facts`) are rewritten, the words normalized, and what is left
is closed fact by fact. -/
syntax "pos_facts" " [" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]" :
  tactic
macro_rules
  | `(tactic| pos_facts [$us,*] [$fs,*]) => `(tactic| (
      simp only [AtPos, Tile, Mult, Row, tsSrc, finVal, getLit]
      rd [$us,*]
      (try simp only [and_self, and_true, true_and, $fs,*])
      (try wn)
      (try simp only [and_self, and_true, true_and])
      (try ((repeat' apply And.intro) <;> wfin))))

/-- `tile_of hT`: the registers of the tile loop are not written (the goal is `Tile` of a state
whose file is the file of `hT` with other registers rewritten). -/
syntax "tile_of " term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| tile_of $hT) => `(tactic| tile_of $hT [])
  | `(tactic| tile_of $hT [$ls,*]) => `(tactic| (
      have hTile := $hT
      simp only [Tile, Mult] at hTile ⊢
      (try rd [$ls,*])
      exact hTile))

/-- The ledger equation of a step, after a case split on the stage of the tile. -/
syntax "led_of " term:max (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| led_of $t) => `(tactic| led_of $t [])
  | `(tactic| led_of $t [$ls,*]) => `(tactic| (
      rcases Nat.mod_two_eq_zero_or_one $t with h2 | h2 <;>
        simp [led, ledIn, ledEntry, ledExit, dZero, dBar, dPoll, dArr, dTs, dCommit, dWait,
          dGst, Led.add_def, h2, $ls,*] <;> omega))

/-- **The poll of a tile**: a failed poll is repeated; after a successful one the leader issues
the first tensor store of a full tile, or starts row 0 of a partial tile. -/
theorem st_wait (hpre : Pre P L mem0) (hg : g < L.threads) (t : Nat) (ok : Bool)
    (h : RefAt P g (.wait t) ⟨.mbarWait 9, w, p, x⟩) :
    Succ P g (.wait t) (if ok then dPoll (t % 2) else dZero)
      (after_mbarWait_9 L g ⟨.mbarWait 9, w, p, x⟩ ok) := by
  obtain ⟨-, hk, hp⟩ := h
  have hp' := hp
  simp only [AtPos, Tile, Mult] at hp'
  obtain ⟨⟨hl, ht, k326, k2111, k2112, k2113, k2114, hM⟩, k1074, k1076⟩ := hp'
  obtain ⟨b1, b2, b3⟩ := len_facts hpre g
  have hs := shared_lt hpre
  have k314 : w 314 = W (P.length (seqOf P g)) := hk.len
  have k2248 : w 2248 = W (firstToken P.length (seqOf P g)) := hk.first
  cases ok with
  | false =>
    have e : after_mbarWait_9 L g ⟨.mbarWait 9, w, p, x⟩ false = ⟨.mbarWait 9, w, p, x⟩ := by
      rd [after_mbarWait_9]
    rw [e]
    exact ⟨.wait t, ⟨rfl, hk, hp⟩, (by simp [led, dZero, Led.add_def]), Step.retry t⟩
  | true =>
    have c59 : scmpi .gt .s (sub32 (w 314) (shl (w 2112) 4)) 15 =
        decide (15 < P.length (seqOf P g) - 16 * t) := by
      rw [k314, k2112]
      wn
    have c60 : scmpi .lt .s (sub32 (w 314) (shl (w 2112) 4)) 1 = false := by
      rw [k314, k2112]
      wn
      simp
      omega
    by_cases hfull : 16 * t + 16 ≤ P.length (seqOf P g)
    · have c59' : scmpi .gt .s (sub32 (w 314) (shl (w 2112) 4)) 15 = true := by
        rw [c59]
        simp
        omega
      refine ⟨.ts t 0, ⟨?_, ?_, ?_⟩, (by led_of t), Step.full t hfull⟩
      · ref_site [after_mbarWait_9, c59']
      · keep_of hk [after_mbarWait_9, c59']
      · pos_facts [after_mbarWait_9, c59', hl, ht, hfull]
          [k326, k2111, k2112, k2113, k2114, hM, k1076, k314, k2248, sharedWord hpre,
            ctaidY hpre hg]
    · have c59' : scmpi .gt .s (sub32 (w 314) (shl (w 2112) 4)) 15 = false := by
        rw [c59]
        simp
        omega
      have e : after_mbarWait_9 L g ⟨.mbarWait 9, w, p, x⟩ true =
          tail_2997 L g ⟨.mbarWait 9, setW [(2115, i32 0)] w, p, x⟩ := by
        rd [after_mbarWait_9, c59', c60]
      rw [e]
      refine ⟨.ld0 t 0 0, tail_2997_at hpre hg (t := t) (row := 0) ?_ ?_ (by omega) (by omega)
        ?_, (by led_of t), Step.part t (by omega)⟩
      · keep_of hk []
      · tile_of hp.1
      · rfl

/-! ### The commit, the group wait and the arrival -/

/-- The role check before the bulk-group wait (instructions 3084 to 3092) is passed. -/
theorem role66 (hpre : Pre P L mem0) (h : warp g = 5) :
    scmpi .gt .u (sel (scmpi .lt .u (sreg ((L.tidOf g).get .x)) 128) (i32 1)
      (sel (scmpi .eq .b (sel (scmpi .lt .u (sreg ((L.tidOf g).get .x)) 128) (i32 0)
        (sel (scmpi .lt .u (sreg ((L.tidOf g).get .x)) 160) (i32 1) (i32 2))) 2) (i32 2)
        (i32 0))) 1 = true := by
  obtain ⟨r1, r2, -⟩ := role63 hpre h
  simp only [r1, r2, Arith32.sel, Bool.false_eq_true, ↓reduceIte, role_eq, role_gt]

theorem st_commit (hpre : Pre P L mem0) (t : Nat)
    (h : RefAt P g (.commit t) ⟨.bulkCommit 0, w, p, x⟩) :
    Succ P g (.commit t) dCommit (after_bulkCommit_0 L g ⟨.bulkCommit 0, w, p, x⟩) := by
  obtain ⟨-, hk, hp⟩ := h
  have hfull : 16 * t + 16 ≤ P.length (seqOf P g) := hp.2
  refine ⟨.bwait t, ⟨rfl, Keep.of_w hk rfl rfl rfl rfl rfl rfl, ⟨by tile_of hp.1, ?_⟩⟩,
    (by led_of t [hfull]), Step.cwait t hfull⟩
  rd [after_bulkCommit_0]
  exact role66 hpre hk.store

/-- **The bulk-group wait**: the leader maps the address of the "store empty" mbarrier of the
stage (`mapa` with rank 0: its own block) and is at the arrival. -/
theorem st_bwait (hpre : Pre P L mem0) (hg : g < L.threads) (t : Nat)
    (h : RefAt P g (.bwait t) ⟨.bulkWait 0, w, p, x⟩) :
    ∃ d', after_bulkWait_0 L g ⟨.bulkWait 0, w, p, x⟩ = some (some d') ∧
      Succ P g (.bwait t) dWait d' := by
  obtain ⟨-, hk, hp⟩ := h
  have hp' := hp
  simp only [AtPos, Tile, Mult] at hp'
  obtain ⟨⟨hl, ht, k326, k2111, k2112, k2113, k2114, hM⟩, k66⟩ := hp'
  have hs := shared_lt hpre
  have k352 : w 352 = W 0 := hk.rank
  have a1 : addi (add32 (sreg L.sharedBase) (shl (w 2114) 3)) 98368 =
      W (P.sharedBase + 8 * (t % 2) + 98368) := by
    rw [sharedWord hpre, k2114]
    wn
  have e : after_bulkWait_0 L g ⟨.bulkWait 0, w, p, x⟩ = some (some ⟨.mbarArrive 6,
      setW [(1137, W (P.sharedBase + 8 * (t % 2) + 98368))] w, p,
      valueEx x [(3436, mapaVal L g ⟨.shared, g / L.block,
        P.sharedBase + 8 * (t % 2) + 98368⟩)]⟩) := by
    rd [after_bulkWait_0, tail_3100, k66, a1, k352, mapaThen,
      mapaPeer_own hpre hg (a := P.sharedBase + 8 * (t % 2) + 98368) (by omega)]
  refine ⟨_, e, .arrive t, ⟨rfl, Keep.of_w hk rfl rfl rfl rfl rfl rfl, ⟨by tile_of hp.1, ?_⟩⟩,
    ?_, Step.bwait t⟩
  · rd [mapaVal, block_div hpre]
  · by_cases hfull : 16 * t + 16 ≤ P.length (seqOf P g) <;> led_of t [hfull]

/-- **The arrival on the "store empty" mbarrier**: the leader polls for the next tile, or, after
the last tile, is at the exit. -/
theorem st_arrive (hpre : Pre P L mem0) (t : Nat)
    (h : RefAt P g (.arrive t) ⟨.mbarArrive 6, w, p, x⟩) :
    Succ P g (.arrive t) (dArr (t % 2)) (after_mbarArrive_6 L g ⟨.mbarArrive 6, w, p, x⟩) ∨
      Done P g (.arrive t) (dArr (t % 2)) (after_mbarArrive_6 L g ⟨.mbarArrive 6, w, p, x⟩) := by
  obtain ⟨-, hk, hp⟩ := h
  have hp' := hp
  simp only [AtPos, Tile, Mult] at hp'
  obtain ⟨⟨hl, ht, k326, k2111, k2112, k2113, k2114, hM⟩, -⟩ := hp'
  obtain ⟨b1, b2, b3⟩ := len_facts hpre g
  obtain ⟨r1, r2, r3⟩ := role63 hpre hk.store
  have hs := shared_lt hpre
  have c68 : scmp .ne .b (addi (w 2112) 1) (w 326) =
      decide (t + 1 ≠ tiles (P.length (seqOf P g))) := by
    rw [k2112, k326]
    wn
  have c67 : scmpi .eq .b (addi (w 2114) 1) 2 = decide (t % 2 = 1) ∧
      (w 2114 = W 0 ∨ w 2114 = W 1) := by
    rw [k2114]
    rcases Nat.mod_two_eq_zero_or_one t with h2 | h2 <;> rw [h2] <;> simp <;> decide
  by_cases hlast : t + 1 = tiles (P.length (seqOf P g))
  · right
    have c68' : scmp .ne .b (addi (w 2112) 1) (w 326) = false := by
      rw [c68]
      simp [hlast]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · ref_site [after_mbarArrive_6, c68']
    · keep_of hk [after_mbarArrive_6, c68']
    · rd [after_mbarArrive_6, c68']
      exact tidWord hpre
    · rd [after_mbarArrive_6, c68', r3]
    · have hne : 1 ≤ P.length (seqOf P g) := by omega
      by_cases hfull : 16 * t + 16 ≤ P.length (seqOf P g) <;>
        led_of t [hfull, hl, hne, ← hlast]
  · left
    have c68' : scmp .ne .b (addi (w 2112) 1) (w 326) = true := by
      rw [c68]
      simp [hlast]
    refine ⟨.wait (t + 1), ⟨?_, ?_, ?_⟩, ?_, Step.next t (by omega)⟩
    · ref_site [after_mbarArrive_6, c68', r1, r2, Arith32.sel, role_eq, role_gt]
    · keep_of hk [after_mbarArrive_6, c68', r1, r2, Arith32.sel, role_eq, role_gt]
    · rcases Nat.mod_two_eq_zero_or_one t with h2 | h2
      · have k2114' : w 2114 = W 0 := by rw [k2114, h2]
        have c67' : scmpi .eq .b (addi (w 2114) 1) 2 = false := by rw [k2114']; decide
        pos_facts [after_mbarArrive_6, c68', c67', r1, r2, hl]
          [k326, k2111, k2112, k2113, k2114', hM, sharedWord hpre]
      · have k2114' : w 2114 = W 1 := by rw [k2114, h2]
        have c67' : scmpi .eq .b (addi (w 2114) 1) 2 = true := by rw [k2114']; decide
        pos_facts [after_mbarArrive_6, c68', c67', r1, r2, hl]
          [k326, k2111, k2112, k2113, k2114', hM, sharedWord hpre]
    · by_cases hfull : 16 * t + 16 ≤ P.length (seqOf P g) <;> led_of t [hfull]

/-! ### The chunk of a row: the vector load and the eight stores -/

/-- A state with the same register file as a state of a row is in the row (the positions of a
chunk differ in the site and in the values already loaded, not in the control registers). -/
theorem row_same {s s' : Site} {p' : Nat → Bool} {x' : Nat → Value} {t row c : Nat}
    (hk : Keep P g ⟨s, w, p, x⟩) (hp : Tile P g t ⟨s, w, p, x⟩ ∧ Row P g t row c ⟨s, w, p, x⟩) :
    Keep P g ⟨s', w, p', x'⟩ ∧ Tile P g t ⟨s', w, p', x'⟩ ∧ Row P g t row c ⟨s', w, p', x'⟩ :=
  ⟨Keep.of_w hk rfl rfl rfl rfl rfl rfl, hp.1, hp.2⟩

/-- **The last store of a chunk**: the next chunk of the row, the next row, or, after the last
row of the partial tile, the bulk-group wait. -/
theorem st_gst_7 (hpre : Pre P L mem0) (hg : g < L.threads) (t row c : Nat)
    (h : RefAt P g (.gst t row c 7) ⟨.store 17, w, p, x⟩) :
    Succ P g (.gst t row c 7) dGst (after_store_17 L g ⟨.store 17, w, p, x⟩) := by
  obtain ⟨-, hk, hp⟩ := h
  have hp' := hp
  simp only [AtPos, Tile, Mult, Row] at hp'
  obtain ⟨⟨hl, ht, k326, k2111, k2112, k2113, k2114, hM⟩, hpart, hrow, hc, k2115, k2116, k2117,
    k3414⟩ := hp'
  obtain ⟨b1, b2, b3⟩ := len_facts hpre g
  have hs := shared_lt hpre
  have h1 := tok_le hpre g
  have ho := out_le hpre (tok := firstToken P.length (seqOf P g) + (16 * t + row))
    (h := headOf P g) (by omega) (headOf_lt hpre hg)
  have c61 : scmpi .ne .b (addi (w 2117) 8) 128 = decide (8 * c + 8 ≠ 128) := by
    rw [k2117]
    wn
  have c62 : scmp .eq .b (addi (w 2115) 1) (min32 (max32 (w 2111) (i32 1)) (i32 16)) =
      decide (row + 1 = min (max (P.length (seqOf P g) - 16 * t) 1) 16) := by
    rw [k2115, k2111]
    wn
  by_cases hc' : c + 1 < 16
  · have c61' : scmpi .ne .b (addi (w 2117) 8) 128 = true := by
      rw [c61]
      simp
      omega
    refine ⟨.ld0 t row (c + 1), ⟨?_, ?_, ?_⟩, (by led_of t), Step.chunk t row c hc'⟩
    · ref_site [after_store_17, c61']
    · keep_of hk [after_store_17, c61']
    · pos_facts [after_store_17, c61', hl, ht, hpart, hrow, hc']
        [k326, k2111, k2112, k2113, k2114, hM, k2115, k2116, k2117, k3414]
  · have c61' : scmpi .ne .b (addi (w 2117) 8) 128 = false := by
      rw [c61]
      simp
      omega
    by_cases hr : row + 1 = P.length (seqOf P g) - 16 * t
    · have c62' : scmp .eq .b (addi (w 2115) 1) (min32 (max32 (w 2111) (i32 1)) (i32 16)) =
          true := by
        rw [c62]
        simp
        omega
      have hnf : ¬ 16 * t + 16 ≤ P.length (seqOf P g) := by omega
      refine ⟨.bwait t, ⟨?_, ?_, ⟨by tile_of hp.1 [after_store_17, c61', c62'], ?_⟩⟩,
        (by led_of t [hnf]), Step.last t row c (by omega) hr hpart⟩
      · ref_site [after_store_17, c61', c62']
      · keep_of hk [after_store_17, c61', c62']
      · rd [after_store_17, c61', c62']
        exact role66 hpre hk.store
    · have c62' : scmp .eq .b (addi (w 2115) 1) (min32 (max32 (w 2111) (i32 1)) (i32 16)) =
          false := by
        rw [c62]
        simp
        omega
      have e : after_store_17 L g ⟨.store 17, w, p, x⟩ =
          tail_2997 L g ⟨.store 17, setW [(2115, addi (w 2115) 1)] w, p, x⟩ := by
        rd [after_store_17, c61', c62']
      rw [e]
      refine ⟨.ld0 t (row + 1) 0, tail_2997_at hpre hg (t := t) (row := row + 1) ?_ ?_ hpart
        (by omega) ?_, (by led_of t), Step.row t row c (by omega) (by omega)⟩
      · keep_of hk []
      · tile_of hp.1
      · rd [k2115]
        wn

end

end PTX.Kernels.FlashKdaFwd.Proof.Ref.Store
