-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Ledger
public import Lemmas.Flow.Counter32
public import Lemmas.Flow.Step.ShapeRegs
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The places and the closed forms of the counts

The definitions of the reference invariant's closed forms, apart from the invariant (`Ref.lean`): a
theorem about a place or a formula does not read the invariant. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (r32 i32 addi sub32 xor32 andi scmpi Scan)

noncomputable section

/-! ### Places -/

/-- A state's position: twice its program counter, plus one at a plain load's implicit wait. -/
def Site.pos (s : Site) : Nat := 2 * s.pc + match s with | .sldw _ => 1 | _ => 0

/-- The positions of a biased round and of a plain round. -/
def inBias (q : Nat) : Bool := 10064 ≤ q && q ≤ 13307
def inPlain (q : Nat) : Bool := 13322 ≤ q && q ≤ 15209

/-- Whether a site is an end state of a lane that found no tile. -/
def Site.noTile : Site → Bool
  | .wend false | .barEnd false | .exit false => true
  | _ => false

/-- Whether point `q` is passed in the current pass before a state at site `s`. -/
def before (s : Site) (q : Nat) : Bool :=
  if inBias q then inBias s.pos && decide (q < s.pos)
  else if inPlain q then inPlain s.pos && decide (q < s.pos)
  else decide (q < s.pos) && !(s.noTile && decide (6738 ≤ q) && decide (q < 15476))

/-- The points of `pts` a state at site `s` with `rb` biased and `rp` plain rounds done has
passed. -/
def passed (pts : List Nat) (s : Site) (rb rp : Nat) : Nat :=
  pts.countP (before s) + rb * pts.countP inBias + rp * pts.countP inPlain

/-- The class of the event a site fires (of a successful poll at a poll site). -/
def sig : Site → Option Cnt
  | .wq | .pwend _ | .wend _ => some (.acquire 192)
  | .ws _ => some (.acquire 80)
  | .wb _ => some (.acquire 320)
  | .barr _ => some (.arrive 336)
  | .parr _ => some (.arrive 96)
  | .parr2 _ => some (.arrive 112)
  | .bar1 | .barEnd _ => some .bar2
  | .narr _ | .finarr => some .nb
  | .bsync _ => some .sb
  | .sld _ _ => some .tcld
  | .pst _ _ => some .tcst
  | .stat _ | .fin _ => some .sst
  | _ => none

/-- The poll sites. -/
def Site.isPoll : Site → Bool
  | .wq | .ws _ | .wb _ | .pwend _ | .wend _ => true
  | _ => false

def Site.isBarr : Site → Bool
  | .barr _ => true
  | _ => false

/-! ### Sites and their successors -/

def allScan : List Scan := [.first, .loop, .second, .loop2]
def allRd : List Rd := [.first, .bias, .plain]

/-- All sites. -/
def allSites : List Site :=
  List.flatten [
    [.setmax, .bar1, .q0, .q1, .uk, .wq, .finarr], allScan.map .word, allScan.map .down,
    allScan.flatMap fun k => (List.finRange 5).map (.up k), allScan.map .total,
    [false, true].flatMap fun l => [.vote l, .pre l, .tiles l, .wend l, .barEnd l, .exit l],
    [false, true].flatMap fun b => [.wb b, .fence b, .bsync b, .barr b, .stat b],
    [false, true].flatMap fun b => (List.finRange 16).map (.bld b),
    allRd.flatMap fun r => [.ws r, .narr r, .parr r, .pws r, .pel r, .parr2 r, .pwend r],
    allRd.flatMap fun r => (List.finRange 4).flatMap fun c => [.sld r c, .pst r c],
    allRd.flatMap fun r => (List.finRange 2).map (.pwst r),
    (List.finRange 4).map .sldw, (List.finRange 2).map .fin]

set_option maxRecDepth 100000 in
theorem mem_allSites (s : Site) : s ∈ allSites := by
  cases s with
  | word k | down k | total k => cases k <;> decide +kernel
  | up k j => revert j; cases k <;> decide +kernel
  | vote l | pre l | tiles l | wend l | barEnd l | exit l | wb l | fence l | bsync l | barr l
  | stat l => cases l <;> decide +kernel
  | bld b c => revert c; cases b <;> decide +kernel
  | ws r | narr r | parr r | pws r | pel r | parr2 r | pwend r => cases r <;> decide +kernel
  | sld r c | pst r c | pwst r c => revert c; cases r <;> decide +kernel
  | sldw c | fin c => revert c; decide +kernel
  | _ => decide +kernel

/-- The signal points of a class for a lane (`lz`: lane 0 of its warp). -/
def ptsOf (lz : Bool) (c : Cnt) : List Nat :=
  if c.pointed then
    ((allSites.filter fun s => sig s == some c && (lz || !s.isBarr)).map (·.pos)).dedup
  else []

/-- The successors of a site other than itself (a failed poll, the elements of a bias load and
the implicit wait of a delayed P store stay at their site). -/
def nexts (lz : Bool) : Site → List Site
  | .setmax => [.bar1]
  | .bar1 => [.down .first, .word .first]
  | .word k => [.down k]
  | .down k => [.up k 0]
  | .up k j => if j.val = 4 then [.total k] else [.up k (j + 1)]
  | .total k => [.wend k.late, .vote k.late, .down (Epilogue.loopOf k.late),
      .word (Epilogue.loopOf k.late)]
  | .vote l => [.tiles l, .pre l]
  | .pre l => [.tiles l]
  | .tiles l => if l then [.wend true] else [.q0, .wend false]
  | .q0 => [.q1]
  | .q1 => [.uk]
  | .uk => [.wq]
  | .wq => [.ws .first]
  | .ws r => [.sld r 0]
  | .sld .plain c => [.sldw c]
  | .sld r c => if c.val = 3 then [afterLoads r] else [.sld r (c + 1)]
  | .sldw c => if c.val = 3 then [.stat true] else [.sld .plain (c + 1)]
  | .wb b => [.bld b 0]
  | .bld b c => if c.val = 15 then [.fence b] else [.bld b (c + 1)]
  | .fence b => [.bsync b]
  | .bsync b => if lz then [.barr b] else [if b then .stat false else .narr .first]
  | .barr b => [if b then .stat false else .narr .first]
  | .stat pl => [.narr (if pl then .plain else .bias)]
  | .narr r => [.pst r 0]
  | .pst r q => [pstNext r q]
  | .pwst r k => [if k.val = 0 then .parr r else .pws r]
  | .parr r => [.pst r 3]
  | .pws r => [.pel r]
  | .pel r => [.parr2 r, .pwend r]
  | .parr2 r => [.pwend r]
  | .pwend .plain => [.ws .plain, .fin 0]
  | .pwend _ => [.ws .bias, .ws .plain, .fin 0]
  | .fin 0 => [.fin 1]
  | .fin 1 => [.finarr]
  | .finarr => [.down .second, .word .second]
  | .wend l => [.barEnd l]
  | .barEnd l => [.exit l]
  | .exit _ => []

/-! ### Regions -/

/-- Before the rounds, or on a lane without a tile: no round done. -/
def preR (s : Site) : Bool := decide (s.pos < 10064) || s.noTile

/-- After the rounds (the final stores, the second pass and the end of a lane with a tile). -/
def afterR (s : Site) : Bool := decide (15228 ≤ s.pos) && !s.noTile

/-- The final stores and the arrival after them (before the second pass). -/
def finR (s : Site) : Bool := decide (15228 ≤ s.pos) && decide (s.pos ≤ 15232)

/-- The ends of the rounds: their successors change the rounds done or enter a region. -/
def Site.special : Site → Bool
  | .pwend _ => true
  | _ => false

/-- The points of all classes for a lane. -/
def allPts (lz : Bool) : List Nat :=
  (allSites.filter fun s => (sig s).any Cnt.pointed && (lz || !s.isBarr)).map (·.pos)

/-- A move from `s` to `s'` with the same rounds done passes exactly the point `s.pos`. -/
def pmove (lz : Bool) (s s' : Site) : Bool :=
  (allPts lz).all fun q => before s' q == (before s q || q == s.pos)

/-- A move at the end of a round of the region `inR`: the round's points are all passed and start
again. -/
def rmove (lz : Bool) (inR : Nat → Bool) (s s' : Site) : Bool :=
  (allPts lz).all fun q =>
    if inR q then (before s q || q == s.pos) && !before s' q
    else before s' q == (before s q || q == s.pos)

/-- A move enters no region it was not in. -/
def regOk (s s' : Site) : Bool :=
  (!inBias s'.pos || inBias s.pos) && (!inPlain s'.pos || inPlain s.pos) &&
    (!preR s' || preR s) && (!afterR s' || afterR s) && (!finR s' || finR s)

/-- What every move from site `s` to a listed successor satisfies. -/
def moveOk (lz : Bool) (s s' : Site) : Bool :=
  (match s with
    | .pwend .bias => rmove lz inBias s s'
    | .pwend .plain => rmove lz inPlain s s'
    | _ => pmove lz s s') && (s.special || regOk s s')

set_option maxRecDepth 100000 in
theorem moves_ok : [false, true].all (fun lz =>
    allSites.all (fun s => (nexts lz s).all (moveOk lz s))) = true := by decide +kernel

/-! ### Points -/

/-- The classes with points. -/
def allCnt : List Cnt :=
  [.arrive 96, .arrive 336, .acquire 80, .acquire 192, .acquire 320, .bar2, .nb, .sb, .tcld, .tcst,
    .sst]

set_option maxRecDepth 100000 in
theorem sig_cnt_all :
    allSites.all (fun s => match sig s with
      | none => true
      | some c => !c.pointed || allCnt.contains c) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem sig_pts_all : [false, true].all (fun lz => allSites.all fun s => (s.isBarr && !lz) ||
    allCnt.all fun c => decide (s.pos ∈ ptsOf lz c) == (sig s == some c)) = true := by
  decide +kernel

theorem ptsOf_nil {lz : Bool} {c : Cnt} (h : c ∉ allCnt) : ptsOf lz c = [] := by
  unfold ptsOf
  split
  · rename_i hp
    rw [List.dedup_eq_nil, List.map_eq_nil_iff, List.filter_eq_nil_iff]
    intro s hs hsig
    simp only [Bool.and_eq_true, beq_iff_eq] at hsig
    have := List.all_eq_true.mp sig_cnt_all s hs
    rw [hsig.1] at this
    simp only [hp, Bool.not_true, Bool.false_or, List.contains_iff_mem] at this
    exact h this
  · rfl

theorem ptsOf_sub (lz : Bool) (c : Cnt) : ∀ q ∈ ptsOf lz c, q ∈ allPts lz := by
  intro q hq
  unfold ptsOf at hq
  split at hq
  · rename_i hp
    simp only [List.mem_dedup, List.mem_map, List.mem_filter, Bool.and_eq_true,
      beq_iff_eq] at hq
    obtain ⟨s, ⟨hs, hsig, hb⟩, rfl⟩ := hq
    simp only [allPts, List.mem_map, List.mem_filter, Bool.and_eq_true]
    exact ⟨s, ⟨hs, by simp [hsig, hp], hb⟩, rfl⟩
  · cases hq

theorem ptsOf_nodup (lz : Bool) (c : Cnt) : (ptsOf lz c).Nodup := by
  unfold ptsOf; split
  · exact List.nodup_dedup _
  · exact List.nodup_nil

/-- **A site's point is a point of a class exactly when the site's event is of the class**, for a
pointed class and a site the lane visits. -/
theorem sig_pts {lz : Bool} (s : Site) {c : Cnt} (hp : c.pointed = true)
    (hb : s.isBarr = true → lz = true) : s.pos ∈ ptsOf lz c ↔ sig s = some c := by
  by_cases h : c ∈ allCnt
  · have h1 := List.all_eq_true.mp sig_pts_all lz (by cases lz <;> simp)
    have h2 := List.all_eq_true.mp h1 s (mem_allSites s)
    have hb' : (s.isBarr && !lz) = false := by
      cases hs : s.isBarr <;> simp_all
    simp only [hb', Bool.false_or] at h2
    have := List.all_eq_true.mp h2 c h
    simp only [beq_iff_eq] at this
    rw [← decide_eq_true_iff (p := s.pos ∈ ptsOf lz c), this]
    simp
  · rw [ptsOf_nil h]
    have := List.all_eq_true.mp sig_cnt_all s (mem_allSites s)
    constructor
    · intro hm; cases hm
    · intro hs
      rw [hs] at this
      simp only [hp, Bool.not_true, Bool.false_or, List.contains_iff_mem] at this
      exact absurd this h

/-! ### Counting lemmas -/

theorem before_self (s : Site) : before s s.pos = false := by
  unfold before; split
  · simp
  · split <;> simp

theorem countP_or_eq {p : Nat → Bool} {a : Nat} {l : List Nat} (hp : p a = false) (hl : l.Nodup) :
    l.countP (fun q => p q || q == a) = l.countP p + if a ∈ l then 1 else 0 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.nodup_cons] at hl
    simp only [List.countP_cons, ih hl.2, List.mem_cons]
    by_cases hx : x = a
    · subst hx
      simp [hp, hl.1]
    · have : (x == a) = false := by simpa using hx
      simp only [this, Bool.or_false]
      by_cases ha : a ∈ l
      · simp [ha, Ne.symm hx]; omega
      · simp [ha, Ne.symm hx]

theorem countP_congr' {p q : Nat → Bool} {l : List Nat} (h : ∀ x ∈ l, p x = q x) :
    l.countP p = l.countP q := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.countP_cons, h x (by simp), ih fun y hy => h y (by simp [hy])]

theorem countP_split (p q : Nat → Bool) (l : List Nat) :
    l.countP p = l.countP (fun x => p x && q x) + l.countP (fun x => p x && !q x) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.countP_cons, ih]
    cases p x <;> cases q x <;> simp <;> omega

/-- **A move passing the point `s.pos`** adds it to the class's count. -/
theorem passed_move {lz : Bool} {s s' : Site} (rb rp : Nat) (hm : pmove lz s s' = true)
    (c : Cnt) : passed (ptsOf lz c) s' rb rp =
      passed (ptsOf lz c) s rb rp + if s.pos ∈ ptsOf lz c then 1 else 0 := by
  unfold passed
  have h1 : (ptsOf lz c).countP (before s') =
      (ptsOf lz c).countP (fun q => before s q || q == s.pos) :=
    countP_congr' fun q hq => by
      have := List.all_eq_true.mp hm q (ptsOf_sub lz c q hq)
      simpa using this
  rw [h1, countP_or_eq (before_self s) (ptsOf_nodup lz c)]
  omega

/-- **The end of a round of the region `inR`**: its points are all passed and start again. -/
theorem passed_rmove_core {lz : Bool} {inR : Nat → Bool} {s s' : Site}
    (hm : rmove lz inR s s' = true)
    (c : Cnt) : (ptsOf lz c).countP (before s') + (ptsOf lz c).countP inR =
      (ptsOf lz c).countP (before s) + (if s.pos ∈ ptsOf lz c then 1 else 0) := by
  have hq := fun q hq => List.all_eq_true.mp hm q (ptsOf_sub lz c q hq)
  have h1 : (ptsOf lz c).countP (before s') =
      (ptsOf lz c).countP (fun q => (before s q || q == s.pos) && !inR q) :=
    countP_congr' fun q hq' => by
      have := hq q hq'
      by_cases hr : inR q <;> simp_all
  have h2 : (ptsOf lz c).countP inR =
      (ptsOf lz c).countP (fun q => (before s q || q == s.pos) && inR q) :=
    countP_congr' fun q hq' => by
      have := hq q hq'
      by_cases hr : inR q <;> simp_all
  have h3 := countP_split (fun q => before s q || q == s.pos) inR (ptsOf lz c)
  rw [countP_or_eq (before_self s) (ptsOf_nodup lz c)] at h3
  rw [h1, h2]
  omega

theorem passed_rmoveB {lz : Bool} {s s' : Site} (rb rp : Nat) (hm : rmove lz inBias s s' = true)
    (c : Cnt) : passed (ptsOf lz c) s' (rb + 1) rp =
      passed (ptsOf lz c) s rb rp + if s.pos ∈ ptsOf lz c then 1 else 0 := by
  have := passed_rmove_core hm c
  unfold passed
  rw [Nat.add_mul, one_mul]
  omega

theorem passed_rmoveP {lz : Bool} {s s' : Site} (rb rp : Nat) (hm : rmove lz inPlain s s' = true)
    (c : Cnt) : passed (ptsOf lz c) s' rb (rp + 1) =
      passed (ptsOf lz c) s rb rp + if s.pos ∈ ptsOf lz c then 1 else 0 := by
  have := passed_rmove_core hm c
  unfold passed
  rw [Nat.add_mul, one_mul]
  omega

/-! ### The reference conjuncts -/

/-- Whether the lane is lane 0 of its warp (the lane that frees the bias slot). -/
def lz (L : Launch) (g : Nat) : Bool := !scmpi .ne .b (andi (tidW L g) 31) 0

/-- The three parities of a biased round, and the two of a plain round, at round count `j`. -/
def parB (j : Nat) (v : V) : Prop :=
  v.spar = i32 ((j % 2 : Nat) : Int) ∧ v.ppar = i32 ((j % 2 : Nat) : Int) ∧
    v.bpar = i32 ((j % 2 : Nat) : Int)
def parP (j : Nat) (v : V) : Prop :=
  v.spar = i32 ((j % 2 : Nat) : Int) ∧ v.ppar = i32 ((j % 2 : Nat) : Int)

def Site.isParr2 : Site → Bool
  | .parr2 _ => true
  | _ => false

/-- The number of biased rounds after the first (the two's complement value of `%r169 - %r299`,
which the code compares with 1 after the first round) and the number of plain rounds (that of
`%r431`). Both read only the scan and the used-K length. -/
def nB (p : Params) (L : Launch) (g : Nat) (v : V) : Int :=
  toSigned 32 (r32 (sub32 (r169 p L g v) (r299 p L g v)))
def nP (p : Params) (L : Launch) (g : Nat) (v : V) : Int := toSigned 32 (r32 (r431 p L g v))

/-- All rounds of a kind are done: `n` of them, or none when there are fewer than one. -/
def Done (r : Nat) (n : Int) : Prop := (r : Int) = n ∨ (r = 0 ∧ n < 1)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
