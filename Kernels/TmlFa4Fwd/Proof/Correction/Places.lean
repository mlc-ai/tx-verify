-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Correction.Ledger
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The places and the closed forms of the counts

The definitions of the reference invariant's closed forms, apart from the invariant (`Ref.lean`): a
theorem about a place or a formula does not read the invariant. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (r32 i32 Scan)

noncomputable section

/-! ### Places -/

/-- The program counters inside a rescale round. -/
def inRound (pc : Nat) : Bool := 8006 ≤ pc && pc ≤ 8446

/-- Whether a site is an end state of a lane that found no tile. -/
def Site.noTile : Site → Bool
  | .wend false | .barEnd false | .exit false => true
  | _ => false

/-- Whether point `q` is passed in the current pass before a state at site `s`: a point of a
round when it lies before `s` in the current round; another point when it lies before `s`, and on
a lane without a tile not between the request's reads and the end. -/
def before (s : Site) (q : Nat) : Bool :=
  if inRound q then inRound s.pc && decide (q < s.pc)
  else decide (q < s.pc) && !(s.noTile && decide (7955 ≤ q) && decide (q < 9201))

/-- The points of `pts` a state at site `s` with `r` rounds done has passed. -/
def passed (pts : List Nat) (s : Site) (r : Nat) : Nat :=
  pts.countP (before s) + r * pts.countP inRound

/-- The signal points of the barrier at shared offset `o` (mbarrier arrivals). -/
def arrivePts : Nat → List Nat
  | 96 => [7752, 8223, 8759]
  | 104 => [7754, 8442, 9055]
  | 192 => [7987, 8443, 8468]
  | 200 => [8224, 8464, 8764]
  | 208 => [8760]
  | 216 => [9056]
  | _ => []

/-- The poll points of the barrier at shared offset `o`. -/
def pollPts : Nat → List Nat
  | 144 => [8473]
  | 224 => [8476]
  | 152 => [8769]
  | 232 => [8772, 9201]
  | _ => []

/-- The points of barrier 2 and of the lane's two named barriers. -/
def bar2Pts : List Nat := [7747, 9204]
def nbPts : Fin 2 → List Nat
  | 0 => [7985, 8006, 8465]
  | 1 => [7988, 8225, 8761]

/-- The points of a class (the stores are counted by `finalStores`). -/
def ptsOf : Cnt → List Nat
  | .arrive o => arrivePts o
  | .acquire o => pollPts o
  | .bar2 => bar2Pts
  | .nb k => nbPts k
  | .st => []

/-- The classes with points. -/
def allCnt : List Cnt :=
  [.arrive 96, .arrive 104, .arrive 192, .arrive 200, .arrive 208, .arrive 216, .acquire 144,
    .acquire 224, .acquire 152, .acquire 232, .bar2, .nb 0, .nb 1]

/-- All points. -/
def allPts : List Nat := allCnt.flatMap ptsOf

/-- The class of the event a site fires (of a successful poll at a poll site). -/
def sig : Site → Option Cnt
  | .arr 0 => some (.arrive 96)
  | .arr 1 => some (.arrive 104)
  | .free => some (.arrive 192)
  | .rarr 0 0 => some (.arrive 96)
  | .rarr 0 1 => some (.arrive 200)
  | .rarr 1 0 => some (.arrive 104)
  | .rarr 1 1 => some (.arrive 192)
  | .farr0 => some (.arrive 200)
  | .farr 0 => some (.arrive 192)
  | .farr 1 => some (.arrive 200)
  | .fdone 0 0 => some (.arrive 96)
  | .fdone 0 1 => some (.arrive 208)
  | .fdone 1 0 => some (.arrive 104)
  | .fdone 1 1 => some (.arrive 216)
  | .fw 0 0 => some (.acquire 144)
  | .fw 0 1 => some (.acquire 224)
  | .fw 1 0 => some (.acquire 152)
  | .fw 1 1 => some (.acquire 232)
  | .wend _ => some (.acquire 232)
  | .bar1 | .barEnd _ => some .bar2
  | .nb k | .rbar k | .fbar k => some (.nb k)
  | .fst _ _ _ | .lse _ => some .st
  | _ => none

/-- The poll sites. -/
def Site.isPoll : Site → Bool
  | .fw _ _ | .wend _ => true
  | _ => false

/-! ### Sites and their successors -/

def allScan : List Scan := [.first, .loop, .second, .loop2]

/-- All sites. -/
def allSites : List Site :=
  List.flatten [
    [.setmax, .bar1, .arr 0, .arr 1], allScan.map .word, allScan.map .down,
    allScan.flatMap fun k => (List.finRange 5).map (.up k), allScan.map .total,
    [false, true].flatMap fun l => [.vote l, .pre l, .tiles l, .wend l, .barEnd l, .exit l],
    [.q0, .q1, .uk, .nb 0, .nb 1, .free, .farr0],
    (List.finRange 2).flatMap fun st =>
      [.rbar st, .rscale st, .rvote st, .rwait st, .rarr st 0, .rarr st 1, .fbar st, .fsum st,
        .fmax st, .farr st, .fw st 0, .fw st 1, .fence st, .fdone st 0, .fdone st 1, .lse st],
    (List.finRange 2).flatMap fun st =>
      (List.finRange 8).flatMap fun c => [.rld st c, .rldw st c, .rst st c],
    (List.finRange 2).flatMap fun st =>
      (List.finRange 16).flatMap fun j => [.fld st j, .fwl st j, .fst st j 0, .fst st j 1]]

set_option maxRecDepth 100000 in
theorem mem_allSites (s : Site) : s ∈ allSites := by
  cases s with
  | word k | down k | total k => cases k <;> decide +kernel
  | up k j => revert j; cases k <;> decide +kernel
  | vote l | pre l | tiles l | wend l | barEnd l | exit l => cases l <;> decide +kernel
  | arr a | nb a | rbar a | rscale a | rvote a | rwait a | fbar a | fsum a | fmax a | farr a
  | fence a | lse a => revert a; decide +kernel
  | rld a b | rldw a b | rst a b | rarr a b | fw a b | fld a b | fwl a b | fdone a b =>
    revert a b; decide +kernel
  | fst a b c => revert a b c; decide +kernel
  | _ => decide +kernel

/-- The successors of a site other than itself (a failed poll and the elements of a vector store
stay at their site). -/
def nexts : Site → List Site
  | .setmax => [.bar1]
  | .bar1 => [.arr 0]
  | .arr 0 => [.arr 1]
  | .arr 1 => [.down .first, .word .first]
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
  | .uk => [.nb 0]
  | .nb 0 => [.free]
  | .free => [.nb 1]
  | .nb 1 => [.farr0, .rbar 0]
  | .rbar st => [.rscale st]
  | .rscale st => [.rvote st]
  | .rvote st => [.rarr st 0, .rld st 0]
  | .rld st c => [.rldw st c]
  | .rldw st c => [.rst st c]
  | .rst st c => if c.val = 7 then [.rwait st] else [.rld st (c + 1)]
  | .rwait st => [.rarr st 0]
  | .rarr st 0 => [.rarr st 1]
  | .rarr 0 1 => [.rbar 1]
  | .rarr 1 1 => [.rbar 0, .farr0]
  | .farr0 => [.fbar 0]
  | .fbar st => [.fsum st]
  | .fsum st => [.fmax st]
  | .fmax st => [.farr st]
  | .farr st => [.fw st 0]
  | .fw st k => if k.val = 0 then [.fw st 1] else [.fld st 0]
  | .fld st j => [.fwl st j]
  | .fwl st j => [.fst st j 0]
  | .fst st j h => if h.val = 0 then [.fst st j 1] else if j.val = 15 then [.fence st]
      else [.fld st (j + 1)]
  | .fence st => [.fdone st 0]
  | .fdone st 0 => [.fdone st 1]
  | .fdone 0 1 => [.fbar 1]
  | .fdone 1 1 => [.lse 0, .lse 1, .down .second, .word .second]
  | .lse 0 => [.lse 1, .down .second, .word .second]
  | .lse 1 => [.down .second, .word .second]
  | .wend l => [.barEnd l]
  | .barEnd l => [.exit l]
  | .exit _ => []

/-- The two sites whose successor changes the rounds: the entry and the end of a round. -/
def Site.special : Site → Bool
  | .nb 1 | .rarr 1 1 => true
  | _ => false

/-! ### Regions, stores, sub-steps -/

/-- Before the rounds, or on a lane without a tile: no round done. -/
def preR (s : Site) : Bool := decide (s.pc < 8006) || s.noTile

/-- From the final stage to the LSE stores: all rounds done. -/
def tailR (s : Site) : Bool := decide (8447 ≤ s.pc) && decide (s.pc < 9089)

/-- The vector-store sites, and the LSE sites. -/
def Site.isFst : Site → Bool
  | .fst _ _ _ => true
  | _ => false
def Site.isLse : Site → Bool
  | .lse _ => true
  | _ => false

/-- The final stage's stores before a state at site `s` and sub-step `k`: eight per chunk done
(stage 0's sixteen chunks before stage 1's), and the elements of the current chunk's stores. -/
def finalStores (s : Site) (k : Fin 4) : Nat :=
  match s with
  | .fld st j | .fwl st j => 8 * (16 * st.val + j.val)
  | .fst st j h => 8 * (16 * st.val + j.val) + 4 * h.val + k.val
  | .fence st | .fdone st _ => 128 * (st.val + 1)
  | .fbar 1 | .fsum 1 | .fmax 1 | .farr 1 | .fw 1 _ => 128
  | .lse _ | .word .second | .down .second | .up .second _ | .total .second | .word .loop2
  | .down .loop2 | .up .loop2 _ | .total .loop2 | .vote true | .pre true | .tiles true
  | .wend true | .barEnd true | .exit true => 256
  | _ => 0

/-- The LSE stores a state at site `s` may have done. -/
def lseB : Site → Nat
  | .lse 1 => 1
  | .word .second | .down .second | .up .second _ | .total .second | .word .loop2
  | .down .loop2 | .up .loop2 _ | .total .loop2 | .vote true | .pre true | .tiles true
  | .wend true | .barEnd true | .exit true => 2
  | _ => 0

/-- The row-sum reads. -/
def Site.isFsum : Site → Bool
  | .fsum _ => true
  | _ => false

/-- The sites after the read of stage `st`'s row sum, up to the LSE stores: the row sum is
nonnegative there (the LSE's logarithm is followed on a positive or a zero sum). -/
def rsPos (st : Fin 2) (s : Site) : Bool :=
  decide (8467 + 296 * st.val ≤ s.pc) && decide (s.pc ≤ 9082)

/-- The sub-step of a state at a site other than a vector store's. -/
def kIn : Site → Fin 4
  | .rldw _ _ => 1
  | _ => 0

/-! ### Moves -/

/-- A move from `s` to `s'` with the same rounds done passes exactly the point `s.pc`. -/
def pmove (s s' : Site) : Bool :=
  allPts.all fun q => before s' q == (before s q || q == s.pc)

/-- A move at the end of a round: the round's points are all passed and start again. -/
def rmove (s s' : Site) : Bool :=
  allPts.all fun q =>
    if inRound q then (before s q || q == s.pc) && !before s' q
    else before s' q == (before s q || q == s.pc)

/-- A move enters no region of the rounds' conjuncts. -/
def regOk (s s' : Site) : Bool :=
  (!inRound s'.pc || inRound s.pc) && (!tailR s' || tailR s) && (!preR s' || preR s)

/-- The stores of a move to `s'` leaving `s` at its last sub-step. -/
def stOk (s s' : Site) : Bool :=
  finalStores s' 0 ==
    finalStores s (if s.isFst then 3 else 0) + if s.isFst then 1 else 0

def lseOk (s s' : Site) : Bool := lseB s + (if s.isLse then 1 else 0) ≤ lseB s'

/-- A move that reads no row sum lands where the row sums it needs were needed before. -/
def rsOk (s s' : Site) : Bool :=
  s.isFsum || ((!rsPos 0 s' || rsPos 0 s) && (!rsPos 1 s' || rsPos 1 s))

/-- What every move from site `s` to a listed successor satisfies. -/
def moveOk (s s' : Site) : Bool :=
  (if s = .rarr 1 1 then rmove s s' else pmove s s') && (s.special || regOk s s') &&
    stOk s s' && lseOk s s' && (!s'.isFst || kIn s' == 0) && rsOk s s'

set_option maxRecDepth 100000 in
theorem moves_ok : allSites.all (fun s => (nexts s).all (moveOk s)) = true := by decide +kernel

theorem setmax_first : allPts.all (fun q => !before .setmax q) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem sig_pts_all :
    allSites.all (fun s => allCnt.all fun c => decide (s.pc ∈ ptsOf c) == (sig s == some c)) =
      true := by decide +kernel

set_option maxRecDepth 100000 in
theorem sig_cnt_all :
    allSites.all (fun s => match sig s with
      | none => true
      | some c => c == .st || allCnt.contains c) = true := by
  decide +kernel

theorem ptsOf_nil {c : Cnt} (h : c ∉ allCnt) : ptsOf c = [] := by
  cases c with
  | arrive o => simp only [ptsOf, arrivePts]; split <;> simp_all [allCnt]
  | acquire o => simp only [ptsOf, pollPts]; split <;> simp_all [allCnt]
  | bar2 => simp [allCnt] at h
  | nb k => fin_cases k <;> simp [allCnt] at h
  | st => rfl

theorem ptsOf_sub (c : Cnt) : ∀ q ∈ ptsOf c, q ∈ allPts := by
  intro q hq
  by_cases h : c ∈ allCnt
  · exact List.mem_flatMap.mpr ⟨c, h, hq⟩
  · rw [ptsOf_nil h] at hq; cases hq

theorem ptsOf_nodup (c : Cnt) : (ptsOf c).Nodup := by
  by_cases h : c ∈ allCnt
  · simp only [allCnt, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  · rw [ptsOf_nil h]; exact List.nodup_nil

/-- **A site's point is in a class's points exactly when the site's event is of the class.** -/
theorem sig_pts (s : Site) {c : Cnt} (hc : c ≠ .st) : s.pc ∈ ptsOf c ↔ sig s = some c := by
  by_cases h : c ∈ allCnt
  · have := List.all_eq_true.mp (List.all_eq_true.mp sig_pts_all s (mem_allSites s)) c h
    simp only [beq_iff_eq] at this
    rw [← decide_eq_true_iff (p := s.pc ∈ ptsOf c), this]
    simp
  · rw [ptsOf_nil h]
    have := List.all_eq_true.mp sig_cnt_all s (mem_allSites s)
    constructor
    · intro hm; cases hm
    · intro hs
      rw [hs] at this
      simp only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at this
      rcases this with h1 | h1
      · exact absurd h1 hc
      · exact absurd h1 h

/-! ### Counting lemmas -/

theorem before_self (s : Site) : before s s.pc = false := by
  unfold before; split <;> simp

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

/-- **A move passing the point `s.pc`** adds it to the class's count. -/
theorem passed_move {s s' : Site} (r : Nat) (hm : pmove s s' = true) (c : Cnt) :
    passed (ptsOf c) s' r = passed (ptsOf c) s r + if s.pc ∈ ptsOf c then 1 else 0 := by
  unfold passed
  have h1 : (ptsOf c).countP (before s') = (ptsOf c).countP (fun q => before s q || q == s.pc) :=
    countP_congr' fun q hq => by
      have := List.all_eq_true.mp hm q (ptsOf_sub c q hq)
      simpa using this
  rw [h1, countP_or_eq (before_self s) (ptsOf_nodup c)]
  omega

theorem countP_split (p q : Nat → Bool) (l : List Nat) :
    l.countP p = l.countP (fun x => p x && q x) + l.countP (fun x => p x && !q x) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.countP_cons, ih]
    cases p x <;> cases q x <;> simp <;> omega

/-- **The end of a round**: one more round done, and the round's points start again. -/
theorem passed_rmove {s s' : Site} (r : Nat) (hm : rmove s s' = true) (c : Cnt) :
    passed (ptsOf c) s' (r + 1) = passed (ptsOf c) s r + if s.pc ∈ ptsOf c then 1 else 0 := by
  unfold passed
  have hq := fun q hq => List.all_eq_true.mp hm q (ptsOf_sub c q hq)
  have h1 : (ptsOf c).countP (before s') =
      (ptsOf c).countP (fun q => (before s q || q == s.pc) && !inRound q) :=
    countP_congr' fun q hq' => by
      have := hq q hq'
      by_cases hr : inRound q <;> simp_all
  have h2 : (ptsOf c).countP inRound =
      (ptsOf c).countP (fun q => (before s q || q == s.pc) && inRound q) :=
    countP_congr' fun q hq' => by
      have := hq q hq'
      by_cases hr : inRound q <;> simp_all
  have h3 := countP_split (fun q => before s q || q == s.pc) inRound (ptsOf c)
  rw [countP_or_eq (before_self s) (ptsOf_nodup c)] at h3
  rw [h1, Nat.add_mul, one_mul]
  have h4 : (ptsOf c).countP inRound * 1 = (ptsOf c).countP inRound := Nat.mul_one _
  omega

/-! ### The count conjuncts -/

/-- The tile's number of K/V blocks as the rounds compare it (a signed word). -/
abbrev Bs (p : Params) (L : Launch) (g : Nat) (v : V) : Int := toSigned 32 (r32 (blocks p L g v))

end
end PTX.Kernels.TmlFa4Fwd.Proof.Correction
