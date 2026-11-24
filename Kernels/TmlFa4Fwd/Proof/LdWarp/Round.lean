-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.Frame
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader's rounds: how many packets a tile has

The loader loads a tile's K/V blocks as packets, two per block (the K half and the V half): the
first block, then the warm rounds (`%r6114` from 0 while the next round is not `warmRounds`), then
the steady rounds (the same counter, while the next round is below `%r31`). The number of
packets is a function of the tile's block word `b = %r28` alone (`pkts b`), with `%r31 = b - 1`
as 32-bit words: the warm rounds `wRn b = min (max (b - 1) 0) 9` (none when `b < 2`, `w0 b`) and
the steady rounds from `wRn b` to `b - 1`. The conditions are the code's signed 32-bit
comparisons (`sv` is the signed value of a 32-bit word); no bound on `b` is used.

`Rounds s v nc` states, at a state of a block, the round counter and the commits `nc` so far:
the first block's commits, `2 + 2 r` plus the block's commits in warm round `r`, the warm rounds'
and the steady rounds' commits in steady round `r`, all warm rounds' after the warm loop. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section

/-- The signed value of a 32-bit word. -/
abbrev sv (x : BitVec 64) : Int := toSigned 32 x

/-- The warm rounds of a tile with block word `b`. -/
def wRn (b : BitVec 64) : Nat := (min (max (sv (addi b (-1))) 0) 9).toNat

/-- The warm rounds done before the steady rounds: none with fewer than two blocks. -/
def w0 (b : BitVec 64) : Nat := if sv b < 2 then 0 else wRn b

/-- **The packets of a tile with block word `b`.** -/
def pkts (b : BitVec 64) : Nat := 2 + 2 * w0 b + 2 * (sv (addi b (-1)) - wRn b).toNat

/-- The rounds conjuncts of a block `o` at a state with `ib` commits of its block so far. -/
def RoundsB (o : Option Blk) (ib : Nat) (v : V) (nc : Nat) : Prop :=
  match o with
  | some .prime => nc = ib
  | some .warm => ∃ r, v.rnd = W r ∧ 2 ≤ sv v.su.r28 ∧ r < wRn v.su.r28 ∧ nc = 2 + 2 * r + ib
  | some .steady => ∃ r, v.rnd = W r ∧ wRn v.su.r28 ≤ r ∧ (r : Int) < sv (addi v.su.r28 (-1)) ∧
      nc = 2 + 2 * w0 v.su.r28 + 2 * (r - wRn v.su.r28) + ib
  | some .tma6 => v.rnd = W (wRn v.su.r28) ∧ 2 ≤ sv v.su.r28 ∧ nc = 2 + 2 * wRn v.su.r28 + ib
  | none => True

/-- The rounds conjuncts at a state of the tile's blocks, with `nc` commits so far. -/
def Rounds (s : Site) (v : V) (nc : Nat) : Prop :=
  v.su.r31 = addi v.su.r28 (-1) ∧ RoundsB (bc s) (inBlk s) v nc

/-! ### Signed 32-bit words -/

theorem sv_spec (x : BitVec 64) :
    sv x % 2 ^ 32 = ((x.toNat % 2 ^ 32 : Nat) : Int) ∧ -2 ^ 31 ≤ sv x ∧ sv x < 2 ^ 31 := by
  simp only [sv, toSigned]
  have h := Nat.mod_lt x.toNat (show 0 < 2 ^ 32 by decide)
  split <;> omega

theorem sv_r32 (x : BitVec 64) : sv (r32 x) = sv x := by
  simp only [sv, toSigned, r32, truncBits, BitVec.toNat_ofNat]
  rw [show x.toNat % 2 ^ 32 % 2 ^ 64 % 2 ^ (32 : Nat) = x.toNat % 2 ^ 32 by omega]

theorem sv_eq {x y : BitVec 64} (h : (x.toNat : Int) % 2 ^ 32 = (y.toNat : Int) % 2 ^ 32) :
    sv x = sv y := by
  have hx := sv_spec x
  have hy := sv_spec y
  omega

theorem sv_W {n : Nat} (h : n < 2 ^ 31) : sv (W n) = n := toSigned_W h

theorem toNat_addi (x : BitVec 64) (n : Int) :
    ((addi x n).toNat : Int) % 2 ^ 32 = ((x.toNat : Int) + n) % 2 ^ 32 := by
  simp only [addi, r32, i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofInt]
  omega

/-- `b - 1` as a 32-bit word: one less, except at the least word. -/
theorem sv_addi_neg1 (x : BitVec 64) (h : -2 ^ 31 < sv x) : sv (addi x (-1)) = sv x - 1 := by
  have h1 := sv_spec (addi x (-1))
  have h2 := sv_spec x
  have h3 := toNat_addi x (-1)
  omega

theorem sv_addi1 (x : BitVec 64) (h : sv x < 2 ^ 31 - 1) : sv (addi x 1) = sv x + 1 := by
  have h1 := sv_spec (addi x 1)
  have h2 := sv_spec x
  have h3 := toNat_addi x 1
  omega

theorem scmp_s (c : Cmp) (x y : BitVec 64) :
    scmp c .s x y = PTX.compare c .s 32 x y := by
  simp only [scmp, PTX.compare]
  have h1 : toSigned 32 (r32 x) = toSigned 32 x := sv_r32 x
  have h2 : toSigned 32 (r32 y) = toSigned 32 y := sv_r32 y
  rw [h1, h2]

theorem scmp_lt_s (x y : BitVec 64) : scmp .lt .s x y = decide (sv x < sv y) := by
  rw [scmp_s]; rfl

theorem scmp_ge_s (x y : BitVec 64) : scmp .ge .s x y = decide (sv y ≤ sv x) := by
  rw [scmp_s]; simp [PTX.compare, sv]

theorem sv_i32 {n : Int} (h0 : -2 ^ 31 ≤ n) (h1 : n < 2 ^ 31) : sv (i32 n) = n := by
  have h := sv_spec (i32 n)
  have h2 : ((i32 n).toNat : Int) % 2 ^ 32 = n % 2 ^ 32 := by
    simp only [i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
    omega
  omega

theorem scmpi_lt_s (x : BitVec 64) {n : Int} (h0 : -2 ^ 31 ≤ n) (h1 : n < 2 ^ 31) :
    scmpi .lt .s x n = decide (sv x < n) := by
  simp only [scmpi, PTX.compare]
  have h2 : toSigned 32 (r32 x) = toSigned 32 x := sv_r32 x
  have h3 : toSigned 32 (i32 n) = n := sv_i32 h0 h1
  rw [h2, h3]

theorem scmpi_gt_s (x : BitVec 64) {n : Int} (h0 : -2 ^ 31 ≤ n) (h1 : n < 2 ^ 31) :
    scmpi .gt .s x n = decide (n < sv x) := by
  simp only [scmpi, PTX.compare]
  have h2 : toSigned 32 (r32 x) = toSigned 32 x := sv_r32 x
  have h3 : toSigned 32 (i32 n) = n := sv_i32 h0 h1
  rw [h2, h3]

/-- The warm rounds as the code computes them (`warmRounds`). -/
theorem warm_eq (x : BitVec 64) :
    min32 (max32 x (i32 0)) (i32 9) = W (min (max (sv x) 0) 9).toNat := by
  have hs := sv_spec x
  have h0 : sv (i32 0) = 0 := sv_i32 (by decide) (by decide)
  have h9 : sv (i32 9) = 9 := sv_i32 (by decide) (by decide)
  simp only [max32, min32]
  have hm : PTX.compare .gt .s 32 (r32 x) (r32 (i32 0)) = decide (0 < sv x) := by
    simp only [PTX.compare]
    rw [show toSigned 32 (r32 x) = sv x from sv_r32 x,
      show toSigned 32 (r32 (i32 0)) = 0 from (sv_r32 _).trans h0]
  rw [hm]
  by_cases hp : 0 < sv x
  · simp only [hp, decide_true, ↓reduceIte]
    have hl : PTX.compare .lt .s 32 (r32 (r32 x)) (r32 (i32 9)) = decide (sv x < 9) := by
      simp only [PTX.compare]
      rw [show toSigned 32 (r32 (r32 x)) = sv x from (sv_r32 _).trans (sv_r32 x),
        show toSigned 32 (r32 (i32 9)) = 9 from (sv_r32 _).trans h9]
    rw [hl]
    by_cases h9' : sv x < 9
    · simp only [h9', decide_true, ↓reduceIte]
      apply BitVec.eq_of_toNat_eq
      have hx := sv_spec x
      simp only [r32, truncBits, BitVec.toNat_ofNat, W]
      omega
    · simp only [h9', decide_false, Bool.false_eq_true, ↓reduceIte]
      rw [show min (max (sv x) 0) 9 = 9 by omega]
      rfl
  · simp only [hp, decide_false, Bool.false_eq_true, ↓reduceIte]
    have hl : PTX.compare .lt .s 32 (r32 (r32 (i32 0))) (r32 (i32 9)) = true := by
      simp only [PTX.compare]
      rw [show toSigned 32 (r32 (r32 (i32 0))) = 0 from (sv_r32 _).trans ((sv_r32 _).trans h0),
        show toSigned 32 (r32 (i32 9)) = 9 from (sv_r32 _).trans h9]
      decide
    rw [hl]
    simp only [↓reduceIte]
    rw [show min (max (sv x) 0) 9 = 0 by omega]
    rfl

theorem wRn_le (b : BitVec 64) : wRn b ≤ 9 := by
  unfold wRn; omega

/-- With two blocks or more there is a warm round. -/
theorem wRn_pos {b : BitVec 64} (h : 2 ≤ sv b) : 1 ≤ wRn b := by
  have := sv_addi_neg1 b (by omega)
  unfold wRn; omega

theorem w0_of {b : BitVec 64} (h : 2 ≤ sv b) : w0 b = wRn b := by
  unfold w0; simp only [show ¬ sv b < 2 by omega, ↓reduceIte]

/-- The warm rounds as the code computes them, from the tile's setup. -/
theorem warmRounds_eq {v : V} (h : v.su.r31 = addi v.su.r28 (-1)) :
    warmRounds v = W (wRn v.su.r28) := by
  simp only [warmRounds, h, warm_eq, wRn]

/-! ### The successors at the ends of the blocks -/

variable {p : Params} {L : Launch} {g w : Nat}

/-- Where a state is after the end of a block: in a block with its rounds conjuncts and no
shuffle of a packet, or at the start of the second pass with all the tile's packets. -/
def AfterBlk (d d' : D) (nc : Nat) : Prop :=
  (d'.v.sc = d.v.sc ∧ d'.v.su = d.v.su ∧ d'.site.blk = true ∧ Rounds d'.site d'.v nc ∧
      pktSh d'.site = 0 ∧ d'.v.ukw = d.v.ukw ∧ d'.v.r56 = addi d'.v.su.r28 (-2) ∧
      RowOk p L g d') ∨
    (∃ s v', d' = passStart p L g true (D.mk' s v') ∧ v'.sc = d.v.sc ∧ v'.su = d.v.su ∧
      nc = pkts d.v.su.r28)

theorem iteS_pos {c : Bool} {a b : D} (h : c = true) (ha : a.k = 0) : D.iteS c a b = a := by
  subst h; obtain ⟨s, v, k⟩ := a; simp only at ha; subst ha; rfl

theorem iteS_neg {c : Bool} {a b : D} (h : c = false) (hb : b.k = 0) : D.iteS c a b = b := by
  subst h; obtain ⟨s, v, k⟩ := b; simp only at hb; subst hb; rfl

theorem ite_k {c : Bool} {a b : D} (ha : a.k = 0) (hb : b.k = 0) : (D.ite c a b).k = 0 := by
  unfold D.ite; split <;> assumption

theorem passStart_k (late : Bool) (d : D) : (passStart p L g late d).k = 0 := by
  unfold passStart; exact ite_k rfl rfl

theorem pgEnter_k (d : D) (per : Per) (it : Fin 2) : (pgEnter p L g d per it).k = 0 := rfl

theorem pgEnter_props (d : D) (per : Per) (it : Fin 2) :
    (pgEnter p L g d per it).v.sc = d.v.sc ∧ (pgEnter p L g d per it).v.su = d.v.su ∧
      (pgEnter p L g d per it).v.rnd = d.v.rnd ∧
      bc (pgEnter p L g d per it).site = bc (.pgLd per it) ∧
      inBlk (pgEnter p L g d per it).site = 0 ∧ pktSh (pgEnter p L g d per it).site = 0 := by
  unfold pgEnter D.iteS
  split <;> simp [bc, inBlk, pktSh]

theorem pgEnter_v (d : D) (per : Per) (it : Fin 2) :
    (pgEnter p L g d per it).v.ukw = d.v.ukw ∧ (pgEnter p L g d per it).v.r56 = d.v.r56 := by
  unfold pgEnter D.iteS
  split <;> exact ⟨rfl, rfl⟩

/-- A block's first state from the page loop's entry. -/
theorem after_pg {d : D} {per : Per} {nc : Nat} (s : Site) (v0 : V) (hsc : v0.sc = d.v.sc)
    (hsu : v0.su = d.v.su) (hu : v0.ukw = d.v.ukw) (h56 : v0.r56 = addi v0.su.r28 (-2))
    (h31 : v0.su.r31 = addi v0.su.r28 (-1))
    (hB : RoundsB (bc (.pgLd per 0)) 0 v0 nc) :
    AfterBlk (p := p) (L := L) (g := g) d (pgEnter p L g (D.mk' s v0) per 0) nc := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := pgEnter_props (p := p) (L := L) (g := g) (D.mk' s v0) per 0
  obtain ⟨h7, h8⟩ := pgEnter_v (p := p) (L := L) (g := g) (D.mk' s v0) per 0
  refine .inl ⟨h1.trans hsc, h2.trans hsu, by simp only [Site.blk, h4]; cases per <;> rfl, ?_, h6,
    h7.trans hu, by rw [h8, h2]; exact h56, pgEnter_row _ _ _⟩
  refine ⟨by rw [h2]; exact h31, ?_⟩
  rw [h4, h5]
  cases per <;> simpa [RoundsB, bc, h2, h3] using hB

theorem mk_sc (s : Site) (v : V) (x : BitVec 64) : (D.mk' s { v with rnd := x }).v.sc = v.sc := rfl
theorem mk_su (s : Site) (v : V) (x : BitVec 64) : (D.mk' s { v with rnd := x }).v.su = v.su := rfl

theorem afterTail_eq (d : D) : afterTail p L g d =
    D.iteS (scmp .ge .s (warmRounds d.v) d.v.su.r31)
      (passStart p L g true (D.mk' d.site { d.v with rnd := warmRounds d.v }))
      (pgEnter p L g (D.mk' d.site { d.v with rnd := warmRounds d.v }) .steady 0) := rfl

/-- **After the warm rounds** (`afterTail`): the steady rounds from `wRn b`, or the second pass. -/
theorem after_tail {d : D} {nc : Nat} (h31 : d.v.su.r31 = addi d.v.su.r28 (-1))
    (h56 : d.v.r56 = addi d.v.su.r28 (-2))
    (hnc : nc = 2 + 2 * w0 d.v.su.r28) :
    AfterBlk (p := p) (L := L) (g := g) d (afterTail p L g d) nc := by
  have hw := warmRounds_eq h31
  have hs : sv (W (wRn d.v.su.r28)) = wRn d.v.su.r28 :=
    sv_W (by have := wRn_le d.v.su.r28; omega)
  rw [afterTail_eq, hw]
  by_cases hc : sv (addi d.v.su.r28 (-1)) ≤ (wRn d.v.su.r28 : Int)
  · have hc' : scmp .ge .s (W (wRn d.v.su.r28)) d.v.su.r31 = true := by
      rw [scmp_ge_s, hs, h31]; exact decide_eq_true hc
    rw [iteS_pos hc' (passStart_k _ _)]
    refine .inr ⟨d.site, { d.v with rnd := W (wRn d.v.su.r28) }, rfl, rfl, rfl, ?_⟩
    rw [hnc, pkts, show (sv (addi d.v.su.r28 (-1)) - wRn d.v.su.r28).toNat = 0 by omega]
    omega
  · have hc' : scmp .ge .s (W (wRn d.v.su.r28)) d.v.su.r31 = false := by
      rw [scmp_ge_s, hs, h31]; exact decide_eq_false hc
    rw [iteS_neg hc' (pgEnter_k _ _ _)]
    have hB : RoundsB (some .steady) 0 { d.v with rnd := W (wRn d.v.su.r28) } nc :=
      ⟨wRn d.v.su.r28, rfl, le_refl _,
        show (wRn d.v.su.r28 : Int) < sv (addi d.v.su.r28 (-1)) by omega, by simp [hnc]⟩
    exact after_pg d.site _ rfl rfl rfl h56 h31 hB

/-- `AfterBlk` depends on the state before only through its scan state and setup. -/
theorem afterBlk_of {d d0 x : D} {nc : Nat} (h : AfterBlk (p := p) (L := L) (g := g) d0 x nc)
    (hsc : d0.v.sc = d.v.sc) (hsu : d0.v.su = d.v.su) (hu : d0.v.ukw = d.v.ukw) :
    AfterBlk (p := p) (L := L) (g := g) d x nc := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6, h7⟩ | ⟨s, v', h1, h2, h3, h4⟩
  · exact .inl ⟨h1.trans hsc, h2.trans hsu, h3, h4, h5, h6.trans hu, h7⟩
  · exact .inr ⟨s, v', h1, h2.trans hsc, h3.trans hsu, by rw [h4, hsu]⟩

theorem afterWarm_eq (d : D) : afterWarm p L g w d =
    D.iteS (not14 w || !(scmpi .gt .s d.v.su.r28 10 && scmpi .lt .s d.v.su.r29 0))
      (afterTail p L g d) (D.mk' (.tw 6) d.v) := rfl

theorem afterTail_k (d : D) : (afterTail p L g d).k = 0 := rfl

/-- **After the warm rounds, warp 14's last Bias group or the steady rounds.** -/
theorem after_warm {d : D} {nc : Nat} (h31 : d.v.su.r31 = addi d.v.su.r28 (-1))
    (h56 : d.v.r56 = addi d.v.su.r28 (-2))
    (hnc : nc = 2 + 2 * w0 d.v.su.r28) (h6 : 10 < sv d.v.su.r28 → d.v.rnd = W (wRn d.v.su.r28)) :
    AfterBlk (p := p) (L := L) (g := g) d (afterWarm p L g w d) nc := by
  rw [afterWarm_eq]
  cases hc : (not14 w || !(scmpi .gt .s d.v.su.r28 10 && scmpi .lt .s d.v.su.r29 0))
  · rw [iteS_neg rfl rfl]
    have hg : scmpi .gt .s d.v.su.r28 10 = true := by
      revert hc; cases scmpi .gt .s d.v.su.r28 10 <;> simp
    rw [scmpi_gt_s _ (by decide) (by decide)] at hg
    have h10 : (10 : Int) < sv d.v.su.r28 := of_decide_eq_true hg
    refine .inl ⟨rfl, rfl, rfl, ⟨h31, ?_⟩, rfl, rfl, h56, fun _ _ h => by cases h⟩
    show d.v.rnd = W (wRn d.v.su.r28) ∧ 2 ≤ sv d.v.su.r28 ∧ nc = 2 + 2 * wRn d.v.su.r28 + 0
    exact ⟨h6 h10, by omega, by rw [hnc, w0_of (by omega), Nat.add_zero]⟩
  · rw [iteS_pos rfl (afterTail_k _)]
    exact after_tail h31 h56 hnc

theorem afterPrime_eq (d : D) : afterPrime p L g w d =
    D.iteS (scmpi .lt .s d.v.su.r28 2)
      (afterWarm p L g w (D.mk' d.site
        { d.v with slot := i32 2, par := i32 1, r56 := addi d.v.su.r28 (-2) }))
      (pgEnter p L g (D.mk' d.site
        { d.v with
          slot := i32 2
          par := i32 1
          r56 := addi d.v.su.r28 (-2)
          rnd := i32 0
          bq1 := d.v.bq0 }) .warm 0) := rfl

theorem afterWarm_k (d : D) : (afterWarm p L g w d).k = 0 := by
  rw [afterWarm_eq]

/-- **After the first block**: the warm rounds, or as after the warm rounds. -/
theorem after_prime {d : D} {nc : Nat} (h31 : d.v.su.r31 = addi d.v.su.r28 (-1))
    (hnc : nc = 2) : AfterBlk (p := p) (L := L) (g := g) d (afterPrime p L g w d) nc := by
  rw [afterPrime_eq]
  by_cases hc : sv d.v.su.r28 < 2
  · have hc' : scmpi .lt .s d.v.su.r28 2 = true := by
      rw [scmpi_lt_s _ (by decide) (by decide)]; exact decide_eq_true hc
    rw [iteS_pos hc' (afterWarm_k _)]
    refine afterBlk_of (after_warm h31 rfl ?_ fun h => absurd (show 10 < sv d.v.su.r28 from h)
      (by omega)) rfl rfl rfl
    show nc = 2 + 2 * w0 d.v.su.r28
    rw [hnc, w0]; simp [hc]
  · have hc' : scmpi .lt .s d.v.su.r28 2 = false := by
      rw [scmpi_lt_s _ (by decide) (by decide)]; exact decide_eq_false hc
    rw [iteS_neg hc' (pgEnter_k _ _ _)]
    have hB : RoundsB (some .warm) 0 { d.v with
        slot := i32 2
        par := i32 1
        r56 := addi d.v.su.r28 (-2)
        rnd := i32 0
        bq1 := d.v.bq0 } nc :=
      ⟨0, rfl, show 2 ≤ sv d.v.su.r28 by omega,
        show 0 < wRn d.v.su.r28 from wRn_pos (by omega), by simp [hnc]⟩
    exact after_pg d.site _ rfl rfl rfl rfl h31 hB

theorem warmEnd_eq (d : D) : warmEnd p L g w d =
    D.iteS (scmp .ne .b (addi d.v.rnd 1) (warmRounds d.v))
      (pgEnter p L g (D.mk' d.site (roundV d.v)) .warm 0)
      (afterWarm p L g w (D.mk' d.site (roundV d.v))) := rfl

/-- **After a warm round's V half**: the next warm round, or the end of the warm rounds. -/
theorem warm_end {d : D} {nc r : Nat} (h31 : d.v.su.r31 = addi d.v.su.r28 (-1))
    (h56 : d.v.r56 = addi d.v.su.r28 (-2))
    (hr : d.v.rnd = W r) (h2 : 2 ≤ sv d.v.su.r28) (hlt : r < wRn d.v.su.r28)
    (hnc : nc = 2 + 2 * r + 2) :
    AfterBlk (p := p) (L := L) (g := g) d (warmEnd p L g w d) nc := by
  have h9 := wRn_le d.v.su.r28
  have ha : addi d.v.rnd 1 = W (r + 1) := by rw [hr]; exact addi1_W (by omega)
  have hrv : (roundV d.v).rnd = W (r + 1) := ha
  rw [warmEnd_eq, ha, warmRounds_eq h31, scmp_ne_b_W (by omega) (by omega)]
  by_cases hc : r + 1 = wRn d.v.su.r28
  · rw [iteS_neg (decide_eq_false (not_not.mpr hc)) (afterWarm_k _)]
    refine afterBlk_of (after_warm h31 h56 ?_ fun _ => ?_) rfl rfl rfl
    · show nc = 2 + 2 * w0 d.v.su.r28
      rw [hnc, w0_of h2]; omega
    · show (roundV d.v).rnd = W (wRn d.v.su.r28)
      rw [hrv, hc]
  · rw [iteS_pos (decide_eq_true hc) (pgEnter_k _ _ _)]
    have hB : RoundsB (some .warm) 0 (roundV d.v) nc :=
      ⟨r + 1, hrv, show 2 ≤ sv d.v.su.r28 from h2, show r + 1 < wRn d.v.su.r28 by omega,
        by simp [hnc]; omega⟩
    exact after_pg d.site _ rfl rfl rfl h56 h31 hB

theorem steadyEnd_eq (d : D) : steadyEnd p L g d =
    D.iteS (scmp .lt .s (addi d.v.rnd 1) d.v.su.r31)
      (pgEnter p L g (D.mk' d.site (roundV d.v)) .steady 0)
      (passStart p L g true (D.mk' d.site (roundV d.v))) := rfl

/-- **After a steady round's V half**: the next steady round, or the second pass. -/
theorem steady_end {d : D} {nc r : Nat} (h31 : d.v.su.r31 = addi d.v.su.r28 (-1))
    (h56 : d.v.r56 = addi d.v.su.r28 (-2))
    (hr : d.v.rnd = W r) (hle : wRn d.v.su.r28 ≤ r) (hlt : (r : Int) < sv (addi d.v.su.r28 (-1)))
    (hnc : nc = 2 + 2 * w0 d.v.su.r28 + 2 * (r - wRn d.v.su.r28) + 2) :
    AfterBlk (p := p) (L := L) (g := g) d (steadyEnd p L g d) nc := by
  have hs := sv_spec (addi d.v.su.r28 (-1))
  have ha : addi d.v.rnd 1 = W (r + 1) := by rw [hr]; exact addi1_W (by omega)
  have hrv : (roundV d.v).rnd = W (r + 1) := ha
  have hsv : sv (W (r + 1)) = (r + 1 : Nat) := sv_W (by omega)
  rw [steadyEnd_eq, ha, scmp_lt_s, hsv, h31]
  by_cases hc : ((r + 1 : Nat) : Int) < sv (addi d.v.su.r28 (-1))
  · rw [iteS_pos (decide_eq_true hc) (pgEnter_k _ _ _)]
    have hB : RoundsB (some .steady) 0 (roundV d.v) nc :=
      ⟨r + 1, hrv, show wRn d.v.su.r28 ≤ r + 1 by omega,
        show ((r + 1 : Nat) : Int) < sv (addi d.v.su.r28 (-1)) from hc, by simp [hnc]; omega⟩
    exact after_pg d.site _ rfl rfl rfl h56 h31 hB
  · rw [iteS_neg (decide_eq_false hc) (passStart_k _ _)]
    refine .inr ⟨d.site, roundV d.v, rfl, rfl, rfl, ?_⟩
    have key : ∀ (a b c : Nat) (S : Int), b ≤ r → (r : Int) < S → ¬ ((r + 1 : Nat) : Int) < S →
        2 + 2 * a + 2 * (r - b) + 2 = 2 + 2 * a + 2 * (S - b).toNat := by
      intro a b c S h1 h2 h3; omega
    rw [hnc, pkts]
    exact key _ _ 0 _ hle hlt hc

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
