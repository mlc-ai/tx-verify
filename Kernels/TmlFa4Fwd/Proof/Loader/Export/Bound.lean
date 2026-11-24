-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.Bound
public import Kernels.TmlFa4Fwd.Proof.LdWarp.Fits
public import Lemmas.Flow.Counter32
public import Lemmas.Tmem.TmemPairSize
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader warps' events are bounded (G1)

A loader lane runs through four regions (`reg`): the first scheduler pass with the request's
reads, the tile's blocks, the second scheduler pass, the drain. Inside a region the sites are
ranked in the order of the code (`lr`). A block's sites are ranked above its period and round:
the prime block, the warm rounds and the steady rounds above the round counter `rnd`, which
the end of a round increments; the reference invariant says the round is below `2 ^ 31`, so it
does not wrap (`rnd_room`). The rank of a state over all regions is `gr`.

Every transition moves to a larger rank, fires a scan shuffle that stays in its scheduler pass,
or is a failed poll that keeps the state (`succ_rank`). So the measure (`measure`) is, in a
scheduler pass, the thread's shuffles above the rank, and in the blocks and the drain the rank,
each region above the bound of the one before it; the bounds of the passes are the reference
invariant's (`Epilogue.fits_coll_le_all`, and in the second pass the blocks' packets of 32
shuffles each, `pkts_le`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

/-! ### Ranks -/

/-- The rank of a scan's first site in its pass. -/
def sb : Epilogue.Scan → Nat
  | .first => 1 | .loop => 9 | .second => 0 | .loop2 => 8

/-- The rank of a period's first site, above the round counter `t`. -/
def perBase (per : Per) (t : BitVec 64) : Nat :=
  match per with
  | .prime => 0
  | .warm => 256 + (r32 t).toNat * 256
  | .steady => 2 ^ 41 + 256 + (r32 t).toNat * 256

/-- The offset of a block's V half. -/
abbrev H (v : Bool) : Nat := if v then 120 else 0

/-- The rank of TMA group `t`'s first site. -/
def tBase (t : Fin 7) (r : BitVec 64) : Nat :=
  if t.val < 4 then 81 + 7 * t.val
  else if t.val < 6 then perBase .warm r + 81 + 7 * (t.val - 4)
  else 2 ^ 41

/-- The rank of a block's site, with round counter `t`. -/
def pb (s : Site) (t : BitVec 64) : Nat :=
  match s with
  | .pgLd per it => perBase per t + 3 * it.val
  | .pgSt per it => perBase per t + 3 * it.val + 1
  | .rwSt per it => perBase per t + 3 * it.val + 2
  | .slot per v => perBase per t + 6 + H v
  | .ptP per v it => perBase per t + 7 + 3 * it.val + H v
  | .ptR per v it => perBase per t + 8 + 3 * it.val + H v
  | .ptS per v it => perBase per t + 9 + 3 * it.val + H v
  | .lw per v h => perBase per t + 13 + 33 * h.val + H v
  | .xl per v i => perBase per t + 14 + 4 * i.val + (if 8 ≤ i.val then 1 else 0) + H v
  | .xh per v i => perBase per t + 15 + 4 * i.val + (if 8 ≤ i.val then 1 else 0) + H v
  | .cp per v i c =>
    perBase per t + 16 + c.val + 4 * i.val + (if 8 ≤ i.val then 1 else 0) + H v
  | .commit per v => perBase per t + 79 + H v
  | .arrive per v => perBase per t + 80 + H v
  | .tw tt => tBase tt t
  | .te tt j => tBase tt t + 1 + 2 * j.val
  | .ta tt => tBase tt t + 2
  | .tc tt c => tBase tt t + 4 + 2 * c.val
  | _ => 0

/-- **The rank of a state inside its region.** -/
def lr (d : D) : Nat :=
  match d.site with
  | .setmax => 0
  | .word k => sb k
  | .down k => sb k + 1
  | .up k j => sb k + 2 + j.val
  | .total k => sb k + 7
  | .vote l => if l then 16 else 17
  | .pre l => if l then 17 else 18
  | .tiles l => if l then 18 else 19
  | .q0 => 20
  | .q1 => 21
  | .uk => 22
  | .dw k => k.val
  | .dq => 3
  | .de => 4
  | .da => 5
  | .exit => 6
  | s => 2 * pb s d.v.rnd + d.k.val

/-- **The region of a site**: the first pass and the request's reads, the blocks, the second
pass, the drain. -/
def reg (s : Site) : Nat :=
  match lc s with
  | .early | .p1 | .req => 0
  | .blk => 1
  | .p2 => 2
  | .drain => 3

/-- The rank of a region's first state. -/
def gbase : Nat → Nat
  | 0 => 0 | 1 => 64 | 2 => 2 ^ 44 + 64 | _ => 2 ^ 44 + 128

/-- **The rank of a state.** -/
def gr (d : D) : Nat := gbase (reg d.site) + lr d

theorem r32_lt (t : BitVec 64) : (r32 t).toNat < 2 ^ 32 := by
  simp only [r32, truncBits, BitVec.toNat_ofNat]; omega

theorem perBase_le (per : Per) (t : BitVec 64) : perBase per t + 256 ≤ 2 ^ 41 + 2 ^ 40 + 512 := by
  have := r32_lt t
  cases per <;> simp only [perBase] <;> omega

theorem warm_le (t : BitVec 64) : perBase .warm t ≤ 2 ^ 40 := by
  have := r32_lt t
  simp only [perBase]
  omega

theorem tBase_le (tt : Fin 7) (t : BitVec 64) : tBase tt t ≤ 2 ^ 41 := by
  have := warm_le t
  unfold tBase
  split_ifs <;> omega

theorem pb_lt (s : Site) (t : BitVec 64) : pb s t < 2 ^ 42 := by
  cases s <;> simp only [pb, H]
  all_goals first
    | omega
    | (have := perBase_le ‹Per› t; have := ‹Fin 16›.isLt; (try split_ifs) <;> omega)
    | (have := perBase_le ‹Per› t; have := ‹Fin 2›.isLt; (try split_ifs) <;> omega)
    | (have := perBase_le ‹Per› t; (try split_ifs) <;> omega)
    | (have := tBase_le ‹Fin 7› t; have := ‹Fin 3›.isLt; omega)
    | (have := tBase_le ‹Fin 7› t; have := ‹Fin 2›.isLt; omega)
    | (have := tBase_le ‹Fin 7› t; omega)

/-- The rank of a state is below its region's bound. -/
theorem lr_lt (d : D) : lr d < (if reg d.site = 1 then 2 ^ 43 else 64) := by
  obtain ⟨s, v, k⟩ := d
  have hk := k.isLt
  have hp := pb_lt s v.rnd
  cases s <;> simp only [lr, reg, lc]
  all_goals first
    | (simp <;> omega)
    | (cases ‹Epilogue.Scan› <;> simp [sb, Epilogue.Scan.late] <;> omega)
    | (cases ‹Bool› <;> simp)

/-! ### The ranks of the composite successors -/

variable {p : Params} {L : Launch} {m : Mem0} {g w : Nat}

/-- The rank of a block state with site `s`, round counter `t` and sub-step 0. -/
theorem gr_blk {s : Site} {v : V} (hs : lc s = .blk) : gr (D.mk' s v) = 64 + 2 * pb s v.rnd := by
  cases s <;> simp only [lc] at hs <;> first
    | (simp at hs; done)
    | (split at hs <;> simp at hs; done)
    | simp [gr, reg, lc, lr, gbase]

theorem gr_passStart_true (d : D) : 2 ^ 44 + 64 ≤ gr (passStart p L g true d) := by
  simp only [passStart, D.ite, ↓reduceIte]
  split <;> simp [gr, reg, lc, lr, gbase, sb, Epilogue.Scan.late]

theorem gr_passStart_false (d : D) : 1 ≤ gr (passStart p L g false d) := by
  simp only [passStart, D.ite, Bool.false_eq_true, ↓reduceIte]
  split <;> simp [gr, reg, lc, lr, gbase, sb, Epilogue.Scan.late]

theorem gr_pgEnter (d : D) (per : Per) (it : Fin 2) :
    64 + 2 * (perBase per d.v.rnd + 3 * it.val) ≤ gr (pgEnter p L g d per it) := by
  simp only [pgEnter, D.iteS]
  split
  · rw [gr_blk (by simp [lc])]; simp [pb]
  · rw [gr_blk (by simp [lc])]; simp [pb]

theorem mk_eta {x : D} (h : x.k = 0) : (⟨x.site, x.v, 0⟩ : D) = x := by
  cases x; simp_all

theorem pgEnter_rnd (d : D) (per : Per) (it : Fin 2) :
    (pgEnter p L g d per it).v.rnd = d.v.rnd := by
  simp only [pgEnter, D.iteS]; split <;> rfl

theorem gr_afterTail (d : D) : 64 + 2 * (2 ^ 41 + 256) ≤ gr (afterTail p L g d) := by
  simp only [afterTail, D.iteS]
  split
  · rw [mk_eta (passStart_k ..)]
    exact le_trans (by norm_num) (gr_passStart_true _)
  · rw [mk_eta (pgEnter_k ..)]
    refine le_trans ?_ (gr_pgEnter _ .steady 0)
    simp only [perBase]
    omega

theorem gr_afterWarm (d : D) : 64 + 2 * 2 ^ 41 ≤ gr (afterWarm p L g w d) := by
  simp only [afterWarm, D.iteS]
  split
  · rw [mk_eta (by unfold afterTail D.iteS; rfl)]
    exact le_trans (by norm_num) (gr_afterTail _)
  · rw [gr_blk (by simp [lc])]; simp [pb, tBase]

theorem gr_afterPrime (d : D) : 64 + 2 * 256 ≤ gr (afterPrime p L g w d) := by
  simp only [afterPrime, D.iteS]
  split
  · rw [mk_eta (afterWarm_k ..)]
    exact le_trans (by norm_num) (gr_afterWarm _)
  · rw [mk_eta (pgEnter_k ..)]
    refine le_trans ?_ (gr_pgEnter _ .warm 0)
    simp [perBase, show (r32 (i32 0)).toNat = 0 from rfl]

/-- The warm loop's counter after a round, when it has room. -/
theorem perBase_round (per : Per) {v : V} (h : (r32 v.rnd).toNat + 1 < 2 ^ 32)
    (hp : per ≠ .prime) : perBase per (roundV v).rnd = perBase per v.rnd + 256 := by
  cases per
  · exact absurd rfl hp
  all_goals simp only [perBase, r32_addi1 h]; ring

theorem gr_warmEnd (d : D) (h : (r32 d.v.rnd).toNat + 1 < 2 ^ 32) :
    64 + 2 * (perBase .warm d.v.rnd + 256) ≤ gr (warmEnd p L g w d) := by
  have := warm_le d.v.rnd
  simp only [warmEnd, D.iteS]
  split
  · rw [mk_eta (pgEnter_k ..)]
    refine le_trans ?_ (gr_pgEnter _ .warm 0)
    rw [perBase_round .warm h (by simp)]
    omega
  · rw [mk_eta (afterWarm_k ..)]
    refine le_trans ?_ (gr_afterWarm _)
    omega

theorem gr_steadyEnd (d : D) (h : (r32 d.v.rnd).toNat + 1 < 2 ^ 32) :
    64 + 2 * (perBase .steady d.v.rnd + 256) ≤ gr (steadyEnd p L g d) := by
  simp only [steadyEnd, D.iteS]
  split
  · rw [mk_eta (pgEnter_k ..)]
    refine le_trans ?_ (gr_pgEnter _ .steady 0)
    rw [perBase_round .steady h (by simp)]
    simp
  · rw [mk_eta (passStart_k ..)]
    refine le_trans ?_ (gr_passStart_true _)
    have := perBase_le .steady d.v.rnd
    generalize perBase .steady d.v.rnd = x at this ⊢
    norm_num at this ⊢
    omega

theorem gr_groupEnd (d : D) (t : Fin 7) :
    64 + 2 * (tBase t d.v.rnd + 7) ≤ gr (groupEnd p L g d t) := by
  have := warm_le d.v.rnd
  fin_cases t
  all_goals simp only [groupEnd]
  case «6» => exact le_trans (by simp [tBase]) (gr_afterTail _)
  all_goals rw [gr_blk (by simp [lc])]
  all_goals simp [pb, tBase, perBase, H]

/-! ### The scan's successors stay in their pass or go to the drain -/

theorem scanExit_site (late : Bool) (d : D) (gx cur : BitVec 64) :
    (scanExit p late d gx cur).site = .dw 0 ∨
      reg (scanExit p late d gx cur).site = reg (.vote late) := by
  simp only [scanExit, D.ite]
  split
  · left; rfl
  · right; rfl

theorem loopHead_site (late : Bool) (d : D) (grp acc : BitVec 64) :
    (loopHead p L g late d grp acc).site = .dw 0 ∨
      reg (loopHead p L g late d grp acc).site = reg (.vote late) := by
  simp only [loopHead, D.ite]
  split
  · exact scanExit_site ..
  · right
    split <;> cases late <;> rfl

theorem afterTotal_site (k : Epilogue.Scan) (d : D) (x : BitVec 64) :
    (afterTotal p L g k d x).site = .dw 0 ∨
      reg (afterTotal p L g k d x).site = reg (.total k) := by
  have hv : reg (.vote k.late) = reg (.total k) := by cases k <;> rfl
  rw [← hv]
  unfold afterTotal
  cases k <;> simp only [D.ite] <;> split
  all_goals first | exact scanExit_site .. | exact loopHead_site ..

theorem afterTiles_site {d d' : D} {x : BitVec 64} (h : afterTiles p L g d x = some d') :
    d' = D.mk' .q0 d'.v ∨ d' = D.mk' (.dw 0) d'.v := by
  simp only [afterTiles] at h
  split at h
  · split at h
    · simp only [Option.some.injEq, D.ite] at h
      subst h
      split
      · left; rfl
      · right; rfl
    · cases h
  · cases h

/-! ### The ranks of the steps -/

/-- Compute the ranks of concrete sites. -/
macro "rk_simp" : tactic => `(tactic|
  simp [gr, reg, lc, lr, gbase, sb, pb, perBase, tBase, H, Epilogue.Scan.late])

/-- The ends of a warm and a steady round, where the round counter steps. -/
def Site.roundEnd : Site → Bool
  | .arrive .warm true | .arrive .steady true => true
  | _ => false

/-- **Every transition of a loader lane moves to a larger rank, fires a scan shuffle that stays
in its scheduler pass, or is a failed poll** that keeps the state, when the round counter has
room at a round's end. -/
theorem succ_rank {d d' : D} {e : Event} (h : succ p L g w d e = some (some d'))
    (ht : d.site.roundEnd = true → (r32 d.v.rnd).toNat + 1 < 2 ^ 32) :
    gr d < gr d' ∨
      (reg d'.site = reg d.site ∧ (reg d.site = 0 ∨ reg d.site = 2) ∧
        Execution.isShfl e = true) ∨
      (d' = d ∧ e.counts = false) := by
  obtain ⟨pc, kind⟩ := e
  obtain ⟨s, v, k⟩ := d
  have hk := k.isLt
  cases s with
  | total kk =>
    cases kind <;> simp only [succ, reduceCtorEq] at h
    unfold word32 at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      rcases afterTotal_site (p := p) (L := L) (g := g) kk ⟨.total kk, v, k⟩ ‹BitVec 64› with
        h1 | h1
      · left
        simp only [gr, h1]
        cases kk <;> simp [reg, lc, lr, gbase, sb, Epilogue.Scan.late] <;> omega
      · right; left
        refine ⟨h1, ?_, rfl⟩
        cases kk <;> simp [reg, lc, Epilogue.Scan.late]
    · cases h
  | setmax =>
    left
    simp only [succ, Option.some.injEq] at h
    subst h
    exact lt_of_lt_of_le (by simp [gr, reg, lc, lr, gbase]) (gr_passStart_false _)
  | down kk =>
    left
    cases kind <;> simp only [succ, reduceCtorEq] at h
    unfold word32 at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      cases kk <;> rk_simp
    · cases h
  | up kk j =>
    left
    cases kind <;> simp only [succ, reduceCtorEq] at h
    unfold word32 at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      fin_cases j <;> cases kk <;> rk_simp
    · cases h
  | pre l =>
    left
    cases kind <;> simp only [succ, reduceCtorEq] at h
    unfold word32 at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      cases l <;> rk_simp
    · cases h
  | tiles l =>
    left
    cases kind <;> simp only [succ, reduceCtorEq] at h
    cases l
    · simp only [Bool.false_eq_true, ↓reduceIte] at h
      split at h
      · obtain ⟨_, h1, h2⟩ := Option.map_eq_some_iff.mp h
        cases h2
        rcases afterTiles_site h1 with h3 | h3 <;> rw [h3] <;> rk_simp
      · cases h
    · simp only [↓reduceIte] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        rk_simp
      · cases h
  | word kk | q0 | q1 =>
    left
    cases kind <;> simp only [succ, reduceCtorEq] at h
    split at h
    · unfold word32 at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        first | (cases kk <;> rk_simp) | rk_simp
      · cases h
    · cases h
  | uk =>
    left
    cases kind <;> simp only [succ, reduceCtorEq] at h
    split at h
    · unfold word32 at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        refine lt_of_lt_of_le ?_ (gr_pgEnter _ .prime 0)
        rk_simp
      · cases h
    · cases h
  | vote l =>
    left
    cases kind <;> simp only [succ, reduceCtorEq] at h
    simp only [Option.some.injEq] at h
    subst h
    simp only [D.ite]
    cases l <;> split <;> rk_simp
  | pgLd per it | ptP per v it | ptR per v it =>
    left
    cases kind <;> simp only [succ, reduceCtorEq] at h
    split at h
    · unfold word32 at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        cases per <;> rk_simp <;> omega
      · cases h
    · cases h
  | pgSt per it | commit per v =>
    left
    simp only [succ, Option.some.injEq] at h
    subst h
    cases per <;> rk_simp <;> omega
  | rwSt per it =>
    left
    simp only [succ] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      refine lt_of_lt_of_le ?_ (gr_pgEnter _ per 1)
      rename_i hit
      cases per <;> rk_simp <;> omega
    · simp only [Option.some.injEq] at h
      subst h
      rename_i hit
      have : it.val = 1 := by omega
      cases per <;> rk_simp <;> omega
  | slot per v | tw per =>
    cases kind <;> simp only [succ, reduceCtorEq] at h
    rename_i ok _ _
    simp only [Option.some.injEq] at h
    subst h
    cases ok
    · right; right; exact ⟨by simp, rfl⟩
    · left
      simp only [↓reduceIte]
      first | (cases per <;> rk_simp <;> omega) | (rk_simp <;> split_ifs <;> omega)
  | ptS per v it =>
    left
    simp only [succ] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      cases per <;> rk_simp <;> omega
    · simp only [Option.some.injEq] at h
      subst h
      unfold pkStart
      rename_i hit
      have : it.val = 1 := by omega
      split
      · subst_vars; rk_simp <;> omega
      · split <;> cases per <;> rk_simp <;> omega
  | lw per v hh =>
    left
    cases kind <;> simp only [succ, reduceCtorEq] at h
    split at h
    · unfold word32 at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        split
        · rename_i hk0
          cases per <;> rk_simp <;> omega
        · rename_i hk0
          have : k.val = 1 := by omega
          cases per <;> rk_simp <;> split_ifs <;> omega
      · cases h
    · cases h
  | xl per v i | xh per v i =>
    left
    cases kind <;> simp only [succ, reduceCtorEq] at h
    unfold word32 at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      cases per <;> rk_simp <;> split_ifs <;> omega
    · cases h
  | cp per v i c =>
    left
    simp only [succ] at h
    split at h <;> (try split at h) <;> (try split at h) <;>
      simp only [Option.some.injEq] at h <;> subst h <;>
      cases per <;> rk_simp <;> (try simp only [Fin.val_add]) <;> split_ifs <;> omega
  | arrive per v =>
    left
    simp only [succ, Option.some.injEq] at h
    subst h
    cases per <;> cases v
    · simp only [afterArrive, D.ite]; split <;> rk_simp <;> omega
    · exact lt_of_lt_of_le (by rk_simp; omega) (gr_afterPrime _)
    · simp only [afterArrive, D.ite]; split <;> rk_simp <;> omega
    · have ht' := ht rfl
      refine lt_of_lt_of_le ?_ (gr_warmEnd _ ht')
      rk_simp
      omega
    · simp only [afterArrive]; rk_simp; omega
    · have ht' := ht rfl
      refine lt_of_lt_of_le ?_ (gr_steadyEnd _ ht')
      rk_simp
      omega
  | te t j =>
    left
    cases kind <;> simp only [succ, reduceCtorEq] at h
    simp only [Option.some.injEq] at h
    subst h
    have := tBase_le t v.rnd
    split
    · fin_cases j <;> simp only [teElected] <;> (try split) <;> rk_simp <;> omega
    · fin_cases j <;> simp only [teNext]
      · rk_simp; omega
      · rk_simp; omega
      · refine lt_of_lt_of_le ?_ (gr_groupEnd _ t)
        split <;> rk_simp <;> omega
  | ta t =>
    left
    simp only [succ, Option.some.injEq] at h
    subst h
    rk_simp
    split_ifs <;> omega
  | tc t c =>
    left
    simp only [succ] at h
    split at h <;> simp only [Option.some.injEq] at h <;> subst h
    · rk_simp; omega
    · refine lt_of_lt_of_le ?_ (gr_groupEnd _ t)
      have : c.val = 1 := by omega
      rk_simp; omega
  | dw kk =>
    cases kind <;> simp only [succ, reduceCtorEq] at h
    rename_i ok _ _
    simp only [Option.some.injEq] at h
    subst h
    cases ok
    · right; right; exact ⟨by simp, rfl⟩
    · left
      simp only [↓reduceIte]
      fin_cases kk <;> simp only [dwNext, D.ite] <;> (try split) <;> rk_simp
  | dq =>
    cases kind <;> simp only [succ, reduceCtorEq] at h
    rename_i ok _ _
    simp only [Option.some.injEq] at h
    subst h
    cases ok
    · right; right; exact ⟨by simp, rfl⟩
    · left; rk_simp
  | de =>
    left
    cases kind <;> simp only [succ, reduceCtorEq] at h
    simp only [Option.some.injEq] at h
    subst h
    split <;> rk_simp
  | da =>
    left
    simp only [succ, Option.some.injEq] at h
    subst h
    rk_simp
  | exit => simp [succ] at h

/-! ### The measure -/

/-- The bound of the shuffles in the first pass, and in the second (above the blocks' packets of
32 shuffles each). -/
def C1 (p : Params) : Nat := 14 * p.batch + 27
def C2 (p : Params) : Nat := 32 * (2 ^ 32 + 20) + C1 p

/-- The measure of a region's first state. -/
def base (p : Params) : Nat → Nat
  | 0 => 0
  | 1 => (C1 p + 1) * 64
  | 2 => (C1 p + 1) * 64 + 2 ^ 44
  | _ => (C1 p + 1) * 64 + 2 ^ 44 + (C2 p + 1) * 64

/-- Whether a region is a scheduler pass. -/
def pass (r : Nat) : Bool := r = 0 || r = 2

/-- **The measure of a state** past `ns` shuffles. -/
def measure (p : Params) (d : D) (ns : Nat) : Nat :=
  base p (reg d.site) + (if pass (reg d.site) then ns * 64 else 0) + lr d

theorem reg_le (s : Site) : reg s ≤ 3 := by
  unfold reg; split <;> omega

/-- A state's measure is below its region's successor's first measure. -/
theorem measure_lt_next (d : D) (ns : Nat) (h0 : reg d.site = 0 → ns ≤ C1 p)
    (h2 : reg d.site = 2 → ns ≤ C2 p) (h3 : reg d.site < 3) :
    measure p d ns < base p (reg d.site + 1) := by
  have hl := lr_lt d
  have hr := h3
  unfold measure
  generalize reg d.site = r at hl h0 h2 hr ⊢
  interval_cases r <;> simp only [base, pass] at hl h0 h2 ⊢ <;> simp at hl h0 h2 ⊢
  · have : ns * 64 ≤ C1 p * 64 := Nat.mul_le_mul_right 64 h0
    omega
  · omega
  · have : ns * 64 ≤ C2 p * 64 := Nat.mul_le_mul_right 64 h2
    omega

theorem base_le_measure (d : D) (ns : Nat) : base p (reg d.site) ≤ measure p d ns := by
  unfold measure; omega

theorem base_mono {a b : Nat} (h : a ≤ b) (hb : b ≤ 3) : base p a ≤ base p b := by
  interval_cases b <;> interval_cases a <;> simp only [base] <;> omega

/-- **The measure never decreases along a transition, and increases at every counted event**,
when the round counter has room at a round's end and the shuffles are within the passes'
bounds. -/
theorem measure_step {d d' : D} {e : Event} {ns ns' : Nat}
    (h : succ p L g w d e = some (some d'))
    (ht : d.site.roundEnd = true → (r32 d.v.rnd).toNat + 1 < 2 ^ 32)
    (h0 : reg d.site = 0 → ns ≤ C1 p) (h2 : reg d.site = 2 → ns ≤ C2 p)
    (hn : ns' = ns + if Execution.isShfl e then 1 else 0) :
    measure p d ns ≤ measure p d' ns' ∧ (e.counts = true → measure p d ns < measure p d' ns') := by
  have hl := lr_lt d
  have hl' := lr_lt d'
  have hr := reg_le d.site
  have hr' := reg_le d'.site
  have hns : ns ≤ ns' := by split at hn <;> omega
  have hle : ns * 64 ≤ ns' * 64 := Nat.mul_le_mul_right 64 hns
  rcases succ_rank h ht with hg | ⟨hreg, hpass, hsh⟩ | ⟨rfl, hc⟩
  · -- a larger rank: a later region, or the same region and a larger rank inside it
    suffices measure p d ns < measure p d' ns' from ⟨this.le, fun _ => this⟩
    unfold gr at hg
    by_cases hrr : reg d.site < reg d'.site
    · have h1 := measure_lt_next (p := p) d ns h0 h2 (by omega)
      have h3 := base_mono (p := p) (show reg d.site + 1 ≤ reg d'.site by omega) hr'
      have h4 := base_le_measure (p := p) d' ns'
      omega
    · have heq : reg d'.site = reg d.site := by
        generalize reg d.site = a at hg hl hrr hr
        generalize reg d'.site = b at hg hl' hrr hr'
        interval_cases a <;> interval_cases b <;> simp_all [gbase] <;> omega
      unfold measure
      rw [heq] at hg ⊢
      split <;> omega
  · simp only [hsh, ↓reduceIte] at hn
    subst hn
    have hp' : pass (reg d.site) = true := by rcases hpass with h | h <;> simp [pass, h]
    have hl0 : lr d < 64 := by rcases hpass with h | h <;> simpa [h] using hl
    have hl0' : lr d' < 64 := by rcases hpass with h | h <;> simpa [hreg, h] using hl'
    unfold measure
    rw [hreg, hp']
    simp only [↓reduceIte, Nat.add_mul, Nat.one_mul]
    omega
  · rw [hc]
    unfold measure
    simp only [Bool.false_eq_true, false_implies, and_true]
    split <;> omega

/-! ### The bounds from the reference invariant -/

/-- **The packets of a tile are at most `2 ^ 32 + 20`.** -/
theorem pkts_le (b : BitVec 64) : pkts b ≤ 2 ^ 32 + 20 := by
  have h1 : wRn b ≤ 9 := by unfold wRn; omega
  have h2 : w0 b ≤ 9 := by unfold w0; split <;> omega
  have h3 := toSigned32_lt (addi b (-1))
  unfold pkts
  simp only [sv] at h3 ⊢
  omega

/-- **The round counter has room at a round's end**: the reference invariant says the round is
below the warm rounds (at most 9) or below the tile's blocks (a signed word). -/
theorem rnd_room {d : D} {ns nv nc : Nat} (hF : LFits p L g d ns nv nc)
    (hs : d.site.roundEnd = true) : (r32 d.v.rnd).toNat + 1 < 2 ^ 32 := by
  obtain ⟨s, v, k⟩ := d
  have hW : ∀ r, r + 1 < 2 ^ 31 → (r32 (W r)).toNat + 1 < 2 ^ 32 := by
    intro r hr
    simp only [r32, W, truncBits, BitVec.toNat_ofNat]
    omega
  cases s <;> simp only [Site.roundEnd] at hs
  all_goals first | (simp at hs; done) | skip
  rename_i per v'
  cases per <;> cases v' <;> simp only [Site.roundEnd, Bool.false_eq_true] at hs
  all_goals
    simp only [LFits, lc] at hF
    obtain ⟨-, -, -, ⟨-, hR⟩, -⟩ := hF
    simp only [RoundsB, bc, inBlk, ↓reduceIte] at hR
  · obtain ⟨r, hr, -, hlt, -⟩ := hR
    simp only at hr ⊢
    rw [hr]
    have : wRn v.su.r28 ≤ 9 := by unfold wRn; omega
    exact hW r (by omega)
  · obtain ⟨r, hr, -, hlt, -⟩ := hR
    simp only at hr ⊢
    rw [hr]
    have := toSigned32_lt (addi v.su.r28 (-1))
    simp only [sv] at hlt
    exact hW r (by omega)

/-- **The shuffles of a pass are within its bound.** -/
theorem pass_bounds (hp : Pre p L m) {d : D} {ns nv nc : Nat} (hF : LFits p L g d ns nv nc) :
    (reg d.site = 0 → ns ≤ C1 p) ∧ (reg d.site = 2 → ns ≤ C2 p) := by
  unfold LFits at hF
  unfold reg C2 C1
  split at hF <;> rename_i hlc <;> simp only [hlc]
  · omega
  · have := Epilogue.fits_coll_le_all hp hF.2; omega
  · have := Epilogue.fits_coll_le_all hp hF.2.1; omega
  · simp
  · obtain ⟨h1, h2, -, h4⟩ := hF
    have := Epilogue.fits_coll_le_all hp h2
    have := pkts_le d.v.su.r28
    have : 32 * nc ≤ 32 * (2 ^ 32 + 20) := by omega
    omega
  · simp

/-- **The measure of a state that holds the reference values is bounded.** -/
theorem measure_le (hp : Pre p L m) {d : D} {ns nv nc : Nat} (hF : LFits p L g d ns nv nc) :
    measure p d ns ≤ base p 3 + 64 := by
  obtain ⟨h0, h2⟩ := pass_bounds hp hF
  have hr := reg_le d.site
  by_cases h3 : reg d.site = 3
  · have := lr_lt d
    unfold measure
    rw [h3] at this ⊢
    simp only [pass] at this ⊢
    simp at this ⊢
    omega
  · have h1 := measure_lt_next (p := p) d ns h0 h2 (by omega)
    have := base_mono (p := p) (show reg d.site + 1 ≤ 3 by omega) le_rfl
    omega

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
