-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LdWarp.RowMem
public import Kernels.TmlFa4Fwd.Proof.LdWarp.TileBlk
import Kernels.TmlFa4Fwd.Proof.LdWarp.Page
import Kernels.TmlFa4Fwd.Proof.LdWarp.RowAddr
import Kernels.TmlFa4Fwd.Proof.Lib.OutputFrame
import Lemmas.Flow.Arith32WordW
import Lemmas.Flow.WordBound
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The rows of a loader lane in numbers

At a block state with `nc` commits the lane's row of page round `it` is a row of block
`n - 1 - nc / 2` of the tile (`row0_num`), and the length of its rows is the used length less the
row group's first key (`len_num`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Loader

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

/-- The row group of a lane. -/
def grpOf (L : Launch) (g : Nat) : Nat := g % L.block / 8 % 8
/-- The row of a lane in a block, in page round 0. -/
def rowIn (L : Launch) (g : Nat) : Nat := grpOf L g + 8 * (g % L.block % 8)

private theorem lane_words : ∀ t < 512,
    add32 (andi (shru (BitVec.ofNat 64 t) 3) 7) (andi (shl (BitVec.ofNat 64 t) 3) 56) =
        W (t / 8 % 8 + 8 * (t % 8)) ∧
      Loader.or32 (andi (shru (BitVec.ofNat 64 t) 3) 7) (andi (shl (BitVec.ofNat 64 t) 3) 56) =
        W (t / 8 % 8 + 8 * (t % 8)) ∧
      andi (shru (BitVec.ofNat 64 t) 3) 7 = W (t / 8 % 8) := by
  decide +kernel

theorem addi_neg {a k : Nat} (hk : k ≤ a) (ha : a < 2 ^ 31) :
    addi (W a) (-(k : Int)) = W (a - k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [addi, i32, r32, truncBits, W, BitVec.toNat_ofNat, BitVec.toNat_add,
    BitVec.toNat_ofInt]
  omega

theorem or32_low {x y : Nat} (hx : x < 128) (hy : y % 128 = 0) (hlt : y < 2 ^ 32) :
    Loader.or32 (W x) (W y) = W (x + y) := by
  have h := toNat_or32_add (k := 7) (x := W x) (y := W y)
    (by rw [r32_W (by omega), toNat_W (by omega)]; exact hx)
    (by rw [r32_W hlt, toNat_W (by omega)]; exact hy)
  apply BitVec.eq_of_toNat_eq
  simp only [Loader.or32]
  rw [h, r32_W (by omega), r32_W hlt, toNat_W (by omega), toNat_W (by omega), toNat_W (by omega)]

/-- The block of a period. -/
def blkOfPer : Per → Blk
  | .prime => .prime
  | .warm => .warm
  | .steady => .steady

theorem bc_per {s : Site} {per : Per} (h : perOf s = some per) :
    bc s = some (blkOfPer per) := by
  cases s <;> simp only [perOf, reduceCtorEq, Option.some.injEq] at h
  all_goals first
    | (subst h; cases ‹Per› <;> rfl)
    | (simp only [bc]
       split at h
       · simp only [Option.some.injEq] at h
         subst h
         rename_i h4
         simp [h4, blkOfPer]
       · split at h
         · simp only [Option.some.injEq] at h
           subst h
           rename_i h4 h6
           simp [h4, h6, blkOfPer]
         · cases h)

set_option maxHeartbeats 1000000 in
/-- **The round of a block state**: its tile round, and the later blocks' words. -/
theorem blk_round {d : D} {ns nv nc b : Nat} {per : Per} (hb : d.site.blk = true)
    (hF : LFits p L g d ns nv nc) (hN : TileNum p L g d.v d.v.su b)
    (hn1 : 1 ≤ tileBlocks p b (Epilogue.assignedCoordinates p b (g / L.block)).1)
    (hn2 : tileBlocks p b (Epilogue.assignedCoordinates p b (g / L.block)).1 < 2 ^ 24)
    (hper : perOf d.site = some per) (hib : inBlk d.site ≤ 1) :
    nc % 2 = inBlk d.site ∧
      nc / 2 + 1 ≤ tileBlocks p b (Epilogue.assignedCoordinates p b (g / L.block)).1 ∧
      (per = .prime → nc / 2 = 0) ∧ (per ≠ .prime → 1 ≤ nc / 2 ∧ startWarm d.v =
        W (tileBlocks p b (Epilogue.assignedCoordinates p b (g / L.block)).1 - 1 - nc / 2)) := by
  obtain ⟨-, -, -, ⟨-, hR⟩, -, -, h56, -⟩ := lfits_blk_of hb hF
  have h28 := hN.r28
  generalize tileBlocks p b (Epilogue.assignedCoordinates p b (g / L.block)).1 = nn at *
  have hsv : sv d.v.su.r28 = nn := by rw [h28]; exact sv_W (by omega)
  have hsv1 : sv (addi d.v.su.r28 (-1)) = nn - 1 := by rw [sv_addi_neg1 _ (by omega), hsv]
  have hw : wRn d.v.su.r28 ≤ nn - 1 := by unfold wRn; rw [hsv1]; omega
  have hst : ∀ r, bc d.site ≠ some .prime → d.v.rnd = W r → r + 2 ≤ nn →
      startWarm d.v = W (nn - 1 - (r + 1)) := by
    intro r hne hr hle
    show sub32 d.v.r56 d.v.rnd = _
    rw [h56 hne, h28, hr, show (-2 : Int) = -((2 : Nat) : Int) from rfl,
      addi_neg (by omega) (by omega), sub32_W (by omega) (by omega)]
    exact congrArg W (by omega)
  have hbc := bc_per hper
  rw [hbc] at hR
  cases per <;> simp only [blkOfPer] at hR hbc
  · simp only [RoundsB] at hR
    exact ⟨by omega, by omega, fun _ => by omega, fun h => absurd rfl h⟩
  · simp only [RoundsB] at hR
    obtain ⟨r, hr, h2, hlt, hnc⟩ := hR
    have hle : r + 2 ≤ nn := by omega
    refine ⟨by omega, by omega, fun h => (by cases h), fun _ => ⟨by omega, ?_⟩⟩
    rw [hst r (by rw [hbc]; simp) hr hle]
    exact congrArg W (by omega)
  · simp only [RoundsB] at hR
    obtain ⟨r, hr, h2, hlt, hnc⟩ := hR
    rw [hsv1] at hlt
    have hle : r + 2 ≤ nn := by omega
    have hw0 : w0 d.v.su.r28 = wRn d.v.su.r28 := by
      unfold w0
      rw [ite_eq_right (by omega)]
    rw [hw0] at hnc
    refine ⟨by omega, by omega, fun h => (by cases h), fun _ => ⟨by omega, ?_⟩⟩
    rw [hst r (by rw [hbc]; simp) hr hle]
    exact congrArg W (by omega)

/-- The blocks of the tile of a CTA. -/
abbrev nBlk (p : Params) (L : Launch) (g b : Nat) : Nat :=
  tileBlocks p b (Epilogue.assignedCoordinates p b (g / L.block)).1

theorem nBlk_bound (hp : Pre p L m) {b : Nat} (hb : b < p.batch)
    (hlo : tilePrefix p b * p.heads ≤ g / L.block)
    (hhi : g / L.block < tilePrefix p (b + 1) * p.heads) :
    1 ≤ nBlk p L g b ∧ nBlk p L g b < 2 ^ 24 ∧ 128 * nBlk p L g b < p.kLength b + 128 := by
  obtain ⟨hv, -⟩ := Epilogue.assignedCoordinates_valid hp hlo hhi
  obtain ⟨-, h1, h2⟩ := hp.lengths b hb
  unfold nBlk tileBlocks
  omega

set_option maxHeartbeats 1000000 in
/-- **The row of a page round.** -/
theorem row0_num (hp : Pre p L m) {d : D} {ns nv nc b : Nat} {per : Per} (hb : d.site.blk = true)
    (hF : LFits p L g d ns nv nc) (hN : TileNum p L g d.v d.v.su b)
    (hper : perOf d.site = some per) (hib : inBlk d.site ≤ 1) (it : Fin 2) :
    (row0 p L g d.v per it).toNat =
      128 * (nBlk p L g b - 1 - nc / 2) + rowIn L g + 64 * it.val := by
  obtain ⟨n1, n2, n3⟩ := nBlk_bound hp hN.batch hN.lo hN.hi
  obtain ⟨h1, h2, h3, h4⟩ := blk_round hb hF hN n1 n2 hper hib
  have hk := (hp.lengths b hN.batch).2.2
  obtain ⟨-, -, -, -, ⟨v₀, hsu, -, -⟩, -, -, -⟩ := lfits_blk_of hb hF
  have ht : g % L.block < 512 := by rw [hp.block]; exact Nat.mod_lt _ (by decide)
  obtain ⟨w1, w2, -⟩ := lane_words _ ht
  have hrow : rowIn L g < 64 := by unfold rowIn grpOf; omega
  have hit : shl (i32 (it.val : Int)) 6 = W (64 * it.val) := by fin_cases it <;> decide
  have hit2 := it.isLt
  have h28 := hN.r28
  change d.v.su.r28 = W (nBlk p L g b) at h28
  have hc7 : ∀ a, a < 2 ^ 24 → shl (W a) 7 = W (a * 128) := fun a ha =>
    shl_W (k := 7) (by decide) (by omega)
  change nc / 2 + 1 ≤ nBlk p L g b at h2
  have h4' : per ≠ .prime → startWarm d.v = W (nBlk p L g b - 1 - nc / 2) := fun h => (h4 h).2
  clear h4
  generalize nBlk p L g b = nn at *
  have key : row0 p L g d.v per it = W (128 * (nn - 1 - nc / 2) + rowIn L g + 64 * it.val) := by
    cases per
    · have h0 := h3 rfl
      show add32 d.v.su.r35 (shl (i32 (it.val : Int)) 6) = _
      have hgt : scmpi .gt .s (W nn) 0 = true := by
        rw [scmpi_gt_s _ (by decide) (by decide), sv_W (by omega)]
        simp
        omega
      rw [hit, hsu, setup_r35, ← hsu, h28, hgt]
      simp only [sel, ↓reduceIte]
      rw [show (-1 : Int) = -((1 : Nat) : Int) from rfl, addi_neg (by omega) (by omega),
        hc7 _ (by omega)]
      rw [show add32 (andi (shru (tidW L g) 3) 7) (andi (shl (tidW L g) 3) 56) =
        W (rowIn L g) from w1, or32_low (by omega) (by omega) (by omega), add32_W (by omega)]
      exact congrArg W (by omega)
    · have h5 := h4' (by decide)
      show add32 (add32 (Loader.or32 (andi (shru (tidW L g) 3) 7) (andi (shl (tidW L g) 3) 56))
        (shl (startWarm d.v) 7)) (shl (i32 (it.val : Int)) 6) = _
      rw [hit, h5, hc7 _ (by omega), show Loader.or32 (andi (shru (tidW L g) 3) 7)
        (andi (shl (tidW L g) 3) 56) = W (rowIn L g) from w2, add32_W (by omega),
        add32_W (by omega)]
      exact congrArg W (by omega)
    · have h5 := h4' (by decide)
      show add32 (Loader.or32 (Loader.or32 (andi (shru (tidW L g) 3) 7)
        (andi (shl (tidW L g) 3) 56)) (shl (startWarm d.v) 7)) (shl (i32 (it.val : Int)) 6) = _
      rw [hit, h5, hc7 _ (by omega), show Loader.or32 (andi (shru (tidW L g) 3) 7)
        (andi (shl (tidW L g) 3) 56) = W (rowIn L g) from w2,
        or32_low (by omega) (by omega) (by omega), add32_W (by omega)]
      exact congrArg W (by omega)
  rw [key, toNat_W (by omega)]

set_option maxHeartbeats 1000000 in
/-- **The length of a lane's rows in a block.** -/
theorem len_num (hp : Pre p L m) {d : D} {ns nv nc b : Nat} {per : Per} (hb : d.site.blk = true)
    (hF : LFits p L g d ns nv nc) (hN : TileNum p L g d.v d.v.su b)
    (hper : perOf d.site = some per) (hib : inBlk d.site ≤ 1) :
    sv (if per = .prime then lenPrime L g d.v else lenW L g d.v per) =
      (p.kLength b : Int) - (128 * (nBlk p L g b - 1 - nc / 2) + grpOf L g : Nat) := by
  obtain ⟨n1, n2, n3⟩ := nBlk_bound hp hN.batch hN.lo hN.hi
  obtain ⟨h1, h2, h3, h4⟩ := blk_round hb hF hN n1 n2 hper hib
  have hk := (hp.lengths b hN.batch).2.2
  obtain ⟨-, -, -, -, ⟨v₀, hsu, -, -⟩, -, -, -⟩ := lfits_blk_of hb hF
  have ht : g % L.block < 512 := by rw [hp.block]; exact Nat.mod_lt _ (by decide)
  obtain ⟨-, -, w3⟩ := lane_words _ ht
  have hgrp : grpOf L g < 8 := by unfold grpOf; omega
  have h28 := hN.r28
  change d.v.su.r28 = W (nBlk p L g b) at h28
  have huk := hN.ukw
  have hc7 : ∀ a, a < 2 ^ 24 → shl (W a) 7 = W (a * 128) := fun a ha =>
    shl_W (k := 7) (by decide) (by omega)
  change nc / 2 + 1 ≤ nBlk p L g b at h2
  have h4' : per ≠ .prime → startWarm d.v = W (nBlk p L g b - 1 - nc / 2) := fun h => (h4 h).2
  clear h4
  generalize nBlk p L g b = nn at *
  have hw3 : andi (shru (tidW L g) 3) 7 = W (grpOf L g) := w3
  have hsub : ∀ y, y = 128 * (nn - 1 - nc / 2) + grpOf L g → sv (sub32 d.v.ukw (W y)) =
      (p.kLength b : Int) - (128 * (nn - 1 - nc / 2) + grpOf L g : Nat) := by
    rintro y rfl
    have e1 : toSigned 32 (W (p.kLength b)) = (p.kLength b : Int) := toSigned_W (by omega)
    have e2 : toSigned 32 (W (128 * (nn - 1 - nc / 2) + grpOf L g)) =
        ((128 * (nn - 1 - nc / 2) + grpOf L g : Nat) : Int) := toSigned_W (by omega)
    rw [huk]
    simp only [sv]
    rw [toSigned_sub32 _ _ (by rw [e1, e2]; omega) (by rw [e1, e2]; omega), e1, e2]
  cases per
  · have h0 := h3 rfl
    simp only [↓reduceIte, lenPrime]
    have hgt : scmpi .gt .s (W nn) 0 = true := by
      rw [scmpi_gt_s _ (by decide) (by decide), sv_W (by omega)]
      simp
      omega
    have hp119 : d.v.su.p119 = scmpi .gt .s d.v.su.r28 0 := by rw [hsu]; simp only [setup]
    have hr32 : d.v.su.r32 = shl (addi d.v.su.r28 (-1)) 7 := by rw [hsu]; simp only [setup]
    rw [hp119, hr32, h28, hgt]
    simp only [sel, ↓reduceIte]
    rw [show (-1 : Int) = -((1 : Nat) : Int) from rfl, addi_neg (by omega) (by omega),
      hc7 _ (by omega)]
    rw [show andi (shru (BitVec.ofNat 64 (g % L.block)) 3) 7 = W (grpOf L g) from w3,
      add32_W (by omega)]
    exact hsub _ (by omega)
  all_goals
    have h5 := h4' (by decide)
    have hlt : scmpi .lt .s (startWarm d.v) 0 = false := by
      rw [h5, scmpi_lt_s _ (by decide) (by decide), sv_W (by omega)]
      simp
    simp only [reduceCtorEq, ↓reduceIte, lenW, hlt, sel, Bool.false_eq_true]
    simp only [lenWarm, lenSteady]
    rw [h5, hc7 _ (by omega), hw3]
  · rw [or32_low (by omega) (by omega) (by omega)]
    exact hsub _ (by omega)
  · rw [add32_W (by omega)]
    exact hsub _ (by omega)

/-- The key of a lane's row of page round `it` in a block with `nc` commits. -/
def keyAt (p : Params) (L : Launch) (b g nc : Nat) (it : Fin 2) : Nat :=
  128 * (nBlk p L g b - 1 - nc / 2) + rowIn L g + 64 * it.val

/-- The page of a key: the first one past the used length. -/
def pageAt (p : Params) (b key : Nat) : Nat := if key < p.kLength b then p.page b (key / 16) else 0

set_option maxHeartbeats 1000000 in
/-- **The address of a lane's row.** -/
theorem adW_num (hp : Pre p L m) {d : D} {ns nv nc b : Nat} {per : Per} (hb : d.site.blk = true)
    (hF : LFits p L g d ns nv nc) (hT : TileW p L g d.v) (hN : TileNum p L g d.v d.v.su b)
    (hper : perOf d.site = some per) (hib : inBlk d.site ≤ 1) (c : Bool) (it : Fin 2) :
    (adW p b L g d.v per c it).toNat = (layOf p c).base +
      2 * (pageAt p b (keyAt p L b g nc it) * (layOf p c).pageStride +
        (Epilogue.assignedCoordinates p b (g / L.block)).2 / 6 * (layOf p c).headStride +
        keyAt p L b g nc it % 16 * (layOf p c).rowStride) := by
  obtain ⟨n1, n2, n3⟩ := nBlk_bound hp hN.batch hN.lo hN.hi
  obtain ⟨-, h2, -, -⟩ := blk_round hb hF hN n1 n2 hper hib
  have hrow := row0_num hp hb hF hN hper hib it
  have hk := (hp.lengths b hN.batch).2.2
  have hri : rowIn L g < 64 := by unfold rowIn grpOf; omega
  have hit := it.isLt
  change _ = keyAt p L b g nc it at hrow
  have hkb : keyAt p L b g nc it < 2 ^ 31 := by unfold keyAt; omega
  generalize keyAt p L b g nc it = key at hrow hkb ⊢
  have hcond : rowCond p L g d.v per it = decide (p.kLength b ≤ key) := by
    have h1 : scmp .ge .s (row0 p L g d.v per it) d.v.ukw = decide (p.kLength b ≤ key) := by
      rw [scmp_ge_s, hN.ukw, sv_W (by omega), eq_W (row0 p L g d.v per it), hrow, sv_W hkb]
      simp
    unfold rowCond
    split
    · exact h1
    · rw [geW_eq]; exact h1
  have hpg : (pgW p b L g d.v per it).toNat = pageAt p b key ∧
      pageAt p b key < p.pages ∧ pageAt p b key < 2 ^ 31 := by
    have h0 : 0 < p.pages := by have := hp.shape; omega
    unfold pgW pageAt
    rw [hcond, hrow]
    by_cases h : key < p.kLength b
    · rw [ite_eq_right (by simp; omega), ite_eq_left h]
      obtain ⟨q1, q2⟩ := (hp.pageTable b hN.batch).2 (key / 16) (by omega)
      exact ⟨toNat_W (by omega), q1, q2⟩
    · rw [ite_eq_left (by simp; omega), ite_eq_right h]
      exact ⟨by decide, h0, by decide⟩
  have hrw : (rwW p L g d.v per it).toNat = key % 16 := by
    unfold rwW
    rw [pgIdx_eq (by omega), hrow, eq_W (row0 p L g d.v per it), hrow,
      show i32 16 = W 16 from rfl, mul32_W (by omega) (by omega) (by omega),
      sub32_W (by omega) (by omega), toNat_W (by omega)]
    omega
  obtain ⟨R, bal, hP, hco, hsu, -⟩ := hT
  obtain ⟨-, hh⟩ := Epilogue.assignedCoordinates_valid hp hN.lo hN.hi
  obtain ⟨r12, r13⟩ := head_exact (p := p) (L := L) (g := g) hp hh
    (by rw [← hco]; exact hN.head) hsu
  have hl : layOf p c = p.kLayout ∨ layOf p c = p.vLayout := by
    cases c
    · exact .inl rfl
    · exact .inr rfl
  have hbase : (if c then d.v.su.rd13 else d.v.su.rd12).toNat = (layOf p c).base +
      2 * ((Epilogue.assignedCoordinates p b (g / L.block)).2 / 6 * (layOf p c).headStride) := by
    cases c
    · exact r12
    · exact r13
  obtain ⟨hp1, hp2, hp3⟩ := hpg
  have hroom := row_room hp hl hp2 (show (Epilogue.assignedCoordinates p b (g / L.block)).2 / 6 <
    p.kvHeads by unfold Params.heads at hh; omega) (show key % 16 < 16 by omega)
  generalize (Epilogue.assignedCoordinates p b (g / L.block)).2 / 6 = hh6 at *
  unfold adW adOf
  rw [add_shl1 hbase (o := (layOf p c).rowStride * (key % 16) +
    (layOf p c).pageStride * pageAt p b key) ?_ ?_]
  · rw [Nat.mul_comm (layOf p c).rowStride, Nat.mul_comm (layOf p c).pageStride]; omega
  · rw [toNat_mad64, toNat_mul64, toNat_sx32 (by omega), toNat_sx32 (by omega), hp1, hrw]
    omega
  · rw [Nat.mul_comm (layOf p c).rowStride, Nat.mul_comm (layOf p c).pageStride]; omega

end
end PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
