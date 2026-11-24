-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Lib.ScheduleCoords
public import Kernels.TmlFa4Fwd.Proof.Epilogue.Reads
public import Lemmas.Arith.WarpPrefix
import Kernels.TmlFa4Fwd.Proof.Lib.OutputMap
import Lemmas.Flow.WarpScan
import Lemmas.Protocol.NamedBarSources
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The output warp's scan, in numbers

The reference values of a scan round (`Ideal`) as the batch's tile counts: lane `ℓ` of round
`r` holds the tile count of request `31 r + ℓ` (`tlv_W`), the prefix scan builds the sums of
the counts below each lane (`psum_W`), and the work before a reached round's group is the
tiles before its first request times the heads (`A_W`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Epilogue
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0}

/-! ### Word arithmetic -/

theorem andi_256_W {a : Nat} (ha : a < 2 ^ 32) : andi (W a) (-256) = W (a / 256 * 256) := by
  apply BitVec.eq_of_toNat_eq
  have hi : (i32 (-256)).toNat = 4294967040 := by decide
  have hr : (r32 (W a)).toNat = a := by rw [r32_W ha]; exact toNat_W (by omega)
  rw [andi, BitVec.toNat_and, hi, hr, Epilogue.lowByteMask ha, toNat_W (by omega)]

theorem tilesOf_W {a b : Nat} (hab : a ≤ b) (hb : b < 2 ^ 31) :
    tilesOf (W b) (W a) = W ((b - a + 255) / 256) := by
  have hr : b - a < 2 ^ 31 := by omega
  have h1 : sub32 (W b) (W a) = W (b - a) := sub32_W hab (by omega)
  have h2 : shrs (W (b - a)) 31 = W 0 := by
    rw [show (31 : Int) = ((31 : Nat) : Int) from rfl, toNat_shrs_W hr (by omega),
      Nat.div_eq_of_lt hr]
  have h3 : shru (W 0) 24 = W 0 := by decide
  have h4 : add32 (W (b - a)) (W 0) = W (b - a) := by rw [add32_W (by omega)]; rfl
  have h5 : shrs (W (b - a)) 8 = W ((b - a) / 256) := by
    rw [show (8 : Int) = ((8 : Nat) : Int) from rfl, toNat_shrs_W hr (by omega)]; rfl
  simp only [tilesOf, h1, h2, h3, h4, h5, andi_256_W (show b - a < 2 ^ 32 by omega),
    scmpi_gt_neg1_W hr, scmp_ne_b_W (show b - a < 2 ^ 32 by omega)
      (show (b - a) / 256 * 256 < 2 ^ 32 by omega), Bool.true_and, sel]
  split
  · rw [show i32 1 = W 1 from rfl, add32_W (by omega)]
    congr 1
    rename_i h
    simp only [decide_eq_true_eq] at h
    omega
  · rw [i32_zero, add32_W (by omega)]
    congr 1
    rename_i h
    simp only [decide_eq_true_eq, not_not] at h
    omega

/-! ### Tile counts -/

theorem qOffset_lt (hp : Pre p L m) {b : Nat} (hb : b ≤ p.batch) : p.qOffset b < 2 ^ 30 := by
  have := hp.qOffset_le_total hb
  obtain ⟨-, -, -, -, -, hsh⟩ := hp.shape
  omega

theorem qv_W (_hp : Pre p L m) {n : Nat} (hn : n < 2 ^ 32) : qv p (W n) = W (p.qOffset n) := by
  simp only [qv, r32_W hn, toNat_W (show n < 2 ^ 64 by omega)]

/-- The tile count of request `first + ℓ` of a group, for lanes below 31 inside the batch. -/
abbrev xs (p : Params) (first : Nat) : Nat → Nat := groupLaneTiles p first

theorem lw_eq_b {ℓ n : Nat} (hℓ : ℓ < 32) (hn : n < 2 ^ 31) :
    scmpi .eq .b (lw ℓ) (n : Int) = decide (ℓ = n) := by
  have hi : (i32 (n : Int)).toNat = n := by
    simp only [i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_ofInt]; omega
  simp only [scmpi, PTX.compare, lw_W hℓ, hi,
    toNat_W (show ℓ < 2 ^ 64 by omega)]
  simp

theorem lw_gt_u {ℓ n : Nat} (hℓ : ℓ < 32) (hn : n < 2 ^ 31) :
    scmpi .gt .u (lw ℓ) (n : Int) = decide (n < ℓ) := by
  have hi : (i32 (n : Int)).toNat = n := by
    simp only [i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_ofInt]; omega
  simp only [scmpi, PTX.compare, lw_W hℓ, hi,
    toNat_W (show ℓ < 2 ^ 64 by omega)]
  simp

theorem lw_ne_b {ℓ n : Nat} (hℓ : ℓ < 32) (hn : n < 2 ^ 31) :
    scmpi .ne .b (lw ℓ) (n : Int) = decide (ℓ ≠ n) := by
  have hi : (i32 (n : Int)).toNat = n := by
    simp only [i32, truncBits, BitVec.toNat_ofNat, BitVec.toNat_ofInt]; omega
  simp only [scmpi, PTX.compare, lw_W hℓ, hi,
    toNat_W (show ℓ < 2 ^ 64 by omega)]
  simp

theorem reqN_add (r ℓ : Nat) : reqN p r ℓ = reqN p r 0 + ℓ := by
  unfold reqN; split <;> omega

theorem reqN_lt (hp : Pre p L m) (r ℓ : Nat) (hℓ : ℓ < 32) : reqN p r ℓ < 2 ^ 31 := by
  have := batch_lt hp
  unfold reqN; split <;> omega

theorem reads_iff (hp : Pre p L m) {late : Bool} {r ℓ : Nat} (hℓ : ℓ < 32) :
    reads p late r ℓ = decide (reqN p r ℓ ≤ p.batch) := by
  have hb := batch_lt hp
  simp only [reads, req_W hp late r hℓ, batchOf_W hp,
    scmp_gt_W (reqN_lt hp r ℓ hℓ) (show p.batch < 2 ^ 31 by omega)]
  by_cases h : reqN p r ℓ ≤ p.batch
  · simp [h]
  · simp [h]; omega

theorem wv_W (hp : Pre p L m) {late : Bool} {r ℓ : Nat} (hℓ : ℓ < 32)
    (h : reqN p r ℓ ≤ p.batch) : wv p late r ℓ = W (p.qOffset (reqN p r ℓ)) := by
  simp only [wv, reads_iff hp hℓ, h, decide_true, ↓reduceIte, req_W hp late r hℓ]
  exact qv_W hp (by have := reqN_lt hp r ℓ hℓ; omega)

/-- **A lane's tile count**: lane `ℓ` of round `r` holds the tile count of request
`reqN r 0 + ℓ`, zero for lane 31 and past the batch. -/
theorem tlv_W (hp : Pre p L m) {late : Bool} {r ℓ : Nat} (hℓ : ℓ < 32) :
    tlv p late r ℓ = W (xs p (reqN p r 0) ℓ) := by
  have hb := batch_lt hp
  have hr := reqN_lt hp r ℓ hℓ
  have hskip : skipv p late r ℓ = !(decide (ℓ < 31 ∧ reqN p r 0 + ℓ < p.batch)) := by
    unfold skipv
    split
    · rename_i h0
      have hW : BitVec.ofNat 64 p.batch = W p.batch := rfl
      rw [show (31 : Int) = ((31 : Nat) : Int) from rfl, lw_ne_b hℓ (by decide), hW, lw_W hℓ,
        scmp_lt_W (by omega) (by omega)]
      simp only [reqN, h0, ↓reduceIte, Nat.zero_add]
      by_cases h1 : ℓ < 31 <;> by_cases h2 : ℓ < p.batch <;> simp [h1, h2] <;> omega
    · rw [show (31 : Int) = ((31 : Nat) : Int) from rfl, lw_eq_b hℓ (by decide),
        req_W hp late r hℓ, batchOf_W hp,
        scmp_ge_W hr (by omega), ← reqN_add]
      by_cases h1 : ℓ < 31 <;> by_cases h2 : reqN p r ℓ < p.batch <;> simp [h1, h2] <;> omega
  simp only [tlv, hskip, sel, xs, groupLaneTiles]
  by_cases hc : ℓ < 31 ∧ reqN p r 0 + ℓ < p.batch
  · simp only [hc, and_self, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hl1 : ℓ + 1 < 32 := by omega
    have e1 : reqN p r (ℓ + 1) = reqN p r 0 + ℓ + 1 := by rw [reqN_add]; omega
    have e0 : reqN p r ℓ = reqN p r 0 + ℓ := reqN_add r ℓ
    have hd : dnv p late r ℓ = W (p.qOffset (reqN p r 0 + ℓ + 1)) := by
      simp only [dnv, hc.1, ↓reduceIte]
      rw [wv_W hp hl1 (by omega), e1]
    rw [hd, wv_W hp hℓ (by omega), e0]
    have hmono := hp.qOffset_mono (show reqN p r 0 + ℓ ≤ reqN p r 0 + ℓ + 1 by omega)
      (show reqN p r 0 + ℓ + 1 ≤ p.batch by omega)
    have hq := qOffset_lt hp (show reqN p r 0 + ℓ + 1 ≤ p.batch by omega)
    rw [tilesOf_W hmono (by omega)]
    rfl
  · simp only [hc, decide_false, Bool.not_false, ↓reduceIte, i32_zero]

/-- **The prefix scan**: after `k` of its five steps, lane `ℓ` holds the sum of the last `2 ^ k`
tile counts up to its own. -/
theorem psum_W (hp : Pre p L m) {late : Bool} {r first : Nat} (hf : first ≤ p.batch)
    (htl : ∀ ℓ < 32, tlv p late r ℓ = W (xs p first ℓ)) :
    ∀ k ≤ 5, ∀ ℓ < 32, psum p late r k ℓ = W (prefixWindow (xs p first) (2 ^ k) ℓ) := by
  have hb (w ℓ : Nat) (hℓ : ℓ < 32) : prefixWindow (xs p first) w ℓ < 2 ^ 31 :=
    hp.groupWindow_signed hf hℓ w
  intro k
  induction k with
  | zero => intro _ ℓ hℓ; simp only [psum, htl ℓ hℓ, pow_zero, prefixWindow_one]
  | succ k ih =>
    intro hk ℓ hℓ
    have hw1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hw5 : 2 ^ k ≤ 16 :=
      calc 2 ^ k ≤ 2 ^ 4 := Nat.pow_le_pow_right (by decide) (by omega)
        _ = 16 := rfl
    have hsrc : upSrc k ℓ < 32 := by unfold upSrc; split <;> omega
    rw [psum, ih (by omega) ℓ hℓ, ih (by omega) _ hsrc, pow_succ, mul_comm,
      prefixWindow_double]
    have hs := hb (2 ^ k) ℓ hℓ
    have hs' := hb (2 ^ k) (ℓ - 2 ^ k) (by omega)
    unfold upd upSrc
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp only [↓reduceIte, ps1, sel, pow_zero] at hs hs' ⊢
      rw [show (0 : Int) = ((0 : Nat) : Int) from rfl, lw_eq_b hℓ (by decide)]
      by_cases h0 : ℓ = 0
      · subst h0
        simp only [decide_true, ↓reduceIte, Nat.one_le_iff_ne_zero, ne_eq, not_true_eq_false]
        rw [show i32 ((0 : Nat) : Int) = W 0 from rfl, add32_W (by omega)]
        simp
      · have h1 : 1 ≤ ℓ := by omega
        simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte, h1]
        rw [add32_W (by omega), Nat.add_comm]
    · have hne : k ≠ 0 := by omega
      have hpk : (2 : Int) ^ k - 1 = ((2 ^ k - 1 : Nat) : Int) := by
        push_cast [hw1]; ring
      simp only [hne, ↓reduceIte, psk, sel, hpk]
      rw [lw_gt_u hℓ (by omega)]
      by_cases hle : 2 ^ k ≤ ℓ
      · have : 2 ^ k - 1 < ℓ := by omega
        simp only [this, decide_true, ↓reduceIte, hle]
        rw [add32_W (by omega)]
      · have : ¬ 2 ^ k - 1 < ℓ := by omega
        simp only [this, decide_false, Bool.false_eq_true, ↓reduceIte, hle]
        rw [i32_zero, add32_W (by omega)]

/-! ### The rounds of a scan -/

theorem heads_lt (hp : Pre p L m) : p.heads < 2 ^ 31 := hp.heads_signed

theorem H_W (hp : Pre p L m) : H p = W p.heads := r32_W (by have := heads_lt hp; omega)

theorem kw_W (c : Nat) : kw c = W c := rfl

/-- The work before request `b` of the batch fits a signed word. -/
theorem work_lt (hp : Pre p L m) {b : Nat} (hb : b ≤ p.batch) :
    tilePrefix p b * p.heads < 2 ^ 31 := hp.prefixWork_signed hb

/-- **The tiles of a group**: lane 31's prefix is the tiles of the group's requests. -/
theorem T_W (hp : Pre p L m) {late : Bool} {r : Nat} (hf : reqN p r 0 ≤ p.batch) :
    T p late r = W (tilePrefix p (min p.batch (reqN p r 0 + 31)) - tilePrefix p (reqN p r 0)) := by
  have h1 : T p late r = psum p late r 5 31 := rfl
  have h := groupTiles_eq p hf (show 32 ≤ 32 by decide)
  have h2 : prefixWindow (xs p (reqN p r 0)) (2 ^ 5) 31 =
      tilePrefix p (min p.batch (reqN p r 0 + 31)) - tilePrefix p (reqN p r 0) := by
    rw [show (2 : Nat) ^ 5 = 32 from rfl, prefixWindow_warp _ (by decide)]
    rw [show min 31 32 = 31 from rfl] at h
    simp only [xs, Nat.reduceAdd]
    omega
  rw [h1, psum_W hp hf (fun ℓ hℓ => tlv_W hp hℓ) 5 le_rfl 31 (by decide), h2]

theorem heads_pos (hp : Pre p L m) : 1 ≤ p.heads := by
  have := hp.shape.2.2.1
  simp only [Params.heads]
  omega

theorem heads_small (hp : Pre p L m) : p.heads ≤ 2 ^ 25 := by
  have hO := hp.ranges p.oRegion (by simp)
  change p.oBase + 512 * p.heads * p.totalQ ≤ 2 ^ 64 at hO
  have hr := hp.raggedBase
  rw [← Nat.mul_assoc] at hr
  omega

theorem le_work (hp : Pre p L m) (a : Nat) : a ≤ a * p.heads :=
  Nat.le_mul_of_pos_right a (heads_pos hp)

/-- A reached loop round `r ≥ 1` reads the group starting at request `31 r`, inside the
batch. -/
theorem reached_first (hp : Pre p L m) {c : Nat} {late : Bool} {r : Nat}
    (hr : Reached p c late r) (h1 : 1 ≤ r) : 31 * r < p.batch ∧ reqN p r 0 = 31 * r := by
  have hb := batch_lt hp
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have hc := hr r' (by omega)
  have hG : addi (G p late (r' + 1)) 31 = W (min (31 * r') p.batch + 31) := by
    rw [G_W hp late (r' + 1) h1, addi31_W (by omega)]
    simp
  have hlt : min (31 * r') p.batch + 31 < p.batch := by
    cases r' with
    | zero =>
      simp only [cont, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
      have h2 := hc.2
      rw [hG, batchOf_W hp, scmp_ge_W (by omega) (by omega)] at h2
      simpa using h2
    | succ r' =>
      simp only [cont, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
      have h2 := hc.2
      rw [hG, batchOf_W hp, scmp_ge_W (by omega) (by omega)] at h2
      simpa using h2
  constructor
  · omega
  · simp only [reqN, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]; omega

/-- **The work before a reached round's group** is the tiles before its first request times the
heads. -/
theorem A_W (hp : Pre p L m) {c : Nat} {late : Bool} :
    ∀ r, Reached p c late r → A p late r = W (tilePrefix p (reqN p r 0) * p.heads)
  | 0, _ => by simp [A, reqN, tilePrefix]
  | 1, hr => by
    obtain ⟨hlt, hf⟩ := reached_first hp hr le_rfl
    have hf0 : reqN p 0 0 = 0 := rfl
    have hT := T_W hp (late := late) (r := 0) (by simp [hf0])
    rw [hf0, Nat.zero_add, Nat.min_eq_right (by omega)] at hT
    have hw := work_lt hp (show 31 ≤ p.batch by omega)
    have hhd := heads_lt hp
    have hl := le_work hp (tilePrefix p 31)
    rw [A, hT, H_W hp, hf, show tilePrefix p 0 = 0 from rfl, Nat.sub_zero,
      mul32_W (by omega) (by omega) (by omega)]
  | r + 2, hr => by
    obtain ⟨hlt, hf⟩ := reached_first hp hr (by omega)
    obtain ⟨hlt', hf'⟩ := reached_first hp (hr.mono (show r + 1 ≤ r + 2 by omega)) (by omega)
    have ih := A_W hp (r + 1) (hr.mono (by omega))
    have hT := T_W hp (late := late) (r := r + 1) (by omega)
    rw [hf', Nat.min_eq_right (by omega)] at hT
    have hmono := tilePrefix_mono p (show 31 * (r + 1) ≤ 31 * (r + 1) + 31 by omega)
    have hw := work_lt hp (show 31 * (r + 1) + 31 ≤ p.batch by omega)
    have hw' := work_lt hp (show 31 * (r + 1) ≤ p.batch by omega)
    have hhd := heads_lt hp
    have hl := le_work hp (tilePrefix p (31 * (r + 1) + 31) - tilePrefix p (31 * (r + 1)))
    have hl' := le_work hp (tilePrefix p (31 * (r + 1) + 31))
    rw [A, hT, H_W hp, ih, hf', hf]
    have hmul : (tilePrefix p (31 * (r + 1) + 31) - tilePrefix p (31 * (r + 1))) * p.heads +
        tilePrefix p (31 * (r + 1)) * p.heads = tilePrefix p (31 * (r + 2)) * p.heads := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hmono]
      congr 2
    have hle : (tilePrefix p (31 * (r + 1) + 31) - tilePrefix p (31 * (r + 1))) * p.heads ≤
        tilePrefix p (31 * (r + 1) + 31) * p.heads := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    rw [mad32_W (by omega) (by omega) (by omega), hmul]

theorem not_gt_eq_le (x y : BitVec 64) : (!scmp .gt .s x y) = scmp .le .s x y := by
  simp only [scmp, PTX.compare]
  by_cases h : toSigned 32 (r32 x) ≤ toSigned 32 (r32 y) <;> simp [h]
  omega

theorem cont_eq (c : Nat) (late : Bool) (r : Nat) :
    cont p c late r = (scmp .le .s (A p late (r + 1)) (kw c) &&
      !scmp .ge .s (addi (G p late (r + 1)) 31) (batchOf p late)) := by
  cases r with
  | zero => simp only [cont, not_gt_eq_le]; rfl
  | succ r => rfl

theorem atTotal_eq (c : Nat) (late : Bool) (r : Nat) :
    atTotal p c late r = !scmp .le .s (A p late (r + 1)) (kw c) := by
  cases r with
  | zero => simp only [atTotal, ← not_gt_eq_le, Bool.not_not]; rfl
  | succ r => rfl

/-- The work through a reached round's group. -/
theorem A_succ_W (hp : Pre p L m) {c : Nat} {late : Bool} {r : Nat} (hr : Reached p c late r)
    (hf : reqN p r 0 ≤ p.batch) :
    A p late (r + 1) = W (tilePrefix p (min p.batch (reqN p r 0 + 31)) * p.heads) := by
  have hT := T_W hp (late := late) hf
  have hmono := tilePrefix_mono p (show reqN p r 0 ≤ min p.batch (reqN p r 0 + 31) by omega)
  have hw := work_lt hp (show min p.batch (reqN p r 0 + 31) ≤ p.batch by omega)
  have hhd := heads_lt hp
  have hl := le_work hp (tilePrefix p (min p.batch (reqN p r 0 + 31)) - tilePrefix p (reqN p r 0))
  have hl' := le_work hp (tilePrefix p (min p.batch (reqN p r 0 + 31)))
  have hle : (tilePrefix p (min p.batch (reqN p r 0 + 31)) - tilePrefix p (reqN p r 0)) *
      p.heads ≤ tilePrefix p (min p.batch (reqN p r 0 + 31)) * p.heads :=
    Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hmul : (tilePrefix p (min p.batch (reqN p r 0 + 31)) - tilePrefix p (reqN p r 0)) *
      p.heads + tilePrefix p (reqN p r 0) * p.heads =
        tilePrefix p (min p.batch (reqN p r 0 + 31)) * p.heads := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hmono]
  cases r with
  | zero =>
    have h0 : tilePrefix p (reqN p 0 0) = 0 := rfl
    rw [h0, Nat.sub_zero] at hT
    rw [A, hT, H_W hp, mul32_W (by omega) (by omega) (by omega)]
  | succ r =>
    rw [A, hT, H_W hp, A_W hp (r + 1) hr, mad32_W (by omega) (by omega) (by omega), hmul]

theorem cta_lt (hp : Pre p L m) {g : Nat} (hg : g < L.threads) : g / L.block < 2 ^ 31 :=
  lt_trans (NamedBar.cta_lt hg) hp.grid.2.2

/-- **The scan's end, when the first pass picks a tile**: the scan ended at the round whose group
holds the CTA's work item: the work before the group's first request `31 R` is at most the CTA
and the work through the group exceeds it. -/
theorem picked_group (hp : Pre p L m) {g R : Nat} {bal : BitVec 64} (hg : g < L.threads)
    (hP : PickedPre p L g R bal) :
    31 * R < p.batch ∧ reqN p R 0 = 31 * R ∧
      tilePrefix p (31 * R) * p.heads ≤ g / L.block ∧
      g / L.block < tilePrefix p (min p.batch (31 * R + 31)) * p.heads ∧
      gxv p (g / L.block) false R = W (31 * R) ∧
      curv p (g / L.block) false R = W (tilePrefix p (min p.batch (31 * R + 31)) * p.heads) := by
  obtain ⟨⟨hReach, hcont⟩, -, hgx⟩ := hP
  have hb := batch_lt hp
  have hc := cta_lt hp hg
  have hfirst : 31 * R < p.batch ∧ reqN p R 0 = 31 * R := by
    rcases Nat.eq_zero_or_pos R with rfl | hR
    · exact ⟨by have := hp.shape.1; omega, rfl⟩
    · exact reached_first hp hReach hR
  obtain ⟨hlt, hf⟩ := hfirst
  have hA := A_W hp R hReach
  have hA1 := A_succ_W hp hReach (by omega)
  rw [hf] at hA hA1
  have hw := work_lt hp (show min p.batch (31 * R + 31) ≤ p.batch by omega)
  have hw' := work_lt hp (show 31 * R ≤ p.batch by omega)
  have hG1 : addi (G p false (R + 1)) 31 = W (31 * R + 31) := by
    rw [G_W hp false (R + 1) (by omega), addi31_W (by omega)]
    congr 1; simp only [Nat.add_sub_cancel]; omega
  have hle : scmp .le .s (A p false (R + 1)) (kw (g / L.block)) =
      decide (tilePrefix p (min p.batch (31 * R + 31)) * p.heads ≤ g / L.block) := by
    rw [hA1, kw_W, scmp_le_W hw hc]
  -- The low bound: the work before the group.
  have hlow : tilePrefix p (31 * R) * p.heads ≤ g / L.block := by
    rcases Nat.eq_zero_or_pos R with rfl | hR
    · simp [tilePrefix]
    · obtain ⟨R', rfl⟩ : ∃ R', R = R' + 1 := ⟨R - 1, by omega⟩
      have hc' := hReach R' (by omega)
      rw [cont_eq] at hc'
      simp only [Bool.and_eq_true] at hc'
      have h1 := hc'.1
      rw [hA, kw_W, scmp_le_W hw' hc] at h1
      simpa using h1
  have hgx' := hgx
  rw [batchOf_W hp] at hgx'
  by_cases hT : tilePrefix p (min p.batch (31 * R + 31)) * p.heads ≤ g / L.block
  · -- The scan did not stop at the group's total: it ran out of groups, and its last group start
    -- is the batch.
    exfalso
    rw [cont_eq, hle, hG1, batchOf_W hp, scmp_ge_W (by omega) (by omega)] at hcont
    simp only [hT, decide_true, Bool.true_and, Bool.not_eq_eq_eq_not, Bool.not_false,
      decide_eq_true_eq] at hcont
    have hat : atTotal p (g / L.block) false R = false := by
      rw [atTotal_eq, hle]; simp [hT]
    have hgxe : gxv p (g / L.block) false R = W p.batch := by
      cases R with
      | zero =>
        simp only [gxv, hat, Bool.false_eq_true, ↓reduceIte]
        rw [hG1, batchOf_W hp, min32_W (by omega) (by omega), Nat.min_eq_right (by omega)]
      | succ R =>
        simp only [gxv, hat, Bool.false_eq_true, ↓reduceIte]
        rw [hG1, batchOf_W hp, min32_W (by omega) (by omega), Nat.min_eq_right (by omega)]
    rw [hgxe, scmp_ge_W (by omega) (by omega)] at hgx'
    simp at hgx'
  · have hat : atTotal p (g / L.block) false R = true := by
      rw [atTotal_eq, hle]; simp [hT]
    refine ⟨hlt, hf, hlow, by omega, ?_, ?_⟩
    · cases R with
      | zero => simp only [gxv, hat, ↓reduceIte]; rfl
      | succ R =>
        simp only [gxv, hat, ↓reduceIte]
        rw [G_W hp false (R + 1) (by omega), addi31_W (by omega), batchOf_W hp,
          min32_W (by omega) (by omega)]
        congr 1
        simp only [Nat.add_sub_cancel]
        omega
    · cases R with
      | zero => simp only [curv, hat, ↓reduceIte]; exact hA1
      | succ R => simp only [curv, hat, ↓reduceIte]; exact hA1

/-! ### The ballot and the chosen request -/

/-- The prefix sum of a lane of round `r` in numbers. -/
theorem psum5_W (hp : Pre p L m) {late : Bool} {r ℓ : Nat} (hf : reqN p r 0 ≤ p.batch)
    (hℓ : ℓ < 32) :
    psum p late r 5 ℓ = W (∑ i ∈ Finset.range (ℓ + 1), xs p (reqN p r 0) i) := by
  rw [psum_W hp hf (fun ℓ hℓ => tlv_W hp hℓ) 5 le_rfl ℓ hℓ, show (2 : Nat) ^ 5 = 32 from rfl,
    prefixWindow_warp _ hℓ]

/-- The selected request of a picked group, and the facts about it. -/
structure Sel (p : Params) (c first b : Nat) : Prop where
  first_le : first ≤ b
  lt_group : b < first + 31
  lt_batch : b < p.batch
  low : tilePrefix p b * p.heads ≤ c
  high : c < tilePrefix p (b + 1) * p.heads

/-- **The ballot's predicate**: a lane of the picked group votes when its request precedes the
selected request. -/
theorem predv_iff (hp : Pre p L m) {g R b : Nat} {bal : BitVec 64} (hg : g < L.threads)
    (hP : PickedPre p L g R bal) (hS : Sel p (g / L.block) (31 * R) b) {ℓ : Nat} (hℓ : ℓ < 32) :
    predv p (g / L.block) false R ℓ = decide (31 * R + ℓ < b) := by
  obtain ⟨hlt, hf, hlow, hhigh, -, hcur⟩ := picked_group hp hg hP
  have hc := cta_lt hp hg
  have hT := T_W hp (late := false) (r := R) (by omega)
  rw [hf] at hT
  have hmono := tilePrefix_mono p (show 31 * R ≤ min p.batch (31 * R + 31) by omega)
  have hw := work_lt hp (show min p.batch (31 * R + 31) ≤ p.batch by omega)
  have hw' := work_lt hp (show 31 * R ≤ p.batch by omega)
  have hhd := heads_lt hp
  have hl := le_work hp (tilePrefix p (min p.batch (31 * R + 31)) - tilePrefix p (31 * R))
  have hl' := le_work hp (tilePrefix p (min p.batch (31 * R + 31)))
  have hle : (tilePrefix p (min p.batch (31 * R + 31)) - tilePrefix p (31 * R)) * p.heads ≤
      tilePrefix p (min p.batch (31 * R + 31)) * p.heads :=
    Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hsub : sub32 (curv p (g / L.block) false R) (mul32 (T p false R) (H p)) =
      W (tilePrefix p (31 * R) * p.heads) := by
    rw [hcur, hT, H_W hp, mul32_W (by omega) (by omega) (by omega), sub32_W hle (by omega)]
    congr 1
    rw [← Nat.sub_mul, Nat.sub_sub_self hmono]
  have hsum := groupTiles_eq p (show 31 * R ≤ p.batch by omega) (show ℓ + 1 ≤ 32 by omega)
  have hwin := hp.groupWindow_signed (show 31 * R ≤ p.batch by omega) hℓ 32
  rw [prefixWindow_warp _ hℓ] at hwin
  have hend := tilePrefix_mono p (show min p.batch (31 * R + min 31 (ℓ + 1)) ≤ p.batch by omega)
  have hwe := work_lt hp (show min p.batch (31 * R + min 31 (ℓ + 1)) ≤ p.batch by omega)
  have hle2 := le_work hp (∑ i ∈ Finset.range (ℓ + 1), groupLaneTiles p (31 * R) i)
  have hdist : (∑ i ∈ Finset.range (ℓ + 1), groupLaneTiles p (31 * R) i) * p.heads +
      tilePrefix p (31 * R) * p.heads =
        (tilePrefix p (31 * R) + ∑ i ∈ Finset.range (ℓ + 1), groupLaneTiles p (31 * R) i) *
          p.heads := by ring
  have hval : (tilePrefix p (31 * R) + ∑ i ∈ Finset.range (ℓ + 1), groupLaneTiles p (31 * R) i)
      * p.heads < 2 ^ 31 := by rw [hsum]; exact hwe
  rw [predv, psum5_W hp (by omega) hℓ, hf, hsub, H_W hp]
  simp only [xs]
  rw [mad32_W (by omega) (by omega) (by omega), hdist, kw_W, scmp_le_W hval hc]
  exact decide_eq_decide.mpr (groupBallot_iff p hS.first_le hS.lt_group hS.lt_batch hℓ hS.low
    hS.high)

/-- **The ballot counts the requests of the group before the selected one.** -/
theorem ballot (hp : Pre p L m) {g R b : Nat} {bal : BitVec 64} (hg : g < L.threads)
    (hP : PickedPre p L g R bal) (hS : Sel p (g / L.block) (31 * R) b) :
    popc bal = W (b - 31 * R) ∧ scmpi .eq .b bal 0 = decide (b = 31 * R) := by
  obtain ⟨w, hw, rfl⟩ := hP.2.1
  have hbits : ∀ ℓ < 32, w.getLsbD ℓ = decide (ℓ < b - 31 * R) := by
    intro ℓ hℓ
    rw [hw ℓ hℓ, predv_iff hp hg hP hS hℓ]
    have := hS.first_le
    exact decide_eq_decide.mpr (by omega)
  have hwt : w.toNat < 2 ^ 32 := w.isLt
  have hr : r32 (BitVec.ofNat 64 w.toNat) = BitVec.ofNat 64 w.toNat := r32_W hwt
  have hn : (BitVec.ofNat 64 w.toNat).toNat = w.toNat := toNat_W (by omega)
  have hS' := hS
  constructor
  · simp only [popc, hr, hn]
    rw [ballot_popc_prefix (by have := hS.lt_group; have := hS.first_le; omega) hbits]
  · have hi : (i32 ((0 : Nat) : Int)).toNat = 0 := rfl
    simp only [scmpi, PTX.compare, hr, hn, show ((0 : Int)) = ((0 : Nat) : Int) from rfl, hi]
    by_cases h0 : b = 31 * R
    · have : w = 0 := by
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        rw [hbits i hi]
        simp [h0]
      subst this
      simp [h0]
    · have h1 := hbits 0 (by decide)
      have hpos : 0 < b - 31 * R := by have := hS.first_le; omega
      simp only [hpos, decide_true] at h1
      have : w.toNat ≠ 0 := by
        intro hz
        have : w = 0 := BitVec.eq_of_toNat_eq (by simpa using hz)
        subst this
        simp at h1
      simp [h0, this]

/-! ### The chosen request's coordinates -/

/-- The chosen request's work item inside the request, in numbers. -/
structure Coord (p : Params) (n item : Nat) : Prop where
  pos : 0 < n
  tiles : n * 256 < 2 ^ 30
  item_lt : item < n * p.heads
  work : n * p.heads < 2 ^ 31

set_option maxRecDepth 20000 in
/-- **The code's coordinates of a work item** are the scheduler's section coordinates. -/
theorem coords_W (hp : Pre p L m) {g : Nat} {d : D} {n item : Nat} (hC : Coord p n item)
    (hr : sub32 (ctaW L g) (add32 (sub32 d.cur (mul32 d.tot (headsW p))) d.pv) = W item)
    (hn : d.nt = W n) :
    let w := sectionWidth n p.heads
    let start := item / (w * n) * w
    let count := min w (p.heads - start)
    let pos := item % (w * n)
    coords p L g d = ⟨W (2 ^ 30 + 256 * (sectionCoords n p.heads w item).1),
      W (sectionCoords n p.heads w item).2, W item, W (w * n), W pos, W count⟩ ∧
    divOk (W item) (W (w * n)) = true ∧ divOk (W pos) (W count) = true := by
  intro w start count pos
  have ew : w = sectionWidth n p.heads := rfl
  have es : start = item / (w * n) * w := rfl
  have ec : count = min w (p.heads - start) := rfl
  have ep : pos = item % (w * n) := rfl
  obtain ⟨sid, esid⟩ : ∃ sid, sid = item / (w * n) := ⟨_, rfl⟩
  have hdm0 := Nat.mod_add_div item (w * n)
  rw [← ep, ← esid] at hdm0
  have hdm : pos + sid * (w * n) = item := by rw [Nat.mul_comm sid]; exact hdm0
  clear hdm0
  have hdv : sid * (w * n) ≤ item := by rw [esid]; exact Nat.div_mul_le_self _ _
  have hfinal : sectionCoords n p.heads w item = (n - 1 - pos / count, start + pos % count) := by
    simp only [sectionCoords, ← esid, ← ep]
    rw [← show start = sid * w by rw [es, esid], ← ec]
  have hq0 : ∀ (hi : item < 2 ^ 31) (hw : w * n < 2 ^ 31) (hw0 : 0 < w * n),
      fdiv (W item) (W (w * n)) = W sid := fun hi hw hw0 => by
    rw [esid]; exact fdiv_W hi hw hw0
  clear_value w start count pos
  rw [← esid] at es
  subst es
  clear esid
  have hhd := heads_lt hp
  have hh25 := heads_small hp
  have hh1 := heads_pos hp
  obtain ⟨hn0, hnt, hit, hwk⟩ := hC
  have hw1 : 1 ≤ w := ew ▸ sectionWidth_pos (by omega)
  have hw16 : w ≤ 16 := by rw [ew]; simp only [sectionWidth]; split_ifs <;> omega
  have hwh : w ≤ p.heads := ew ▸ Nat.min_le_left _ _
  have hwn : w * n ≤ 16 * n := Nat.mul_le_mul_right n hw16
  have hwn0 : 0 < w * n := Nat.mul_pos (by omega) hn0
  have hitem : item < 2 ^ 31 := by omega
  have hsn : sid * w * n = sid * (w * n) := by ring
  have hsidle : sid ≤ sid * (w * n) := Nat.le_mul_of_pos_right _ hwn0
  have hposlt : pos < w * n := by rw [ep]; exact Nat.mod_lt _ hwn0
  have hstart : sid * w < p.heads := by
    by_contra h
    have := Nat.mul_le_mul_right n (Nat.le_of_not_lt h)
    rw [Nat.mul_comm p.heads n] at this
    omega
  have hcount1 : 1 ≤ count := by rw [ec]; omega
  have hcountw : count ≤ w := by rw [ec]; exact Nat.min_le_left _ _
  have hposc : pos < count * n := by
    rw [ec]
    rcases Nat.le_total w (p.heads - sid * w) with h | h
    · rw [Nat.min_eq_left h]; exact hposlt
    · rw [Nat.min_eq_right h, Nat.sub_mul]
      have : n * p.heads = p.heads * n := Nat.mul_comm _ _
      omega
  have hqc : pos / count < n := by
    rw [Nat.div_lt_iff_lt_mul (by omega), Nat.mul_comm]; exact hposc
  have hn256 : n * 256 < 2 ^ 32 := by omega
  have h256 : shl d.nt 8 = W (256 * n) := by rw [hn, shl8_W hn256]
  have hk : paramW 800 = W 800 := r32_W (by decide)
  have hsh (k : Nat) (hk : k ≤ 6) : shrs (W (256 * n)) (k : Int) = W (256 * n / 2 ^ k) :=
    toNat_shrs_W (by omega) (by omega)
  have s3 : shrs (W (256 * n)) 3 = W (32 * n) := by
    have := hsh 3 (by decide); rw [show 256 * n / 2 ^ 3 = 32 * n by omega] at this; exact this
  have s4 : shrs (W (256 * n)) 4 = W (16 * n) := by
    have := hsh 4 (by decide); rw [show 256 * n / 2 ^ 4 = 16 * n by omega] at this; exact this
  have s5 : shrs (W (256 * n)) 5 = W (8 * n) := by
    have := hsh 5 (by decide); rw [show 256 * n / 2 ^ 5 = 8 * n by omega] at this; exact this
  have s6 : shrs (W (256 * n)) 6 = W (4 * n) := by
    have := hsh 6 (by decide); rw [show 256 * n / 2 ^ 6 = 4 * n by omega] at this; exact this
  have hgt (x : Nat) (hx : x < 2 ^ 31) : scmp .gt .s (W x) (W 800) = decide (800 < x) :=
    scmp_gt_W hx (by decide)
  have hH : headsW p = W p.heads := H_W hp
  have hW : min32 (sel (scmp .gt .s (shrs (shl d.nt 8) 3) (paramW 800))
      (sel (scmp .gt .s (shrs (shl d.nt 8) 4) (paramW 800))
        (sel (scmp .gt .s (shrs (shl d.nt 8) 5) (paramW 800))
          (sel (scmp .gt .s (shrs (shl d.nt 8) 6) (paramW 800)) (i32 1) (i32 2)) (i32 4))
        (i32 8)) (i32 16)) (headsW p) = W w := by
    rw [h256, hk, s3, s4, s5, s6, hgt _ (by omega), hgt _ (by omega), hgt _ (by omega),
      hgt _ (by omega), hH]
    have i1 : i32 1 = W 1 := rfl
    have i2 : i32 2 = W 2 := rfl
    have i4 : i32 4 = W 4 := rfl
    have i8 : i32 8 = W 8 := rfl
    have i16 : i32 16 = W 16 := rfl
    by_cases c3 : 800 < 32 * n <;> by_cases c4 : 800 < 16 * n <;> by_cases c5 : 800 < 8 * n <;>
      by_cases c6 : 800 < 4 * n <;>
      simp only [sel, c3, c4, c5, c6, decide_true, decide_false, ↓reduceIte,
        Bool.false_eq_true, i1, i2, i4, i8, i16] <;>
      rw [min32_W (by decide) hhd] <;> congr 1 <;> rw [ew] <;> simp only [sectionWidth] <;>
      split_ifs <;> omega
  have hm1 : mul32 (W w) d.nt = W (w * n) := by
    rw [hn, mul32_W (by omega) (by omega) (by omega)]
  have hq : fdiv (W item) (W (w * n)) = W sid := hq0 hitem (by omega) hwn0
  have hpos : sub32 (W item) (mul32 (W sid) (W (w * n))) = W pos := by
    rw [mul32_W (by omega) (by omega) (by omega), sub32_W hdv (by omega)]
    congr 1; omega
  have hst : mul32 (W sid) (W w) = W (sid * w) := mul32_W (by omega) (by omega) (by omega)
  have hcnt : sel (scmp .gt .s (add32 (W (sid * w)) (W w)) (headsW p))
      (sub32 (headsW p) (W (sid * w))) (W w) = W count := by
    rw [add32_W (by omega), hH, scmp_gt_W (by omega) hhd, ec]
    by_cases h : p.heads < sid * w + w
    · simp only [h, decide_true, sel, ↓reduceIte]
      rw [sub32_W (by omega) (by omega)]
      congr 1; omega
    · simp only [h, decide_false, sel, Bool.false_eq_true, ↓reduceIte]
      congr 1; omega
  have hq2 : fdiv (W pos) (W count) = W (pos / count) := fdiv_W (by omega) (by omega) (by omega)
  have hpcd := Nat.mod_add_div pos count
  have hqle : pos / count ≤ pos := Nat.div_le_self _ _
  have hqm : count * (pos / count) ≤ pos := Nat.mul_div_le pos count
  have hrow : addi (shl (add32 d.nt (not32 (W (pos / count)))) 8) 1073741824 =
      W (2 ^ 30 + 256 * (n - 1 - pos / count)) := by
    rw [hn, not32_add_W hqc (by omega)]
    generalize pos / count = q at hqc ⊢
    have hb : n - 1 - q < 2 ^ 22 := by omega
    generalize n - 1 - q = r at hb ⊢
    rw [shl8_W (by omega), show (1073741824 : Int) = ((1073741824 : Nat) : Int) by norm_num,
      addi_W (by norm_num) (by omega)]
    congr 1
    omega
  have hhead : sub32 (add32 (W pos) (W (sid * w))) (mul32 (W (pos / count)) (W count)) =
      W (sid * w + pos % count) := by
    have hc : pos / count * count = count * (pos / count) := Nat.mul_comm _ _
    rw [add32_W (by omega), mul32_W (by omega) (by omega) (by omega),
      sub32_W (by omega) (by omega)]
    congr 1
    omega
  obtain ⟨-, hok1⟩ := sdiv_W hitem (show w * n < 2 ^ 31 by omega) hwn0
  obtain ⟨-, hok2⟩ := sdiv_W (show pos < 2 ^ 31 by omega) (show count < 2 ^ 31 by omega)
    (by omega)
  refine ⟨?_, hok1, hok2⟩
  rw [hfinal]
  simp only [coords]
  rw [hr, hW, hm1, hq, hpos, hst, hcnt, hq2, hrow, hhead]

/-- The chosen request's prefix of work. -/
theorem pvv_W (hp : Pre p L m) {g R b : Nat} {bal : BitVec 64} (hg : g < L.threads)
    (hP : PickedPre p L g R bal) (hS : Sel p (g / L.block) (31 * R) b) :
    pvv p false R bal = W ((tilePrefix p b - tilePrefix p (31 * R)) * p.heads) := by
  obtain ⟨hlt, hf, hlow, hhigh, hgxv, hcurv⟩ := picked_group hp hg hP
  obtain ⟨hpopc, hzero⟩ := ballot hp hg hP hS
  have hb1 := hS.first_le
  have hb2 := hS.lt_group
  have hb3 := hS.lt_batch
  have hbb := batch_lt hp
  have hhd := heads_lt hp
  have hmono := tilePrefix_mono p (show 31 * R ≤ b by omega)
  have hwb := work_lt hp (show b ≤ p.batch by omega)
  rw [pvv, hzero]
  by_cases h0 : b = 31 * R
  · subst h0
    simp only [decide_true, ↓reduceIte, Nat.sub_self, Nat.zero_mul]
    exact i32_zero
  · simp only [h0, decide_false, Bool.false_eq_true, ↓reduceIte]
    have hlane : (addi (popc bal) (-1)).toNat % 32 = b - 31 * R - 1 := by
      have hn : (i32 (-1)).toNat = 2 ^ 32 - 1 := by
        show (truncBits 32 (BitVec.ofInt 64 (-1))).toNat = 2 ^ 32 - 1
        decide
      have hr : (r32 (W (b - 31 * R))).toNat = b - 31 * R := by
        rw [r32_W (by omega)]; exact toNat_W (by omega)
      rw [hpopc]
      show (BitVec.ofNat 64 ((r32 (W (b - 31 * R)) + i32 (-1)).toNat % 2 ^ 32)).toNat % 32 = _
      rw [BitVec.toNat_ofNat, BitVec.toNat_add, hr, hn]
      omega
    rw [hlane, psum5_W hp (by omega) (by omega), hf, H_W hp]
    have hsum := groupTiles_eq p (show 31 * R ≤ p.batch by omega)
      (show b - 31 * R - 1 + 1 ≤ 32 by omega)
    rw [show min 31 (b - 31 * R - 1 + 1) = b - 31 * R by omega,
      show 31 * R + (b - 31 * R) = b by omega, Nat.min_eq_right (by omega)] at hsum
    simp only [xs]
    have hle := le_work hp (tilePrefix p b - tilePrefix p (31 * R))
    have hle2 : (tilePrefix p b - tilePrefix p (31 * R)) * p.heads ≤ tilePrefix p b * p.heads :=
      Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    rw [show ∑ i ∈ Finset.range (b - 31 * R - 1 + 1), groupLaneTiles p (31 * R) i =
      tilePrefix p b - tilePrefix p (31 * R) by omega, mul32_W (by omega) (by omega) (by omega)]

set_option maxRecDepth 400000 in
/-- **The chosen request**: the first pass's choice is the request whose work holds the CTA, its
prefix and tile count are that request's, and the code's coordinates are the scheduler's. -/
theorem chosen_spec (hp : Pre p L m) {g R ns nv : Nat} {bal : BitVec 64} {d : D}
    (hg : g < L.threads)
    (hC : ChosenVals p L g R bal d ns nv) :
    ∃ b < p.batch, tilePrefix p b * p.heads ≤ g / L.block ∧
      g / L.block < tilePrefix p (b + 1) * p.heads ∧ chosen d = W b ∧
      coords p L g d = ⟨W (2 ^ 30 + 256 * (Epilogue.assignedCoordinates p b (g / L.block)).1),
        W (Epilogue.assignedCoordinates p b (g / L.block)).2,
        W (g / L.block - tilePrefix p b * p.heads),
        W (sectionWidth (requestTiles p b) p.heads * requestTiles p b),
        W ((g / L.block - tilePrefix p b * p.heads) %
          (sectionWidth (requestTiles p b) p.heads * requestTiles p b)),
        W (min (sectionWidth (requestTiles p b) p.heads)
          (p.heads - (g / L.block - tilePrefix p b * p.heads) /
            (sectionWidth (requestTiles p b) p.heads * requestTiles p b) *
              sectionWidth (requestTiles p b) p.heads))⟩ := by
  obtain ⟨hP, htot, hgx, hcur, hbal, hpv, hnt, -, -⟩ := hC
  obtain ⟨hlt, hf, hlow, hhigh, hgxv, hcurv⟩ := picked_group hp hg hP.pre
  obtain ⟨b, ⟨hb1, hb2, hb3, hb4, hb5⟩, -⟩ := groupContains_request p hlow hhigh
  have hS : Sel p (g / L.block) (31 * R) b := ⟨hb1, hb2, hb3, hb4, hb5⟩
  obtain ⟨hpopc, hzero⟩ := ballot hp hg hP.pre hS
  have hc := cta_lt hp hg
  have hbb := batch_lt hp
  have hhd := heads_lt hp
  have hchosen : chosen d = W b := by
    simp only [chosen, hbal, hgx, hgxv, hpopc]
    rw [add32_W (by omega)]; congr 1; omega
  -- The tile count of the chosen request.
  have hntv : d.nt = W (requestTiles p b) := by
    rw [hnt, ntv, hpopc, tlv_W hp (by rw [toNat_W (by omega)]; omega)]
    rw [toNat_W (by omega), Nat.mod_eq_of_lt (by omega), hf]
    simp only [xs, groupLaneTiles]
    split_ifs with h1
    · congr 2; omega
    · exact absurd ⟨by omega, by omega⟩ h1
  -- The work before the chosen request.
  have hmono := tilePrefix_mono p (show 31 * R ≤ b by omega)
  have hmono' := tilePrefix_mono p (show b ≤ min p.batch (31 * R + 31) by omega)
  have hw := work_lt hp (show min p.batch (31 * R + 31) ≤ p.batch by omega)
  have hwb := work_lt hp (show b ≤ p.batch by omega)
  have hwb1 := work_lt hp (show b + 1 ≤ p.batch by omega)
  have hw' := work_lt hp (show 31 * R ≤ p.batch by omega)
  have hpvv : d.pv = W ((tilePrefix p b - tilePrefix p (31 * R)) * p.heads) := by
    rw [hpv]; exact pvv_W hp hg hP.pre hS
  have hT := T_W hp (late := false) (r := R) (by omega)
  rw [hf] at hT
  have hle := le_work hp (tilePrefix p (min p.batch (31 * R + 31)) - tilePrefix p (31 * R))
  have hle3 : (tilePrefix p (min p.batch (31 * R + 31)) - tilePrefix p (31 * R)) * p.heads ≤
      tilePrefix p (min p.batch (31 * R + 31)) * p.heads := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hbase : sub32 d.cur (mul32 d.tot (headsW p)) = W (tilePrefix p (31 * R) * p.heads) := by
    rw [htot, hcur, hcurv, hT, show headsW p = W p.heads from H_W hp,
      mul32_W (by omega) (by omega) (by omega),
      sub32_W hle3 (by omega)]
    congr 1
    rw [← Nat.sub_mul, Nat.sub_sub_self (hmono.trans hmono')]
  have hitem : sub32 (ctaW L g) (add32 (sub32 d.cur (mul32 d.tot (headsW p))) d.pv) =
      W (g / L.block - tilePrefix p b * p.heads) := by
    have hle4 : (tilePrefix p b - tilePrefix p (31 * R)) * p.heads ≤ tilePrefix p b * p.heads :=
      Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    have hsplit : tilePrefix p (31 * R) * p.heads +
        (tilePrefix p b - tilePrefix p (31 * R)) * p.heads = tilePrefix p b * p.heads := by
      rw [← Nat.add_mul, Nat.add_sub_cancel' hmono]
    rw [hbase, hpvv, add32_W (by omega), hsplit, show ctaW L g = W (g / L.block) from rfl,
      sub32_W hb4 (by omega)]
  -- The coordinates.
  have hn1 := tilePrefix_succ p b
  have hrt := requestTiles_mul_le p b
  have hql : p.qLength b ≤ p.totalQ := by
    have := hp.qOffset_le_total (show b + 1 ≤ p.batch by omega)
    simp only [Params.qLength]; omega
  obtain ⟨hb0, -, -, -, -, htq⟩ := hp.shape
  have hcoord : Coord p (requestTiles p b) (g / L.block - tilePrefix p b * p.heads) := by
    have hm : tilePrefix p (b + 1) * p.heads =
        tilePrefix p b * p.heads + requestTiles p b * p.heads := by rw [hn1, Nat.add_mul]
    have ht1 : requestTiles p b * 256 < 2 ^ 30 := by
      have := hrt; have := hql; have := htq; have := hb0
      omega
    have hb5' := hb5
    rw [hm] at hb5'
    have hw1 := hwb1
    rw [hm] at hw1
    refine ⟨?_, ht1, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos (requestTiles p b) with h | h
      · rw [h, Nat.zero_mul] at hb5'; omega
      · exact h
    · generalize requestTiles p b * p.heads = nh at hb5' ⊢; omega
    · generalize requestTiles p b * p.heads = nh at hw1 ⊢; omega
  obtain ⟨hco, -, -⟩ := coords_W hp hcoord hitem hntv
  refine ⟨b, hb3, hb4, hb5, hchosen, ?_⟩
  rw [hco, Epilogue.assignedCoordinates]

/-- **The chosen request's coordinate divisions have rules** (the code's signed divisions by
the section's tile count and its head count). -/
theorem chosen_divOk (hp : Pre p L m) {g R ns nv : Nat} {bal : BitVec 64} {d : D}
    (hg : g < L.threads)
    (hC : ChosenVals p L g R bal d ns nv) :
    divOk (coords p L g d).n1 (coords p L g d).d1 = true ∧
      divOk (coords p L g d).n2 (coords p L g d).d2 = true := by
  obtain ⟨hP, htot, hgx, hcur, hbal, hpv, hnt, -, -⟩ := hC
  obtain ⟨hlt, hf, hlow, hhigh, hgxv, hcurv⟩ := picked_group hp hg hP.pre
  obtain ⟨b, ⟨hb1, hb2, hb3, hb4, hb5⟩, -⟩ := groupContains_request p hlow hhigh
  have hS : Sel p (g / L.block) (31 * R) b := ⟨hb1, hb2, hb3, hb4, hb5⟩
  obtain ⟨hpopc, hzero⟩ := ballot hp hg hP.pre hS
  have hc := cta_lt hp hg
  have hbb := batch_lt hp
  have hhd := heads_lt hp
  have hchosen : chosen d = W b := by
    simp only [chosen, hbal, hgx, hgxv, hpopc]
    rw [add32_W (by omega)]; congr 1; omega
  -- The tile count of the chosen request.
  have hntv : d.nt = W (requestTiles p b) := by
    rw [hnt, ntv, hpopc, tlv_W hp (by rw [toNat_W (by omega)]; omega)]
    rw [toNat_W (by omega), Nat.mod_eq_of_lt (by omega), hf]
    simp only [xs, groupLaneTiles]
    split_ifs with h1
    · congr 2; omega
    · exact absurd ⟨by omega, by omega⟩ h1
  -- The work before the chosen request.
  have hmono := tilePrefix_mono p (show 31 * R ≤ b by omega)
  have hmono' := tilePrefix_mono p (show b ≤ min p.batch (31 * R + 31) by omega)
  have hw := work_lt hp (show min p.batch (31 * R + 31) ≤ p.batch by omega)
  have hwb := work_lt hp (show b ≤ p.batch by omega)
  have hwb1 := work_lt hp (show b + 1 ≤ p.batch by omega)
  have hw' := work_lt hp (show 31 * R ≤ p.batch by omega)
  have hpvv : d.pv = W ((tilePrefix p b - tilePrefix p (31 * R)) * p.heads) := by
    rw [hpv]; exact pvv_W hp hg hP.pre hS
  have hT := T_W hp (late := false) (r := R) (by omega)
  rw [hf] at hT
  have hle := le_work hp (tilePrefix p (min p.batch (31 * R + 31)) - tilePrefix p (31 * R))
  have hle3 : (tilePrefix p (min p.batch (31 * R + 31)) - tilePrefix p (31 * R)) * p.heads ≤
      tilePrefix p (min p.batch (31 * R + 31)) * p.heads := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hbase : sub32 d.cur (mul32 d.tot (headsW p)) = W (tilePrefix p (31 * R) * p.heads) := by
    rw [htot, hcur, hcurv, hT, show headsW p = W p.heads from H_W hp,
      mul32_W (by omega) (by omega) (by omega),
      sub32_W hle3 (by omega)]
    congr 1
    rw [← Nat.sub_mul, Nat.sub_sub_self (hmono.trans hmono')]
  have hitem : sub32 (ctaW L g) (add32 (sub32 d.cur (mul32 d.tot (headsW p))) d.pv) =
      W (g / L.block - tilePrefix p b * p.heads) := by
    have hle4 : (tilePrefix p b - tilePrefix p (31 * R)) * p.heads ≤ tilePrefix p b * p.heads :=
      Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    have hsplit : tilePrefix p (31 * R) * p.heads +
        (tilePrefix p b - tilePrefix p (31 * R)) * p.heads = tilePrefix p b * p.heads := by
      rw [← Nat.add_mul, Nat.add_sub_cancel' hmono]
    rw [hbase, hpvv, add32_W (by omega), hsplit, show ctaW L g = W (g / L.block) from rfl,
      sub32_W hb4 (by omega)]
  -- The coordinates.
  have hn1 := tilePrefix_succ p b
  have hrt := requestTiles_mul_le p b
  have hql : p.qLength b ≤ p.totalQ := by
    have := hp.qOffset_le_total (show b + 1 ≤ p.batch by omega)
    simp only [Params.qLength]; omega
  obtain ⟨hb0, -, -, -, -, htq⟩ := hp.shape
  have hcoord : Coord p (requestTiles p b) (g / L.block - tilePrefix p b * p.heads) := by
    have hm : tilePrefix p (b + 1) * p.heads =
        tilePrefix p b * p.heads + requestTiles p b * p.heads := by rw [hn1, Nat.add_mul]
    have ht1 : requestTiles p b * 256 < 2 ^ 30 := by
      have := hrt; have := hql; have := htq; have := hb0
      omega
    have hb5' := hb5
    rw [hm] at hb5'
    have hw1 := hwb1
    rw [hm] at hw1
    refine ⟨?_, ht1, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos (requestTiles p b) with h | h
      · rw [h, Nat.zero_mul] at hb5'; omega
      · exact h
    · generalize requestTiles p b * p.heads = nh at hb5' ⊢; omega
    · generalize requestTiles p b * p.heads = nh at hw1 ⊢; omega
  obtain ⟨hco, h1, h2⟩ := coords_W hp hcoord hitem hntv
  rw [hco]
  exact ⟨h1, h2⟩


/-- **A scan that ended at a group of the batch picked a request of the batch**: the CTA's work
item lies in the group (`picked_group`), so the ballot counts the requests before it
(`ballot`) and the chosen request is it, below the batch. -/
theorem picked_of_pre (hp : Pre p L m) {g R : Nat} {bal : BitVec 64} (hg : g < L.threads)
    (h : PickedPre p L g R bal) : Picked p L g R bal := by
  refine ⟨h.1, h.2.1, h.2.2, ?_⟩
  obtain ⟨hlt, hf, hlow, hhigh, hgxv, hcurv⟩ := picked_group hp hg h
  obtain ⟨b, ⟨hb1, hb2, hb3, hb4, hb5⟩, -⟩ := groupContains_request p hlow hhigh
  have hS : Sel p (g / L.block) (31 * R) b := ⟨hb1, hb2, hb3, hb4, hb5⟩
  obtain ⟨hpopc, hzero⟩ := ballot hp hg h hS
  have hbb := batch_lt hp
  have hchosen : chosen (chosenD p (g / L.block) R bal) = W b := by
    simp only [chosen, chosenD, hgxv, hpopc]
    rw [add32_W (by omega)]; congr 1; omega
  rw [hchosen, show paramW p.batch = W p.batch from r32_W (by omega),
    scmp_lt_W (by omega) (by omega)]
  exact decide_eq_true (by omega)

/-! ### The first pass's collectives -/

/-- The sites of the second pass and its return. -/
def Site.late : Site → Bool
  | .word k | .down k | .up k _ | .total k => k.late
  | .vote l | .pre l | .tiles l | .exit l => l
  | _ => false

/-- A reached round is at most the batch. -/
theorem reached_le (hp : Pre p L m) {c : Nat} {late : Bool} {r : Nat}
    (hr : Reached p c late r) : r ≤ p.batch := by
  rcases Nat.eq_zero_or_pos r with rfl | h
  · omega
  · have := (reached_first hp hr h).1; omega

theorem chosen_coll_le (hp : Pre p L m) {g R : Nat} {b : BitVec 64} {d : D} {ns nv : Nat}
    (hC : ChosenVals p L g R b d ns nv) : ns + nv ≤ 7 * (p.batch + 3) + 6 := by
  obtain ⟨hP, -, -, -, -, -, -, hns, hnv⟩ := hC
  have := reached_le hp hP.1.1
  have := (selN_pos b).2
  omega

/-- **A state of the first pass is past at most `7 (batch + 3) + 6` warp collectives.** -/
theorem fits_coll_le (hp : Pre p L m) {g : Nat} {d : D} {ns nv : Nat}
    (hF : Fits p L g d ns nv) (hl : d.site.late = false) : ns + nv ≤ 7 * (p.batch + 3) + 6 := by
  have hsel : ∀ b : BitVec 64, selN b ≤ 2 := fun b => (selN_pos b).2
  obtain ⟨s, w, dn, tl, u1, u2, u4, u8, u16, tot, grp, acc, gx, cur, bal, pv, nt, c0, c1⟩ := d
  cases s <;> simp only [Site.late] at hl <;> simp only [Fits] at hF
  case start => omega
  case word k | down k | up k j | total k =>
    obtain ⟨r, n0, v0, hP, hR, hns, hnv, -⟩ := hF
    rw [hl, passStart_false] at hP
    have := reached_le hp hR.1
    omega
  case vote l | pre l =>
    obtain ⟨R, n0, v0, hP, hE, hns, hnv, -⟩ := hF
    subst hl
    rw [passStart_false] at hP
    have := reached_le hp hE.1.1
    omega
  case tiles l =>
    obtain ⟨R, n0, v0, hP, hE, hns, hnv, -⟩ := hF
    subst hl
    rw [passStart_false] at hP
    have := reached_le hp hE.1.1
    have := hsel bal
    omega
  case exit l =>
    subst hl
    obtain ⟨n0, v0, hP, R, hE, h⟩ := hF
    rw [passStart_false] at hP
    have := reached_le hp hE.1
    rcases h with ⟨-, h1, h2⟩ | ⟨b, -, -, h1, h2, -⟩
    · omega
    · have := hsel b; omega
  case q0 => obtain ⟨R, b, hC⟩ := hF; exact chosen_coll_le hp hC
  case q1 => obtain ⟨R, b, hC, -⟩ := hF; exact chosen_coll_le hp hC
  all_goals obtain ⟨R, b, hC, -⟩ := hF; exact chosen_coll_le hp hC

end
end PTX.Kernels.TmlFa4Fwd.Proof.Epilogue
