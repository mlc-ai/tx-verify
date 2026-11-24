-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Common.Inj
public import Core.Assembly.Execution
public import Core.Data.Types
public import Core.Data.Value
public import Core.Source.Instr
public import Core.Thread.Access
public import Core.Thread.Local
public import Core.Thread.Run
public import Kernels.TmlFa4Fwd.Assumptions
public import Kernels.TmlFa4Fwd.Proof.Common.Roles
public import Kernels.TmlFa4Fwd.Proof.LdWarp.Fits
public import Kernels.TmlFa4Fwd.Proof.LdWarp.Round
public import Kernels.TmlFa4Fwd.Proof.Loader.Machine
public import Kernels.TmlFa4Fwd.Proof.Loader.Shape
public import Kernels.TmlFa4Fwd.Proof.Loader.ShapeAll
public import Kernels.TmlFa4Fwd.Spec
public import Lemmas.Flow.Arith32
public import Lemmas.Flow.Arith32Word
public import Lemmas.Flow.Code
public import Lemmas.Kernel.Frame
import Kernels.TmlFa4Fwd.Flow.Code.Part007
import Kernels.TmlFa4Fwd.Flow.Code.Part014
import Kernels.TmlFa4Fwd.Flow.Code.Part022
import Kernels.TmlFa4Fwd.Proof.Lib.InputRead
import Kernels.TmlFa4Fwd.Proof.Epilogue.Reads
import Kernels.TmlFa4Fwd.Proof.LdWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Lib.LoadAl
import Lemmas.Flow.AllocTmpl
import Lemmas.Flow.WordBound
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader's page-table loads read the launch's page table

At a page-table load (`pgLd`) the reference values (`LFits`, its block part `PgOk`) give the setup
words as the setup of the chosen request (`setup`, with the request's used-K word `kLength i`),
the later blocks' first block `%r56 = %r28 - 2`, the round (`Rounds`), and the round's condition
(`rowCond`: the row is below the used length, signed). The row is a lane's row in a block of the
tile, so it is nonnegative and below `2 ^ 31` (the tile's blocks are at most `kLength i / 128 + 1`,
`r28_le`); with the condition it is below `kLength i`. So the page index (`pgIdx`, the code's
multiply-high division) is `row / 16 < (kLength i + 15) / 16`, the address is the launch's
page-table word `pageTableBase + 4 (i stride + row / 16)` (`Pre.pageTable`, `Pre.ranges`), and
the load returns the launch's word there (`inputReadValue` with `Pre.pageBytes`). This
discharges the loader warps' page-table premise (`LdWarp.pgSrc`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (chosen)
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (ukv)

noncomputable section

variable {p : Params} {L : Launch} {g : Nat}

/-! ### The tile's blocks -/

theorem cdivS_W {k : Nat} (hk : k < 2 ^ 31) : cdivS (W k) = W (k / 128) := by
  have h1 : shrs (W k) 31 = W 0 := by
    have := toNat_shrs_W hk (k := 31) (by decide)
    rw [show k / 2 ^ 31 = 0 by omega] at this
    exact this
  have h2 : shru (W 0) 25 = W 0 := by decide
  have h3 : add32 (W k) (W 0) = W k := by rw [add32_W (by omega)]; rfl
  have h4 := toNat_shrs_W hk (k := 7) (by decide)
  simp only [cdivS, h1, h2, h3]
  exact h4

theorem sv_min32_le (x y : BitVec 64) : sv (min32 x y) ≤ sv x := by
  have hx : sv (r32 x) = sv x := sv_r32 x
  have hy : sv (r32 y) = sv y := sv_r32 y
  simp only [min32]
  split <;> rename_i h
  · rw [hx]
  · simp only [PTX.compare] at h
    rw [hy]
    simp only [sv] at hx hy ⊢
    rw [hx, hy] at h
    simp at h
    omega

/-- **The tile's blocks are at most the used length's blocks plus one.** -/
theorem r28_le (v : V) {k : Nat} (hu : v.ukw = W k) (hk : k < 2 ^ 31 - 256) :
    sv (setup p L g v).r28 ≤ (k / 128 : Nat) + 1 := by
  have h1 := sv_min32_le
    (add32 (cdivS v.ukw) (sel (cdivP v.ukw) (i32 1) (i32 0)))
    (add32 (cdivS (addi (add32 (add32 (shl v.co.row 8) v.ukw) (sub32 v.sc.c0 v.sc.c1)) 256))
      (sel (cdivP (addi (add32 (add32 (shl v.co.row 8) v.ukw) (sub32 v.sc.c0 v.sc.c1)) 256))
        (i32 1) (i32 0)))
  have h2 : sv (add32 (cdivS v.ukw) (sel (cdivP v.ukw) (i32 1) (i32 0))) ≤
      (k / 128 : Nat) + 1 := by
    rw [hu, cdivS_W (by omega)]
    cases cdivP (W k)
    · rw [show sel false (i32 1) (i32 0) = W 0 from rfl, add32_W (by omega), sv_W (by omega)]
      omega
    · rw [show sel true (i32 1) (i32 0) = W 1 from rfl, add32_W (by omega), sv_W (by omega)]
      push_cast; omega
  simp only [setup]
  exact le_trans h1 h2

theorem sv_cdivS (z : BitVec 64) : -2 ^ 24 ≤ sv (cdivS z) ∧ sv (cdivS z) < 2 ^ 24 := by
  have h7 : (i32 7).toNat = 7 := by decide
  have hs := toSigned32_spec (r32 (add32 z (shru (shrs z 31) 25)))
  have he : cdivS z = i32 (toSigned 32 (r32 (add32 z (shru (shrs z 31) 25))) / 2 ^ 7) := by
    show i32 (toSigned 32 (r32 (add32 z (shru (shrs z 31) 25))) / 2 ^ min (i32 7).toNat 32) = _
    rw [h7]; rfl
  rw [he, sv_i32 (by omega) (by omega)]
  omega

theorem sv_cdiv1 (z : BitVec 64) (c : Bool) :
    -2 ^ 24 ≤ sv (add32 (cdivS z) (sel c (i32 1) (i32 0))) := by
  have h := sv_cdivS z
  have ha : ∀ n : Int, 0 ≤ n → n ≤ 1 → add32 (cdivS z) (i32 n) = addi (cdivS z) n := by
    intro n _ _
    have : r32 (i32 n) = i32 n := r32_of_lt (toNat_r32_lt (BitVec.ofInt 64 n))
    show truncBits 32 (r32 (cdivS z) + r32 (i32 n)) = truncBits 32 (r32 (cdivS z) + i32 n)
    rw [this]
  simp only [sv] at h ⊢
  cases c
  · rw [show sel false (i32 1) (i32 0) = i32 0 from rfl, ha 0 (by omega) (by omega),
      toSigned_addi _ _ (by omega) (by omega)]
    omega
  · rw [show sel true (i32 1) (i32 0) = i32 1 from rfl, ha 1 (by omega) (by omega),
      toSigned_addi _ _ (by omega) (by omega)]
    omega

theorem sv_min32_ge (x y : BitVec 64) : min (sv x) (sv y) ≤ sv (min32 x y) := by
  have hx : sv (r32 x) = sv x := sv_r32 x
  have hy : sv (r32 y) = sv y := sv_r32 y
  simp only [min32]
  split <;> rename_i h
  · rw [hx]; omega
  · rw [hy]; omega

/-- **The tile's blocks are above `-2 ^ 24`** (each operand of the code's minimum is a signed
shift by 7 plus at most one). -/
theorem r28_ge (v : V) : -2 ^ 24 ≤ sv (setup p L g v).r28 := by
  have h1 := sv_min32_ge
    (add32 (cdivS v.ukw) (sel (cdivP v.ukw) (i32 1) (i32 0)))
    (add32 (cdivS (addi (add32 (add32 (shl v.co.row 8) v.ukw) (sub32 v.sc.c0 v.sc.c1)) 256))
      (sel (cdivP (addi (add32 (add32 (shl v.co.row 8) v.ukw) (sub32 v.sc.c0 v.sc.c1)) 256))
        (i32 1) (i32 0)))
  have h2 := sv_cdiv1 v.ukw (cdivP v.ukw)
  have h3 := sv_cdiv1 (addi (add32 (add32 (shl v.co.row 8) v.ukw) (sub32 v.sc.c0 v.sc.c1)) 256)
    (cdivP (addi (add32 (add32 (shl v.co.row 8) v.ukw) (sub32 v.sc.c0 v.sc.c1)) 256))
  simp only [setup]
  omega

theorem setup_r35 (v : V) : (setup p L g v).r35 =
    or32 (add32 (andi (shru (tidW L g) 3) 7) (andi (shl (tidW L g) 3) 56))
      (sel (scmpi .gt .s (setup p L g v).r28 0) (shl (addi (setup p L g v).r28 (-1)) 7)
        (i32 0)) := by
  simp only [setup]

theorem setup_rd11 (v : V) : (setup p L g v).rd11 = ptRow p v := by
  simp only [setup]

/-! ### The rows of the page rounds -/

theorem toNat_r32_r32 (x : BitVec 64) : (r32 (r32 x)).toNat = (r32 x).toNat := by
  rw [r32_of_lt (toNat_r32_lt x)]

theorem lane_add_le (L : Launch) (g : Nat) :
    (r32 (add32 (andi (shru (tidW L g) 3) 7) (andi (shl (tidW L g) 3) 56))).toNat ≤ 63 := by
  rw [r32_of_lt (toNat_add32_lt _ _)]
  have h1 := toNat_add32_le (andi (shru (tidW L g) 3) 7) (andi (shl (tidW L g) 3) 56)
  have h2 := toNat_andi_le (shru (tidW L g) 3) 7
  have h3 := toNat_andi_le (shl (tidW L g) 3) 56
  have h7 : (i32 7).toNat = 7 := by decide
  have h56 : (i32 56).toNat = 56 := by decide
  rw [r32_of_lt (by have := toNat_r32_lt (shru (tidW L g) 3); simp only [andi] at h2 ⊢; omega)]
    at h1
  rw [r32_of_lt (by simp only [andi] at h3 ⊢; omega)] at h1
  omega

theorem lane_or_lt (L : Launch) (g : Nat) :
    (r32 (or32 (andi (shru (tidW L g) 3) 7) (andi (shl (tidW L g) 3) 56))).toNat < 2 ^ 7 := by
  have h2 := toNat_andi_le (shru (tidW L g) 3) 7
  have h3 := toNat_andi_le (shl (tidW L g) 3) 56
  have h7 : (i32 7).toNat = 7 := by decide
  have h56 : (i32 56).toNat = 56 := by decide
  have ha : (andi (shru (tidW L g) 3) 7).toNat < 2 ^ 7 := by omega
  have hb : (andi (shl (tidW L g) 3) 56).toNat < 2 ^ 7 := by omega
  have hor : (or32 (andi (shru (tidW L g) 3) 7) (andi (shl (tidW L g) 3) 56)).toNat < 2 ^ 7 := by
    simp only [or32, BitVec.toNat_or]
    rw [r32_of_lt (by omega), r32_of_lt (by omega)]
    exact Nat.or_lt_two_pow ha hb
  rw [r32_of_lt (by omega)]
  exact hor

theorem it_le (it : Fin 2) : (r32 (shl (i32 (it.val : Int)) 6)).toNat ≤ 64 := by
  fin_cases it <;> decide

/-- A left shift by 7 is a multiple of 128 below `2 ^ 32`, at most the shifted word times 128. -/
theorem shl7_facts (x : BitVec 64) :
    (r32 (shl x 7)).toNat % 2 ^ 7 = 0 ∧ (r32 (shl x 7)).toNat ≤ (r32 x).toNat * 128 := by
  have h : (shl x 7).toNat = (r32 x).toNat * 2 ^ 7 % 2 ^ 32 := toNat_shl (k := 7) x (by decide)
  have hlt : (shl x 7).toNat < 2 ^ 32 := by rw [h]; omega
  rw [r32_of_lt hlt, h]
  constructor <;> omega

/-- **The prime block's rows**: below the used length's blocks times 128, plus a block. -/
theorem row_prime_le (v₀ : V) {k : Nat} (hu : v₀.ukw = W k) (hk : k < 2 ^ 31 - 256)
    (it : Fin 2) : (add32 (setup p L g v₀).r35 (shl (i32 (it.val : Int)) 6)).toNat ≤ k + 127 := by
  have hB := r28_le (p := p) (L := L) (g := g) v₀ hu hk
  rw [setup_r35]
  generalize (setup p L g v₀).r28 = b at hB
  have ha := lane_add_le L g
  have hb : (r32 (sel (scmpi .gt .s b 0) (shl (addi b (-1)) 7) (i32 0))).toNat % 2 ^ 7 = 0 ∧
      (r32 (sel (scmpi .gt .s b 0) (shl (addi b (-1)) 7) (i32 0))).toNat ≤ 128 * (k / 128) := by
    rw [scmpi_gt_s _ (by decide) (by decide)]
    by_cases hc : (0 : Int) < sv b
    · simp only [hc, decide_true, sel, ↓reduceIte]
      obtain ⟨h1, h2⟩ := shl7_facts (addi b (-1))
      have h3 : sv (addi b (-1)) = sv b - 1 := sv_addi_neg1 b (by omega)
      simp only [sv] at h3 hB hc
      have h4 := toNat_r32_of_toSigned (x := addi b (-1)) (by omega)
      refine ⟨h1, ?_⟩
      have : (r32 (addi b (-1))).toNat ≤ k / 128 := by omega
      omega
    · simp only [hc, decide_false, sel, Bool.false_eq_true, ↓reduceIte]
      rw [show (r32 (i32 0)).toNat = 0 by decide]
      omega
  have hor : (r32 (or32 (add32 (andi (shru (tidW L g) 3) 7) (andi (shl (tidW L g) 3) 56))
      (sel (scmpi .gt .s b 0) (shl (addi b (-1)) 7) (i32 0)))).toNat ≤ 63 + 128 * (k / 128) := by
    have h1 := toNat_or32_add (k := 7) (Nat.lt_of_le_of_lt ha (by decide)) hb.1
    have h2 := hb.2
    have h3 : (r32 (add32 (andi (shru (tidW L g) 3) 7) (andi (shl (tidW L g) 3) 56)) |||
        r32 (sel (scmpi .gt .s b 0) (shl (addi b (-1)) 7) (i32 0))).toNat < 2 ^ 32 := by
      rw [h1]; omega
    simp only [or32]
    rw [r32_of_lt h3, h1]
    omega
  have := toNat_add32_le (or32 (add32 (andi (shru (tidW L g) 3) 7) (andi (shl (tidW L g) 3) 56))
      (sel (scmpi .gt .s b 0) (shl (addi b (-1)) 7) (i32 0))) (shl (i32 (it.val : Int)) 6)
  have := it_le it
  omega

/-- The block offset of a later round (`%r56 - rnd`): below the used length's blocks. -/
theorem r84_le {v : V} {k r : Nat} (hB : sv v.su.r28 ≤ (k / 128 : Nat) + 1)
    (h56 : v.r56 = addi v.su.r28 (-2)) (hr : v.rnd = W r) (hr2 : (r : Int) + 2 ≤ sv v.su.r28) :
    (r32 (sub32 v.r56 v.rnd)).toNat + 1 ≤ k / 128 := by
  have h2 : sv v.rnd = r := by rw [hr]; exact sv_W (by have := sv_spec v.su.r28; omega)
  simp only [sv] at hB hr2 h2
  have hs := toSigned32_spec v.su.r28
  have h1 : toSigned 32 v.r56 = toSigned 32 v.su.r28 - 2 := by
    rw [h56]; exact toSigned_addi _ _ (by omega) (by omega)
  have h3 : toSigned 32 (sub32 v.r56 v.rnd) = toSigned 32 v.su.r28 - 2 - r := by
    rw [toSigned_sub32 _ _ (by omega) (by omega)]
    omega
  have h4 := toNat_r32_of_toSigned (x := sub32 v.r56 v.rnd) (by omega)
  omega

/-- **A later round's rows**: below the used length's blocks times 128. -/
theorem row_later_le {v : V} {k r : Nat} (per : Per) (hper : per ≠ .prime) (it : Fin 2)
    (hk : k < 2 ^ 31 - 256) (hB : sv v.su.r28 ≤ (k / 128 : Nat) + 1)
    (h56 : v.r56 = addi v.su.r28 (-2)) (hr : v.rnd = W r)
    (hr2 : (r : Int) + 2 ≤ sv v.su.r28) : (row0 p L g v per it).toNat ≤ k + 63 := by
  have h84 := r84_le hB h56 hr hr2
  obtain ⟨hm, hle⟩ := shl7_facts (sub32 v.r56 v.rnd)
  have hl := lane_or_lt L g
  have hit := it_le it
  cases per
  · exact absurd rfl hper
  · show (add32 (add32 (or32 (andi (shru (tidW L g) 3) 7) (andi (shl (tidW L g) 3) 56))
      (shl (sub32 v.r56 v.rnd) 7)) (shl (i32 (it.val : Int)) 6)).toNat ≤ k + 63
    have h1 := toNat_add32_le (add32 (or32 (andi (shru (tidW L g) 3) 7)
      (andi (shl (tidW L g) 3) 56)) (shl (sub32 v.r56 v.rnd) 7)) (shl (i32 (it.val : Int)) 6)
    have h2 := toNat_add32_le (or32 (andi (shru (tidW L g) 3) 7) (andi (shl (tidW L g) 3) 56))
      (shl (sub32 v.r56 v.rnd) 7)
    rw [r32_of_lt (toNat_add32_lt _ _)] at h1
    omega
  · show (add32 (or32 (or32 (andi (shru (tidW L g) 3) 7) (andi (shl (tidW L g) 3) 56))
      (shl (sub32 v.r56 v.rnd) 7)) (shl (i32 (it.val : Int)) 6)).toNat ≤ k + 63
    have h1 := toNat_add32_le (or32 (or32 (andi (shru (tidW L g) 3) 7)
      (andi (shl (tidW L g) 3) 56)) (shl (sub32 v.r56 v.rnd) 7)) (shl (i32 (it.val : Int)) 6)
    have h2 := toNat_or32_add (k := 7) hl hm
    have h5 : (r32 (shl (sub32 v.r56 v.rnd) 7)).toNat ≤ 128 * (k / 128) - 128 := by omega
    have h3 : (r32 (or32 (andi (shru (tidW L g) 3) 7) (andi (shl (tidW L g) 3) 56)) |||
        r32 (shl (sub32 v.r56 v.rnd) 7)).toNat < 2 ^ 32 := by
      rw [h2]; have : k / 128 < 2 ^ 25 := by omega
      omega
    have h6 : (r32 (or32 (or32 (andi (shru (tidW L g) 3) 7) (andi (shl (tidW L g) 3) 56))
        (shl (sub32 v.r56 v.rnd) 7))).toNat ≤ 127 + (128 * (k / 128) - 128) := by
      simp only [or32] at h3 ⊢
      rw [r32_of_lt h3, h2]
      omega
    omega

/-! ### The page index and the address -/

theorem toNat_trunc64 (y : BitVec 64) : (truncBits 64 y).toNat = y.toNat := by
  simp only [truncBits, BitVec.toNat_ofNat]; omega

theorem shrur_i32 (x : BitVec 64) {n : Nat} (hn : (r32 (i32 (n : Int))).toNat = n) (h : n < 32) :
    (shrur x (i32 (n : Int))).toNat = (r32 x).toNat / 2 ^ n := by
  simp only [shrur]
  rw [hn, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]

theorem hiWord_zero {y : BitVec 64} (hy : y.toNat < 2 ^ 32) : hiWord y = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp only [hiWord, truncBits, BitVec.toNat_ofNat]
  rw [Nat.div_eq_of_lt (show y.toNat < 4294967296 by omega)]
  rfl

theorem toNat_zero64 : (0 : BitVec 64).toNat = 0 := rfl

/-- **The page index of a row below `2 ^ 31` is the row divided by 16.** -/
theorem pgIdx_eq {x : BitVec 64} (h : x.toNat < 2 ^ 31) : pgIdx x = W (x.toNat / 16) := by
  have hx : r32 x = x := r32_of_lt (by omega)
  have hm : (mul64 (BitVec.ofNat 64 1) (zext x)).toNat < 2 ^ 32 := by
    unfold mul64 zext r64
    rw [toNat_trunc64, BitVec.toNat_mul, toNat_trunc64, toNat_trunc64, toNat_trunc64, hx,
      show (BitVec.ofNat 64 1).toNat = 1 from rfl]
    omega
  rw [pgIdx, hiWord_zero hm]
  have h0 : r32 (0 : BitVec 64) = 0 := rfl
  have hs : sub32 x 0 = x := by
    apply BitVec.eq_of_toNat_eq
    unfold sub32
    have hz : x - (0 : BitVec 64) = x := by apply BitVec.eq_of_toNat_eq; simp
    rw [hx, h0, hz, show truncBits 32 x = r32 x from rfl, hx]
  rw [hs]
  have h1 := shrur_i32 x (n := 1) (by decide) (by decide)
  rw [show ((1 : Nat) : Int) = 1 from rfl, hx] at h1
  have h1' : (shrur x (i32 1)).toNat < 2 ^ 32 := by rw [h1]; omega
  have ha : add32 (shrur x (i32 1)) 0 = shrur x (i32 1) := by
    unfold add32
    have hz : r32 (shrur x (i32 1)) + (0 : BitVec 64) = r32 (shrur x (i32 1)) := by
      apply BitVec.eq_of_toNat_eq; simp
    rw [h0, hz, show truncBits 32 (r32 (shrur x (i32 1))) =
      r32 (r32 (shrur x (i32 1))) from rfl, r32_of_lt (toNat_r32_lt _), r32_of_lt h1']
  rw [ha]
  apply BitVec.eq_of_toNat_eq
  have h3 := shrur_i32 (shrur x (i32 1)) (n := 3) (by decide) (by decide)
  rw [show ((3 : Nat) : Int) = 3 from rfl, r32_of_lt h1', h1] at h3
  rw [h3, W, BitVec.toNat_ofNat]
  omega

theorem sext_W {i : Nat} (h : i < 2 ^ 31) : sext (W i) = W i := by
  apply BitVec.eq_of_toNat_eq
  simp [sext, cvtIntBits, intBits, intSat, intOf, r32, truncBits, toSigned]
  omega

theorem wide4_W {q : Nat} (h : q < 2 ^ 29) : wide4 (W q) = W (4 * q) := by
  have h1 : toSigned 32 (r32 (W q)) = q := by rw [r32_W (by omega)]; exact toSigned_W (by omega)
  have h4 : toSigned 32 (i32 4) = 4 := by decide
  simp only [wide4, mulWide, h1, h4]
  apply BitVec.eq_of_toNat_eq
  simp only [beq_self_eq_true, ↓reduceIte, truncBits, BitVec.toNat_ofNat, W]
  rw [show (q : Int) * 4 = ((4 * q : Nat) : Int) by push_cast; ring, BitVec.ofInt_natCast]
  simp only [BitVec.toNat_ofNat]
  omega

/-- **The page-table word's address.** -/
theorem ptAddr_toNat {B S i q : Nat} (hi : i < 2 ^ 31) (hq : q < 2 ^ 29) (hS : S < 2 ^ 64)
    (hfit : B + 4 * (S * i + q) < 2 ^ 64) :
    (add64 (add64 (BitVec.ofNat 64 B) (shl64 (mul64 (BitVec.ofNat 64 S) (sext (W i))) 2))
      (wide4 (W q))).toNat = B + 4 * (S * i + q) := by
  rw [sext_W hi, wide4_W hq]
  have h2 : (i32 2).toNat = 2 := by decide
  have hm : (mul64 (BitVec.ofNat 64 S) (W i)).toNat = S * i := by
    simp only [mul64, r64, toNat_trunc64, BitVec.toNat_mul, W, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt hS, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega)]
    omega
  have hsh : (shl64 (mul64 (BitVec.ofNat 64 S) (W i)) 2).toNat = 4 * (S * i) := by
    unfold shl64
    rw [h2, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), toNat_trunc64,
      BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, r64, toNat_trunc64, hm]
    omega
  simp only [add64, r64, toNat_trunc64, BitVec.toNat_add, hsh, W, BitVec.toNat_ofNat]
  omega

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader

namespace PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
open PTX PTX.Proof PTX.Flow
open PTX.Flow.Arith32
open PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX.Kernels.TmlFa4Fwd.Proof.Epilogue (chosen)
open PTX.Kernels.TmlFa4Fwd.Proof.Mma (ukv)

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {g : Nat}

/-- The row of a page round at a state with the reference values: at most the used length plus
a block. -/
theorem row_le (hp : Pre p L m) {d : D} {ns nv nc i : Nat} {per : Per} {it : Fin 2}
    (hb : d.site.blk = true) (hs : d.site = .pgLd per it) (hF : LFits p L g d ns nv nc)
    (hi : i < p.batch) (hku : d.v.ukw = W (p.kLength i)) :
    (row0 p L g d.v per it).toNat ≤ p.kLength i + 127 := by
  obtain ⟨-, -, -, ⟨-, hR⟩, ⟨v₀, hsu, hu0, -⟩, -, h56, -⟩ := lfits_blk_of hb hF
  have hk : p.kLength i < 2 ^ 31 - 256 := by have := (hp.lengths i hi).2.2; omega
  have hu : v₀.ukw = W (p.kLength i) := hu0.trans hku
  have hB : sv d.v.su.r28 ≤ (p.kLength i / 128 : Nat) + 1 := by
    rw [hsu]; exact r28_le v₀ hu hk
  have hG : -2 ^ 24 ≤ sv d.v.su.r28 := by rw [hsu]; exact r28_ge v₀
  have h56' : per ≠ .prime → d.v.r56 = addi d.v.su.r28 (-2) := fun hper =>
    h56 (by rw [hs]; cases per <;> simp_all [bc])
  rw [hs] at hR
  cases per
  · show (add32 d.v.su.r35 (shl (i32 (it.val : Int)) 6)).toNat ≤ _
    rw [hsu]
    exact row_prime_le v₀ hu hk it
  · simp only [RoundsB, bc, inBlk] at hR
    obtain ⟨r, hr, h2, hlt, -⟩ := hR
    have : (r : Int) + 2 ≤ sv d.v.su.r28 := by
      have := sv_addi_neg1 d.v.su.r28 (by omega)
      unfold wRn at hlt
      omega
    have := row_later_le (p := p) (L := L) (g := g) .warm (by decide) it hk hB
      (h56' (by decide)) hr this
    omega
  · simp only [RoundsB, bc, inBlk] at hR
    obtain ⟨r, hr, -, hlt, -⟩ := hR
    have : (r : Int) + 2 ≤ sv d.v.su.r28 := by
      have := sv_addi_neg1 d.v.su.r28 (by omega)
      omega
    have := row_later_le (p := p) (L := L) (g := g) .steady (by decide) it hk hB
      (h56' (by decide)) hr this
    omega

theorem rv_pg (w : Nat) (v : V) (kk : Fin 2) (per : Per) (it : Fin 2) :
    rv p L g w ⟨.pgLd per it, v, kk⟩ (pgLdA per) =
      add64 (match per with | .prime => v.su.rd11 | _ => ptRow p v)
        (wide4 (pgIdx (row0 p L g v per it))) := by
  cases per
  · simp [rv, valueOf, values, valuesPgPrime, lookupLit, pgLdA, truncBits64, row0, Epilogue.vbits]
  · simp [rv, valueOf, values, valuesPgWarm, lookupLit, pgLdA, truncBits64, Epilogue.vbits]
  · simp [rv, valueOf, values, valuesPgSteady, lookupLit, pgLdA, truncBits64, Epilogue.vbits]

set_option maxHeartbeats 1000000 in
/-- **The address of a page-table load**: the launch's page-table word of the chosen request's row.
-/
theorem pg_addr (hp : Pre p L m) {d : D} {ns nv nc : Nat} {per : Per} {it : Fin 2}
    (hF : LFits p L g d ns nv nc) (hs : d.site = .pgLd per it) (w : Nat) :
    ∃ i q, i < p.batch ∧ q < (p.kLength i + 15) / 16 ∧
      (rv p L g w d (pgLdA per) + BitVec.ofInt 64 0).toNat =
        p.pageTableBase + 4 * (i * p.pageTableStride + q) ∧
      chosen d.v.sc = W i ∧ q = (row0 p L g d.v per it).toNat / 16 := by
  have hb : d.site.blk = true := by rw [hs]; cases per <;> rfl
  obtain ⟨-, hFE, -, -, ⟨v₀, hsu, -, hsc0⟩, hukw, -, hrow⟩ := lfits_blk_of hb hF
  simp only [Epilogue.Fits, toE, epi_blk hb] at hFE
  obtain ⟨R, bal, hC, -⟩ := hFE
  obtain ⟨i, hi, hib⟩ := Epilogue.chosen_W hp hC
  have hc : chosen d.v.sc = W i := hi
  have hbt := Epilogue.batch_lt hp
  have hku : d.v.ukw = W (p.kLength i) := by
    rw [hukw, hc]
    simp only [ukv, r32_W (show i < 2 ^ 32 by omega), toNat_W (show i < 2 ^ 64 by omega)]
  have hrl := row_le hp hb hs hF (by omega) hku
  have hk : p.kLength i + 256 < 2 ^ 31 := (hp.lengths i (by omega)).2.2
  have hcond := hrow per it hs
  have hx32 : (row0 p L g d.v per it).toNat < 2 ^ 31 := by omega
  have hsx : sv (row0 p L g d.v per it) = (row0 p L g d.v per it).toNat := by
    simp only [sv, toSigned]
    rw [Nat.mod_eq_of_lt (by omega)]
    simp only [show (row0 p L g d.v per it).toNat < 2 ^ (32 - 1) by omega, ↓reduceIte]
  have hsk : sv d.v.ukw = p.kLength i := by rw [hku]; exact sv_W (by omega)
  have hxlt : (row0 p L g d.v per it).toNat < p.kLength i := by
    have h' : scmp .ge .s (row0 p L g d.v per it) d.v.ukw = false := by
      unfold rowCond at hcond
      split at hcond
      · exact hcond
      · rwa [geW_eq] at hcond
    rw [scmp_ge_s, hsx, hsk] at h'
    simp only [decide_eq_false_iff_not, not_le] at h'
    omega
  -- the page-table word
  obtain ⟨hpt, -⟩ := hp.pageTable i (by omega)
  have hroom : p.pageTableBase + 4 * p.batch * p.pageTableStride ≤ 2 ^ 64 :=
    hp.ranges ⟨p.pageTableBase, 4 * p.batch * p.pageTableStride⟩ (by simp [Params.inputRegions])
  set q := (row0 p L g d.v per it).toNat / 16 with hqdef
  have hq : q < (p.kLength i + 15) / 16 := by omega
  have hmul : p.pageTableStride * (i + 1) ≤ p.pageTableStride * p.batch :=
    Nat.mul_le_mul_left _ (by omega)
  have hle : p.pageTableStride ≤ p.pageTableStride * p.batch :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hassoc : 4 * p.batch * p.pageTableStride = 4 * (p.pageTableStride * p.batch) := by
    rw [Nat.mul_assoc, Nat.mul_comm p.batch]
  rw [Nat.mul_succ] at hmul
  have hfit : p.pageTableBase + 4 * (p.pageTableStride * i + q) < 2 ^ 64 := by omega
  have hS : p.pageTableStride < 2 ^ 64 := by omega
  have hd : d = ⟨.pgLd per it, d.v, d.k⟩ := by
    obtain ⟨s', v', k'⟩ := d; simp only at hs; subst hs; rfl
  have haddr : (rv p L g w d (pgLdA per) + BitVec.ofInt 64 0).toNat =
      p.pageTableBase + 4 * (i * p.pageTableStride + q) := by
    have h0 : ∀ x : BitVec 64, x + BitVec.ofInt 64 0 = x := fun x => by
      apply BitVec.eq_of_toNat_eq; simp
    rw [h0, Nat.mul_comm i, hd, rv_pg, pgIdx_eq hx32]
    have hpr : ptRow p d.v = add64 (BitVec.ofNat 64 p.pageTableBase)
        (shl64 (mul64 (BitVec.ofNat 64 p.pageTableStride) (sext (W i))) 2) := by
      simp only [ptRow]; rw [hc]
    cases per
    · simp only
      rw [hsu, setup_rd11, show ptRow p v₀ = ptRow p d.v by simp only [ptRow, hsc0], hpr]
      exact ptAddr_toNat (by omega) (by omega) hS hfit
    · simp only
      rw [hpr]; exact ptAddr_toNat (by omega) (by omega) hS hfit
    · simp only
      rw [hpr]; exact ptAddr_toNat (by omega) (by omega) hS hfit
  exact ⟨i, q, by omega, hq, haddr, hc, hqdef⟩

/-- **A page-table load of a loader lane returns the launch's page-table word**: at a state
with the reference values, the row is inside the chosen request's used length, so the address is
the page table's word for the row's page (`inputReadValue`, `Pre.pageBytes`). -/
theorem pg_exact (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {b : Bool} {d : D} {n : Cls → Nat} {e : Event} {ns nv nc : Nat} {per : Per} {it : Fin 2}
    (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (linj p L g b d n)))
    (hF : LFits p L g d ns nv nc) (hs : d.site = .pgLd per it) :
    ∃ i < p.batch, ∃ q < (p.kLength i + 15) / 16, ∀ a bs, e.kind = .rd a bs →
      rebuild 3 bs = .ok (.bits 32 (BitVec.ofNat 64 (p.page i q))) ∧
      chosen d.v.sc = W i ∧ q = (row0 p L g d.v per it).toNat / 16 := by
  have hev := (lfired hp hX he hσ).1
  obtain ⟨i, q, hib, hq, haddr, hci⟩ := pg_addr hp hF hs (wOf b)
  refine ⟨i, hib, q, hq, fun a bs hka => ⟨?_, hci⟩⟩
  obtain ⟨pc, kind⟩ := e
  simp only at hka
  subst hka
  have hd : d = ⟨.pgLd per it, d.v, d.k⟩ := by
    obtain ⟨s', v', k'⟩ := d; simp only at hs; subst hs; rfl
  rw [hd] at hev
  simp only [Ev] at hev
  rw [← hd] at hev
  rcases hev with ⟨bs', hk'⟩ | ⟨f, hk'⟩
  swap
  · cases hk'
  simp only [Kind.rd.injEq] at hk'
  obtain ⟨rfl, rfl⟩ := hk'
  rw [haddr] at he
  obtain ⟨hst, hpt⟩ := hp.pageTable i hib
  have hin : ∀ j < 4, ∃ r ∈ p.inputRegions,
      r.Contains ((globalLoc (p.pageTableBase + 4 * (i * p.pageTableStride + q))).at j) := by
    intro j hj
    refine ⟨⟨p.pageTableBase, 4 * p.batch * p.pageTableStride⟩,
      by simp [Params.inputRegions], ?_⟩
    have hmul : p.pageTableStride * (i + 1) ≤ p.pageTableStride * p.batch :=
      Nat.mul_le_mul_left _ (by omega)
    have hassoc : 4 * p.batch * p.pageTableStride = 4 * (p.pageTableStride * p.batch) := by
      rw [Nat.mul_assoc, Nat.mul_comm p.batch]
    rw [Nat.mul_succ] at hmul
    simp only [Region.Contains, globalLoc, Loc.at, true_and]
    rw [Nat.mul_comm i]
    omega
  rw [inputReadValue hp hX (i := (g, k)) ⟨pc, he⟩ rfl hin (hp.pageBytes i hib q hq),
    show Value.bits 32 (BitVec.ofNat 64 (p.page i q)) = b32 (p.page i q) from rfl, rebuild_b32]

/-- **A page-table load returns a page-table word.** -/
theorem pg_value (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {b : Bool} {d : D} {n : Cls → Nat} {e : Event} {ns nv nc : Nat} {per : Per} {it : Fin 2}
    (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (linj p L g b d n)))
    (hF : LFits p L g d ns nv nc) (hs : d.site = .pgLd per it) :
    ∃ i < p.batch, ∃ q < (p.kLength i + 15) / 16, ∀ a bs, e.kind = .rd a bs →
      rebuild 3 bs = .ok (.bits 32 (BitVec.ofNat 64 (p.page i q))) := by
  obtain ⟨i, hi, q, hq, h⟩ := pg_exact hp hX he hσ hF hs
  exact ⟨i, hi, q, hq, fun a bs hk => (h a bs hk).1⟩

/-- A page-table load returns a 32-bit word. -/
theorem pg_rebuild (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {b : Bool} {d : D} {n : Cls → Nat} {e : Event} {ns nv nc : Nat} {per : Per} {it : Fin 2}
    (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (linj p L g b d n)))
    (hF : LFits p L g d ns nv nc) (hs : d.site = .pgLd per it) :
    ∀ a bs, e.kind = .rd a bs → ∃ x, rebuild 3 bs = .ok (.bits 32 x) := by
  obtain ⟨i, -, q, -, h⟩ := pg_value hp hX he hσ hF hs
  exact fun a bs hk => ⟨_, h a bs hk⟩

/-- **A page-table load of a loader lane returns a 32-bit word** (`pg_rebuild`). -/
theorem pg_word (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) {k : Nat}
    {b : Bool} {d : D} {n : Cls → Nat} {e : Event} {ns nv nc : Nat} {per : Per} {it : Fin 2}
    (he : X.get (g, k) = some e)
    (hσ : Frame.stateAt (thread p L) X g k = some (some (linj p L g b d n)))
    (hF : LFits p L g d ns nv nc) (hs : d.site = .pgLd per it) : (ret d).accepts e := by
  have hret : ret d = .word 32 := by simp only [ret, hs]
  rw [hret]
  have hev := (lfired hp hX he hσ).1
  obtain ⟨s', v', k'⟩ := d
  simp only at hs
  subst hs
  obtain ⟨pc, kind⟩ := e
  simp only [Ev] at hev
  rcases hev with ⟨bs, hk'⟩ | ⟨f, hk'⟩
  · subst hk'
    obtain ⟨x, hx⟩ := pg_rebuild hp hX he hσ hF rfl _ bs rfl
    exact acc_rd rfl hx
  · exact acc_ub ⟨f, hk'⟩

set_option maxHeartbeats 4000000 in
/-- **No page-table load of a loader lane under its reference values is undefined behaviour**:
its address is a page-table word (`pg_addr`), 4-aligned since `pageTableBase` is. -/
theorem pg_safe (hp : Pre p L m) {w : Nat} {ent : Nat → Value} {d : D} {ns nv nc : Nat}
    {per : Per} {it : Fin 2} (hF : LFits p L g d ns nv nc) (hs : d.site = .pgLd per it)
    (hk0 : d.k = 0) {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (h : (code p L g w ent).AtD d t) (hc : kernel.code[(code p L g w ent).pc d]? = some ins)
    (hf : Fires ((code p L g w ent).pc d) (eventTmpl Assumptions.all L g t ins.op) e o)
    (f : Fault) : e.kind ≠ .ub f := by
  obtain ⟨i, q, -, -, ha, -⟩ := pg_addr hp hF hs w
  have hal : p.pageTableBase % 4 = 0 := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, h3, -⟩ := hp.alignment; exact h3
  have hreg : ∀ r ∈ Flow.live d.site.pc, t.regs r = some (valueOf p L g w ent d r) :=
    fun r hr => holds_mem h.2.2.2.2 (mem_factsFrom hr)
  have hsub : t.sub = 0 := by
    have := h.2.1; obtain ⟨s, v, k⟩ := d
    simp only at hk0; subst hk0; simpa using this
  replace hc : kernel.code[d.site.pc]? = some ins := hc
  obtain ⟨site, v, k⟩ := d
  simp only at hs
  subst hs
  intro hk
  rw [rv_pg] at ha
  have ht : ∀ y : BitVec 64, truncBits 64 y = y := fun y =>
    BitVec.eq_of_toNat_eq (by simp only [truncBits, BitVec.toNat_ofNat]; omega)
  cases per <;> fin_cases it <;>
  · obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    tmpl_unfold hf PTX.loadTmpl
    simp only [PTX.DType.width, PTX.MemAccess.regs, List.filterMap_cons, List.filterMap_nil,
      id] at hf
    first
      | (have hr := hreg 7531 (by lit_mem)
         simp only [valueOf, values, valuesPgPrime, lookupLit] at hr
         refine fires_load_reg_al hsub hr hf hk ?_
         simp only at ha ⊢
         rw [ht, ha]
         omega)
      | (have hr := hreg 7650 (by lit_mem)
         simp only [valueOf, values, valuesPgWarm, lookupLit] at hr
         refine fires_load_reg_al hsub hr hf hk ?_
         simp only at ha ⊢
         rw [ht, ha]
         omega)
      | (have hr := hreg 7765 (by lit_mem)
         simp only [valueOf, values, valuesPgSteady, lookupLit] at hr
         refine fires_load_reg_al hsub hr hf hk ?_
         simp only at ha ⊢
         rw [ht, ha]
         omega)

end
end PTX.Kernels.TmlFa4Fwd.Proof.LdWarp
