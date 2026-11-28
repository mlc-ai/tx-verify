-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Grid
public import Lemmas.Flow.Arith32WordW
public import Lemmas.Flow.Arith32WordWide
public import Lemmas.Flow.Arith32Norm

@[expose] public section

/-! # Every CTA has a block

`Pre.paddedRange` bounds each row's padded total `origPadded len + ceilToMultiple extra 64` below
`2 ^ 31`, and `origPadded` is at least one block (`64`). The code's 32-bit padded total
(`totL`) of the row's two length words is that number (each length is below `2 ^ 31`, so no
signed shift fires), so the test `tot < 64` that skips the roles' block loops fails and the block
count is at least one (`blocksOf_pos`). This sits next to `Lib/Rounds.lean` rather than in it, so
that adding it rebuilds nothing above. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0}

private theorem shru0 : shru (W 0) 26 = W 0 := by decide

private theorem shrs_hi {a : Nat} (h : a < 2 ^ 31) : shrs (W a) 31 = W 0 := by
  have := toNat_shrs_W (k := 31) h (by norm_num)
  rw [Nat.div_eq_of_lt (by omega)] at this
  exact_mod_cast this

/-- The code's padded length of a word below `2 ^ 31 - 63`. -/
theorem padL_W {a : Nat} (h : a + 63 < 2 ^ 31) :
    padL (W a) = W (a + 63 - (a + 63) % 64) := by
  have h1 : addi (W a) 63 = W (a + 63) := by
    have := addi_W (a := a) (n := 63) (by norm_num) (by omega)
    exact_mod_cast this
  simp only [padL, h1, shrs_hi h, shru0, add32_W (show a + 63 + 0 < 2 ^ 32 by omega),
    Nat.add_zero]
  exact andi_W_neg64 (by omega)

/-- **The block count of two lengths inside the padded range** is the data's total. -/
theorem rounds_val {a b : Nat}
    (h : FlashMlaSparseDecodeH64.origPadded a +
      FlashMlaSparseDecodeH64.ceilToMultiple b FlashMlaSparseDecodeH64.topkBlock < 2 ^ 31) :
    roundsOf (W a) (W b) = FlashMlaSparseDecodeH64.totalBlocks a b := by
  simp only [FlashMlaSparseDecodeH64.totalBlocks, FlashMlaSparseDecodeH64.origPadded,
    FlashMlaSparseDecodeH64.ceilToMultiple, FlashMlaSparseDecodeH64.topkBlock]
  simp only [FlashMlaSparseDecodeH64.origPadded, FlashMlaSparseDecodeH64.ceilToMultiple,
    FlashMlaSparseDecodeH64.topkBlock] at h
  have ha := Nat.div_mul_le_self (a + 64 - 1) 64
  have hb := Nat.div_mul_le_self (b + 64 - 1) 64
  have ha' := Nat.lt_div_mul_add (a := a + 64 - 1) (b := 64) (by norm_num)
  have hb' := Nat.lt_div_mul_add (a := b + 64 - 1) (b := 64) (by norm_num)
  have hA : a + 63 - (a + 63) % 64 = (a + 64 - 1) / 64 * 64 := by omega
  have hB : b + 63 - (b + 63) % 64 = (b + 64 - 1) / 64 * 64 := by omega
  have hmx : max ((a + 64 - 1) / 64 * 64) 64 < 2 ^ 31 := by omega
  have h64 : i32 (64 : Nat) = W 64 := i32_W (by norm_num)
  have htot : totL (W a) (W b) =
      W ((b + 64 - 1) / 64 * 64 + max ((a + 64 - 1) / 64 * 64) 64) := by
    rw [totL_eq, padL_W (by omega), padL_W (by omega), hA, hB]
    have h64' : i32 64 = W 64 := by exact_mod_cast h64
    rw [h64', max32_W (by omega) (by norm_num), add32_W (by omega)]
  generalize ht : (b + 64 - 1) / 64 * 64 + max ((a + 64 - 1) / 64 * 64) 64 = t at htot
  have ht1 : 64 ≤ t := by omega
  have ht2 : t < 2 ^ 31 := by omega
  have hlt : scmpi .lt .s (totL (W a) (W b)) 64 = false := by
    rw [htot, scmpi_s_W _ (by norm_num) (by norm_num)]
    rw [show (64 : Int).toNat = 64 from rfl, scmp_lt_W ht2 (by norm_num)]
    simp only [decide_eq_false_iff_not, Nat.not_lt]; exact ht1
  have hn : nblkL (W a) (W b) = W (t / 64) := by
    simp only [nblkL, htot, shrs_hi ht2, shru0, add32_W (show t + 0 < 2 ^ 32 by omega),
      Nat.add_zero]
    have := toNat_shrs_W (k := 6) ht2 (by norm_num)
    exact_mod_cast this
  simp only [roundsOf, hlt, Bool.false_eq_true, ite_false, hn, W, BitVec.toNat_ofNat]
  omega

/-- **The block count of two lengths inside the padded range is positive.** -/
theorem rounds_pos {a b : Nat}
    (h : FlashMlaSparseDecodeH64.origPadded a +
      FlashMlaSparseDecodeH64.ceilToMultiple b FlashMlaSparseDecodeH64.topkBlock < 2 ^ 31) :
    1 ≤ roundsOf (W a) (W b) := by
  rw [rounds_val h]
  simp only [FlashMlaSparseDecodeH64.totalBlocks, FlashMlaSparseDecodeH64.origPadded,
    FlashMlaSparseDecodeH64.ceilToMultiple, FlashMlaSparseDecodeH64.topkBlock] at h ⊢
  omega

private theorem eqz_W {x : Nat} (h0 : 0 < x) (h : x < 2 ^ 64) : eqz64 (W x) = false := by
  simp only [eqz64, PTX.compare, r64, truncBits, W, BitVec.toNat_ofNat, BitVec.ofInt_ofNat]
  simp only [decide_eq_false_iff_not]
  intro he
  omega

/-- A length word of a row is the row's length: the parameter (which every row's length equals)
when the pointer is null, else the row's word. -/
private theorem len_word {base : Option Nat} {par : Nat} {len : Nat} (hlt : len < 2 ^ 31)
    (hnone : base = none → len = par) (hsome : ∀ x, base = some x → 0 < x ∧ x < 2 ^ 64) :
    (if eqz64 (pw8 (base.getD 0)) then pw par else W len) = W len := by
  rcases base with _ | x
  · have he : eqz64 (pw8 ((none : Option Nat).getD 0)) = true := by decide
    simp only [he, ↓reduceIte, ← hnone rfl]
    simp only [pw, leNat_eq, pow_zero, Nat.div_one, W]
    rw [Nat.mod_eq_of_lt (by omega)]
  · obtain ⟨h0, h1⟩ := hsome x rfl
    rw [Option.getD_some, pw8_eq x h1, eqz_W h0 h1]
    simp only [Bool.false_eq_true, ↓reduceIte]

/-- **A CTA's two length words are its row's lengths**, both at most their arrays' widths, and
the padded total is below `2 ^ 31`. -/
theorem len_words (hp : Pre P L m) (c : Nat) :
    lenWA P L c = W (P.topkLen (rowOf L c)) ∧ lenWB P L c = W (P.extraTopkLen (rowOf L c)) ∧
      FlashMlaSparseDecodeH64.origPadded (P.topkLen (rowOf L c)) +
        FlashMlaSparseDecodeH64.ceilToMultiple (P.extraTopkLen (rowOf L c))
          FlashMlaSparseDecodeH64.topkBlock < 2 ^ 31 ∧
      P.topkLen (rowOf L c) ≤ P.topk ∧ P.extraTopkLen (rowOf L c) ≤ P.extra_topk := by
  have hrow : rowOf L c < P.b := by
    have h := (ctaid_lt hp (c * L.block)).2
    rw [← rowOf_cta, Nat.mul_div_cancel _ (by rw [hp.block]; norm_num)] at h
    exact h
  have hr := hp.paddedRange _ hrow
  have hA : P.topkLen (rowOf L c) < 2 ^ 31 := by
    simp only [FlashMlaSparseDecodeH64.origPadded, FlashMlaSparseDecodeH64.ceilToMultiple,
      FlashMlaSparseDecodeH64.topkBlock] at hr
    have := Nat.lt_div_mul_add (a := P.topkLen (rowOf L c) + 64 - 1) (b := 64) (by norm_num)
    omega
  have hB : P.extraTopkLen (rowOf L c) < 2 ^ 31 := by
    simp only [FlashMlaSparseDecodeH64.origPadded, FlashMlaSparseDecodeH64.ceilToMultiple,
      FlashMlaSparseDecodeH64.topkBlock] at hr
    have := Nat.lt_div_mul_add (a := P.extraTopkLen (rowOf L c) + 64 - 1) (b := 64) (by norm_num)
    omega
  have hpa := hp.paramTopkLen
  have hpb := hp.paramExtraTopkLen
  refine ⟨?_, ?_, hr, ?_, ?_⟩
  · refine len_word hA (fun hb => ?_) (fun x hx => ⟨hp.topkLenNonNull x hx, hp.topkLenBaseLt x hx⟩)
    rw [hb] at hpa
    exact hpa.2 _ hrow
  · refine len_word hB (fun hb => ?_)
      (fun x hx => ⟨hp.extraTopkLenNonNull x hx, hp.extraTopkLenBaseLt x hx⟩)
    rw [hb] at hpb
    exact hpb.2 _ hrow
  · cases hb : P.topkLenBase with
    | none => rw [hb] at hpa; exact (hpa.2 _ hrow).le
    | some x => rw [hb] at hpa; exact (hpa.2.2 _ hrow 0 (by norm_num)).2 _ hrow
  · cases hb : P.extraTopkLenBase with
    | none => rw [hb] at hpb; exact (hpb.2 _ hrow).le
    | some x => rw [hb] at hpb; exact (hpb.2.2 _ hrow 0 (by norm_num)).2 _ hrow

/-- **Every CTA has at least one block**: the padded total of its row is at least `64`. -/
theorem blocksOf_pos (hp : Pre P L m) (c : Nat) : 1 ≤ blocksOf P L c := by
  obtain ⟨hwa, hwb, hr, -, -⟩ := len_words hp c
  rw [blocksOf, hwa, hwb]
  exact rounds_pos hr

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
