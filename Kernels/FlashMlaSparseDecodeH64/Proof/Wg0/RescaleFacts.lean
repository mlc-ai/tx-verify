-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.RescaleStep
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.NumBlk
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.RescaleVals0
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.RescaleVals1
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.NumVote
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.Blk
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen.DataFacts

@[expose] public section

/-! # The facts of a rescale store's site

At chunk `c`'s store the data machine's facts are the products `x j * s` of the loaded words and
the block's factor `s` (`rst_facts`, from `rs0_vals` to `rs3_vals`). The factor (register 2951)
is `1` without a vote, else `2 ^ (m - m')` for the carried and the new maximum, numbers by
`w0_block` (`blk_alpha`); the register of the pair (3312) holds it twice (`alpha_pair`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.FlashMlaSparseDecodeH64.Proof
  PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen

noncomputable section


/-- The scale factor of block `b`'s facts: register 2951. -/
def blkA (x : BitVec 64) (b : Blk) : Value :=
  lookupD (f_fin x b.m b.l b.mx b.sk b.lo b.hi b.mw (b.pw 0) (b.pw 1) (b.pw 2) (b.pw 3) (b.pw 4)
    (b.pw 5) (b.pw 6) (b.pw 7) b.pm b.vt) 2951

/-- The scale factor of a block is a number, `2 ^ (m - m')` for the carried maximum `m` and the
block's new maximum `m'` (`1` without a vote, where the maximum stays). -/
theorem blk_alpha_val {sc : ℝ} {w : W0Words} {x : BitVec 64} (hx : Rd (.bits 32 x) (sc : EReal))
    {b : Blk} (hb : BlkIs b w) (hvt : b.vt = true → W0Ok sc w) {mR lR : ℝ}
    (hm : Rd b.m (mR : EReal)) (hl : Rd b.l (lR : EReal)) {r0 : EReal} (hmx : Rd b.mx r0) :
    ∃ s : ℝ, ((∃ y, blkA x b = .bits 32 y) ∨ ∃ r, blkA x b = .float .f32 r) ∧
      OkF (blkA x b) s ∧ s = (2 : ℝ) ^ (mR - w0Max sc mR w) := by
  have e1 : lookupD (f_fin x b.m b.l b.mx b.sk b.lo b.hi b.mw (b.pw 0) (b.pw 1) (b.pw 2)
      (b.pw 3) (b.pw 4) (b.pw 5) (b.pw 6) (b.pw 7) b.pm b.vt) 2951 = blkOst x b 2951 := by
    unfold f_fin blkOst
    exact lookupD_factsFrom (by decide)
  unfold blkA
  rw [e1]
  unfold blkOst f_ost
  rw [lk_frame (K := w0KeepOst) (r := 2951) (by decide)
    (by simp only [pw_facts4, List.map_cons, List.map_nil]; decide) (by decide)]
  have e2951 : lookupD (f_join x b.m b.l b.mx b.sk b.lo b.hi b.mw (b.pw 0) (b.pw 1) (b.pw 2)
      (b.pw 3) (b.pw 4) (b.pw 5) (b.pw 6) (b.pw 7) b.pm b.vt) 2951 =
      if b.vt then vt_v584 (lookupD (f_vh x b.m b.l b.mx b.sk b.lo b.hi b.mw (b.pw 0) (b.pw 1)
        (b.pw 2) (b.pw 3) (b.pw 4) (b.pw 5) (b.pw 6) (b.pw 7) b.pm)) else
        lookupD (f_vh x b.m b.l b.mx b.sk b.lo b.hi b.mw (b.pw 0) (b.pw 1) (b.pw 2) (b.pw 3)
          (b.pw 4) (b.pw 5) (b.pw 6) (b.pw 7) b.pm) 2951 := by
    dsimp only [f_join]
    exact lk_head (by simp [List.lookup])
  rw [e2951]
  cases hv : b.vt
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have : lookupD (f_vh x b.m b.l b.mx b.sk b.lo b.hi b.mw (b.pw 0) (b.pw 1) (b.pw 2) (b.pw 3)
        (b.pw 4) (b.pw 5) (b.pw 6) (b.pw 7) b.pm) 2951 =
        .bits 32 (BitVec.ofNat 64 1065353216) := by
      unfold f_vh
      simp [lookupD, List.lookup]
    rw [this]
    have hw : w.vt = false := hb.vt ▸ hv
    refine ⟨1, Or.inl ⟨_, rfl⟩, ⟨⟨rfl, fun _ _ _ h => (by cases h), fun _ _ h => by
      simp only [Value.bits.injEq] at h; obtain ⟨-, rfl⟩ := h; simp [BitVec.toNat_ofNat]⟩,
      valFloat_one⟩, ?_⟩
    simp [w0Max, hw]
  · simp only [↓reduceIte]
    have hw0 := hvt hv
    have h2950 := (w0_block hw0 hx hb hm hl hmx).1
    have e2950 : blkOst x b 2950 = vt_v582 (lookupD (f_vh x b.m b.l b.mx b.sk b.lo b.hi b.mw
        (b.pw 0) (b.pw 1) (b.pw 2) (b.pw 3) (b.pw 4) (b.pw 5) (b.pw 6) (b.pw 7) b.pm)) := by
      unfold blkOst f_ost
      rw [lk_frame (K := w0KeepOst) (r := 2950) (by decide)
        (by simp only [pw_facts4, List.map_cons, List.map_nil]; decide) (by decide)]
      have e2950 : lookupD (f_join x b.m b.l b.mx b.sk b.lo b.hi b.mw (b.pw 0) (b.pw 1) (b.pw 2)
          (b.pw 3) (b.pw 4) (b.pw 5) (b.pw 6) (b.pw 7) b.pm b.vt) 2950 =
          if b.vt then vt_v585 (lookupD (f_vh x b.m b.l b.mx b.sk b.lo b.hi b.mw (b.pw 0)
            (b.pw 1) (b.pw 2) (b.pw 3) (b.pw 4) (b.pw 5) (b.pw 6) (b.pw 7) b.pm)) else
            lookupD (f_vh x b.m b.l b.mx b.sk b.lo b.hi b.mw (b.pw 0) (b.pw 1) (b.pw 2) (b.pw 3)
              (b.pw 4) (b.pw 5) (b.pw 6) (b.pw 7) b.pm) 2950 := by
        dsimp only [f_join]
        exact lk_head (by simp [List.lookup])
      rw [e2950, hv]
      simp only [↓reduceIte]
      rfl
    rw [e2950] at h2950
    have hmR : Rd (lookupD (f_vh x b.m b.l b.mx b.sk b.lo b.hi b.mw (b.pw 0) (b.pw 1) (b.pw 2)
        (b.pw 3) (b.pw 4) (b.pw 5) (b.pw 6) (b.pw 7) b.pm) 2950) (mR : EReal) := by
      rw [w0c_sc_vh 2950 (by decide), w0c_vm_car x b.m b.l b.mx b.sk b.lo b.hi b.mw 2950
        (by decide), w0c_car_2950]
      exact hm
    have e3 : vt_v583 (lookupD (f_vh x b.m b.l b.mx b.sk b.lo b.hi b.mw (b.pw 0) (b.pw 1)
        (b.pw 2) (b.pw 3) (b.pw 4) (b.pw 5) (b.pw 6) (b.pw 7) b.pm)) =
        .float .f32 (mR - w0Max sc mR w) :=
      okVal_ok (w0v_sub (rd_read hmR) (rd_read h2950))
    have e4 : vt_v584 (lookupD (f_vh x b.m b.l b.mx b.sk b.lo b.hi b.mw (b.pw 0) (b.pw 1)
        (b.pw 2) (b.pw 3) (b.pw 4) (b.pw 5) (b.pw 6) (b.pw 7) b.pm)) =
        .float .f32 (Real.rpow 2 (mR - w0Max sc mR w)) :=
      okVal_ok (by rw [e3]; exact ex2E_real (readEReal_float _))
    refine ⟨Real.rpow 2 (mR - w0Max sc mR w), ?_, ?_, rfl⟩
    · rw [e4]; exact Or.inr ⟨_, rfl⟩
    · rw [e4]; exact okF_float _

/-- The scale factor of a block is a number: `1` without a vote, else `2 ^ (m - m')`. -/
theorem blk_alpha {sc : ℝ} {w : W0Words} {x : BitVec 64} (hx : Rd (.bits 32 x) (sc : EReal))
    {b : Blk} (hb : BlkIs b w) (hvt : b.vt = true → W0Ok sc w) {mR lR : ℝ}
    (hm : Rd b.m (mR : EReal)) (hl : Rd b.l (lR : EReal)) {r0 : EReal} (hmx : Rd b.mx r0) :
    ∃ s : ℝ, ((∃ y, blkA x b = .bits 32 y) ∨ ∃ r, blkA x b = .float .f32 r) ∧
      OkF (blkA x b) s := by
  obtain ⟨s, h1, h2, -⟩ := blk_alpha_val hx hb hvt hm hl hmx
  exact ⟨s, h1, h2⟩


theorem alpha_pair {A : Value} {s : ℝ} (hA : OkF A s)
    (hf : (∃ y, A = .bits 32 y) ∨ ∃ r, A = .float .f32 r) (V : Nat → Value)
    (hV : V 3565 = joinValue A (.bits 32 0)) :
    valFloat .f32 (splitValue 64 (alpha_v714 V)).1 = .ok s ∧
      valFloat .f32 (splitValue 64 (alpha_v714 V)).2 = .ok s := by
  have hz : Clean (.bits 32 0) := ⟨rfl, fun _ _ _ h => (by cases h), fun _ _ h => by
    simp only [Value.bits.injEq] at h; obtain ⟨-, rfl⟩ := h; simp⟩
  have hj := split_join_clean hA.1 hz
  have hb8 : (joinValue A (.bits 32 0)).bytes = 8 := by
    rcases hf with ⟨y, rfl⟩ | ⟨r, rfl⟩
    · simp [joinValue, Value.bytes]
    · simp [joinValue, Value.bytes]; rfl
  have hA4 := hA.1.1
  have e : alpha_v713 V = A := by
    unfold alpha_v713
    have hl : lk [3565] [V 3565] 3565 = joinValue A (.bits 32 0) := by
      rw [hV]; simp [lk]
    simp only [hl, sinkW, hb8, hj, hA4]
    simp [okVal, Value.bytes]
  have e2 : splitValue 64 (alpha_v714 V) = (A, A) := by
    unfold alpha_v714
    rw [e]
    exact split_join_clean hA.1 hA.1
  rw [e2]
  exact ⟨hA.2, hA.2⟩

/-- Chunk `c`'s product facts of the generated run. -/
def rsF (c : Fin 4) (V : Nat → Value) : List (Nat × Value) :=
  match c with
  | 0 => rs0_facts3 V
  | 1 => rs1_facts3 V
  | 2 => rs2_facts3 V
  | 3 => rs3_facts3 V

theorem rsF_vals (c : Fin 4) {V : Nat → Value} {x : Nat → ℝ} {s : ℝ}
    (hX : ∀ j < 64, OkF (V (1199 + 129 * c.val + j)) (x j))
    (hs0 : valFloat .f32 (splitValue 64 (V 3312)).1 = .ok s)
    (hs1 : valFloat .f32 (splitValue 64 (V 3312)).2 = .ok s) :
    rsF c V = mulFacts (1264 + 129 * c.val) x s 64 := by
  fin_cases c
  · simpa [rsF] using (rs0_vals (x := x) (s := s) (by simpa using hX) hs0 hs1).2
  · simpa [rsF] using (rs1_vals (x := x) (s := s) (by simpa using hX) hs0 hs1).2
  · simpa [rsF] using (rs2_vals (x := x) (s := s) (by simpa using hX) hs0 hs1).2
  · simpa [rsF] using (rs3_vals (x := x) (s := s) (by simpa using hX) hs0 hs1).2

theorem wF_rst0 (x : BitVec 64) (b : Blk) :
    wF x (.rst 0) b = rsF 0 (lookupD (wF x (.rldw 0) b)) ++ wF x (.rld 0) b := rfl
theorem wF_rst1 (x : BitVec 64) (b : Blk) :
    wF x (.rst 1) b = rsF 1 (lookupD (wF x (.rldw 1) b)) ++ wF x (.rld 1) b := rfl
theorem wF_rst2 (x : BitVec 64) (b : Blk) :
    wF x (.rst 2) b = rsF 2 (lookupD (wF x (.rldw 2) b)) ++ wF x (.rld 2) b := rfl
theorem wF_rst3 (x : BitVec 64) (b : Blk) :
    wF x (.rst 3) b = rsF 3 (lookupD (wF x (.rldw 3) b)) ++ wF x (.rld 3) b := rfl

theorem wF_rst (c : Fin 4) (x : BitVec 64) (b : Blk) :
    wF x (.rst c) b = rsF c (lookupD (wF x (.rldw c) b)) ++ wF x (.rld c) b := by
  fin_cases c
  exacts [wF_rst0 x b, wF_rst1 x b, wF_rst2 x b, wF_rst3 x b]

theorem wF_rldw0 (x : BitVec 64) (b : Blk) : wF x (.rldw 0) b = wF x (.rld 0) b ++
    factsFrom (oRegs 0) (lookupD ((oRegs 0).zip b.o)) := rfl
theorem wF_rldw1 (x : BitVec 64) (b : Blk) : wF x (.rldw 1) b = wF x (.rld 1) b ++
    factsFrom (oRegs 1) (lookupD ((oRegs 1).zip b.o)) := rfl
theorem wF_rldw2 (x : BitVec 64) (b : Blk) : wF x (.rldw 2) b = wF x (.rld 2) b ++
    factsFrom (oRegs 2) (lookupD ((oRegs 2).zip b.o)) := rfl
theorem wF_rldw3 (x : BitVec 64) (b : Blk) : wF x (.rldw 3) b = wF x (.rld 3) b ++
    factsFrom (oRegs 3) (lookupD ((oRegs 3).zip b.o)) := rfl

theorem wF_rldw (c : Fin 4) (x : BitVec 64) (b : Blk) :
    wF x (.rldw c) b = wF x (.rld c) b ++ factsFrom (oRegs c) (lookupD ((oRegs c).zip b.o)) := by
  fin_cases c
  exacts [wF_rldw0 x b, wF_rldw1 x b, wF_rldw2 x b, wF_rldw3 x b]

theorem wF_rld_keys (c : Fin 4) (x : BitVec 64) (b : Blk) :
    (wF x (.rld c) b).map Prod.fst = [3312, 2951, 467, 3243, 2950, 2955, 2885, 2880] := by
  simp [wF, wcls, wFc, f_blk, f_fin, alpha_facts1, factsFrom]

/-- The registers of the loaded chunk, in the facts after the load's wait. -/
theorem rldw_word (c : Fin 4) (x : BitVec 64) (b : Blk) (ho : b.o.length = 64) {j : Nat}
    (hj : j < 64) :
    lookupD (wF x (.rldw c) b) (1199 + 129 * c.val + j) = b.o.getD j (.pred false) := by
  have hn : 1199 + 129 * c.val + j ∉ (wF x (.rld c) b).map Prod.fst := by
    rw [wF_rld_keys]
    have := c.isLt
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    omega
  rw [wF_rldw, lk_skip hn]
  have hmem : 1199 + 129 * c.val + j ∈ oRegs c := by
    simp only [oRegs, List.mem_range'_1]
    omega
  rw [lookupD_factsFrom hmem]
  have h := lookup_range_zip (1199 + 129 * c.val) b.o j (by omega)
  have hr : oRegs c = List.range' (1199 + 129 * c.val) b.o.length := by rw [ho]; rfl
  unfold lookupD
  rw [hr, h]
  simp [List.getElem?_eq_getElem (show j < b.o.length by omega)]

/-- **The inputs of chunk `c`'s product run**: the loaded words are numbers `y` and the factor
pair is `(s, s)`. -/
theorem rs_inputs_val {sc : ℝ} {w : W0Words} {x : BitVec 64} (hx : Rd (.bits 32 x) (sc : EReal))
    {b : Blk} (hb : BlkIs b w) (hvt : b.vt = true → W0Ok sc w) {mR lR : ℝ}
    (hm : Rd b.m (mR : EReal)) (hl : Rd b.l (lR : EReal)) {r0 : EReal} (hmx : Rd b.mx r0)
    (c : Fin 4) (ho : b.o.length = 64) (hO : ∀ v ∈ b.o, ∃ r : ℝ, OkF v r) :
    ∃ (y : Nat → ℝ) (s : ℝ), (∀ j < 64, OkF (lookupD (wF x (.rldw c) b)
        (1199 + 129 * c.val + j)) (y j)) ∧
      valFloat .f32 (splitValue 64 (lookupD (wF x (.rldw c) b) 3312)).1 = .ok s ∧
      valFloat .f32 (splitValue 64 (lookupD (wF x (.rldw c) b) 3312)).2 = .ok s ∧
      s = (2 : ℝ) ^ (mR - w0Max sc mR w) := by
  obtain ⟨s, hform, hA, hsv⟩ := blk_alpha_val hx hb hvt hm hl hmx
  choose! y hy using fun j : Nat => (fun (hj : j < 64) => hO (b.o.getD j (.pred false))
    (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      exact List.getElem_mem _))
  refine ⟨y, s, fun j hj => by rw [rldw_word c x b ho hj]; exact hy j hj, ?_⟩
  have hV3565 : (lookupD (f_a0 x b.m b.l b.mx b.sk b.lo b.hi b.mw (b.pw 0) (b.pw 1) (b.pw 2)
      (b.pw 3) (b.pw 4) (b.pw 5) (b.pw 6) (b.pw 7) b.pm b.vt)) 3565 =
      joinValue (blkA x b) (.bits 32 0) := by
    simp [f_a0, blkA, lookupD]
  obtain ⟨h0, h1⟩ := alpha_pair hA hform _ hV3565
  have e3312 : lookupD (wF x (.rldw c) b) 3312 = alpha_v714 (lookupD (f_a0 x b.m b.l b.mx b.sk
      b.lo b.hi b.mw (b.pw 0) (b.pw 1) (b.pw 2) (b.pw 3) (b.pw 4) (b.pw 5) (b.pw 6) (b.pw 7)
      b.pm b.vt)) := by
    rw [wF_rldw, lk_head_mem (by rw [wF_rld_keys]; decide)]
    fin_cases c <;> exact lk_head (by simp [alpha_facts1])
  rw [e3312]
  exact ⟨h0, h1, hsv⟩

/-- **The inputs of chunk `c`'s product run**: the loaded words are numbers `y` and the factor
pair is `(s, s)`. -/
theorem rs_inputs {sc : ℝ} {w : W0Words} {x : BitVec 64} (hx : Rd (.bits 32 x) (sc : EReal))
    {b : Blk} (hb : BlkIs b w) (hvt : b.vt = true → W0Ok sc w) {mR lR : ℝ}
    (hm : Rd b.m (mR : EReal)) (hl : Rd b.l (lR : EReal)) {r0 : EReal} (hmx : Rd b.mx r0)
    (c : Fin 4) (ho : b.o.length = 64) (hO : ∀ v ∈ b.o, ∃ r : ℝ, OkF v r) :
    ∃ (y : Nat → ℝ) (s : ℝ), (∀ j < 64, OkF (lookupD (wF x (.rldw c) b)
        (1199 + 129 * c.val + j)) (y j)) ∧
      valFloat .f32 (splitValue 64 (lookupD (wF x (.rldw c) b) 3312)).1 = .ok s ∧
      valFloat .f32 (splitValue 64 (lookupD (wF x (.rldw c) b) 3312)).2 = .ok s := by
  obtain ⟨y, s, h1, h2, h3, -⟩ := rs_inputs_val hx hb hvt hm hl hmx c ho hO
  exact ⟨y, s, h1, h2, h3⟩

/-- **The products of chunk `c`** are numbers when the loaded words are: the facts of the store's
site hold the products `x j * s` of the loaded words and the block's factor. -/
theorem rst_facts {sc : ℝ} {w : W0Words} {x : BitVec 64} (hx : Rd (.bits 32 x) (sc : EReal))
    {b : Blk} (hb : BlkIs b w) (hvt : b.vt = true → W0Ok sc w) {mR lR : ℝ}
    (hm : Rd b.m (mR : EReal)) (hl : Rd b.l (lR : EReal)) {r0 : EReal} (hmx : Rd b.mx r0)
    (c : Fin 4) (ho : b.o.length = 64) (hO : ∀ v ∈ b.o, ∃ r : ℝ, OkF v r) :
    ∃ (y : Nat → ℝ) (s : ℝ), wF x (.rst c) b = mulFacts (1264 + 129 * c.val) y s 64 ++
      wF x (.rld c) b ∧ (∀ j < 64, OkF (b.o.getD j (.pred false)) (y j)) ∧
      s = (2 : ℝ) ^ (mR - w0Max sc mR w) := by
  obtain ⟨y, s, hX, h0, h1, hsv⟩ := rs_inputs_val hx hb hvt hm hl hmx c ho hO
  exact ⟨y, s, by rw [wF_rst, rsF_vals c hX h0 h1], fun j hj => by
    rw [← rldw_word c x b ho hj]; exact hX j hj, hsv⟩

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
