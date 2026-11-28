-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.RescaleFacts
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.StrictEpi

@[expose] public section

/-! # The conditions of the rescale runs

`w0k_alpha`, `w0k_rs`: the factor's run (pcs 713-715) and the chunk `c`'s product run (pcs 718-813
and the like) are no fault for the words of a valid block: the factor is a number (`blk_alpha`) and
the loaded words are numbers. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Flow PTX.Proof PTX.Assumption PTX.Kernels.FlashMlaSparseDecodeH64.Proof
  PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Gen

noncomputable section

/-- The condition of rescale chunk `c`'s run. -/
def RsCond (c : Fin 4) (V : Nat → Value) : Prop :=
  match c with
  | 0 => rs0_cond V
  | 1 => rs1_cond V
  | 2 => rs2_cond V
  | 3 => rs3_cond V

theorem rsCond_vals (c : Fin 4) {V : Nat → Value} {x : Nat → ℝ} {s : ℝ}
    (hX : ∀ j < 64, OkF (V (1199 + 129 * c.val + j)) (x j))
    (hs0 : valFloat .f32 (splitValue 64 (V 3312)).1 = .ok s)
    (hs1 : valFloat .f32 (splitValue 64 (V 3312)).2 = .ok s) : RsCond c V := by
  fin_cases c
  · exact (rs0_vals (x := x) (s := s) (by simpa using hX) hs0 hs1).1
  · exact (rs1_vals (x := x) (s := s) (by simpa using hX) hs0 hs1).1
  · exact (rs2_vals (x := x) (s := s) (by simpa using hX) hs0 hs1).1
  · exact (rs3_vals (x := x) (s := s) (by simpa using hX) hs0 hs1).1

/-- **The factor's run** is no fault for a valid block. -/
theorem w0k_alpha {sc : ℝ} {w : W0Words} {x : BitVec 64} (hx : Rd (.bits 32 x) (sc : EReal))
    {b : Blk} (hb : BlkIs b w) (hvt : b.vt = true → W0Ok sc w) {mR lR : ℝ}
    (hm : Rd b.m (mR : EReal)) (hl : Rd b.l (lR : EReal)) {r0 : EReal} (hmx : Rd b.mx r0) :
    alpha_cond (lookupD (f_a0 x b.m b.l b.mx b.sk b.lo b.hi b.mw (b.pw 0) (b.pw 1) (b.pw 2)
      (b.pw 3) (b.pw 4) (b.pw 5) (b.pw 6) (b.pw 7) b.pm b.vt)) := by
  obtain ⟨s, hform, hA⟩ := blk_alpha hx hb hvt hm hl hmx
  exact alpha_cond_of_reads _ hA hform (by simp [f_a0, blkA, lookupD])

/-- **The product run of chunk `c`** is no fault when the loaded words are numbers. -/
theorem w0k_rs {sc : ℝ} {w : W0Words} {x : BitVec 64} (hx : Rd (.bits 32 x) (sc : EReal))
    {b : Blk} (hb : BlkIs b w) (hvt : b.vt = true → W0Ok sc w) {mR lR : ℝ}
    (hm : Rd b.m (mR : EReal)) (hl : Rd b.l (lR : EReal)) {r0 : EReal} (hmx : Rd b.mx r0)
    (c : Fin 4) (ho : b.o.length = 64) (hO : ∀ v ∈ b.o, ∃ r : ℝ, OkF v r) :
    RsCond c (lookupD (wF x (.rldw c) b)) := by
  obtain ⟨y, s, hX, h0, h1⟩ := rs_inputs hx hb hvt hm hl hmx c ho hO
  exact rsCond_vals c hX h0 h1

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
