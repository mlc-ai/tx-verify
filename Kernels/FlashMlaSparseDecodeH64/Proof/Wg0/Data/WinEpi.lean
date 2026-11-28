-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.WinRes
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.EpiRd
public import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data.NumEpi

@[expose] public section

/-! # The conditions of the windows of the epilogue

The fields `w1157` (the row-sum read), `w1187` (the factor) and `w1202` to `w1677` (the four
output chunks) of `WinCond`, from the carried statistics, the sink word, the peer's row sum and the
accumulator words of a valid trace. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Arith32 PTX.Kernels.FlashMlaSparseDecodeH64

noncomputable section

variable {L : Launch} {g : Nat} {sc : ℝ} {l : List Event} {d : D} {e : Event}

/-- The sink word of a valid trace reads as an extended number. -/
theorem WCtx.sink (c : WCtx L g sc l d e) : ∃ sk : EReal, Rd d.b.sk sk := by
  have hv' : W0Valid sc l := by simpa using c.hv.take (j := l.length)
  obtain ⟨h1, -⟩ := hv'.epi
  rw [c.hSk.sk]
  rcases h1 with h | ⟨sk, hsk⟩
  · rw [h]; exact ⟨⊥, rd_negInf⟩
  · exact ⟨sk, hsk⟩

/-- The row sum of the peer, loaded: a non-negative number, zero for a row without a kept column. -/
theorem WCtx.rowSum (c : WCtx L g sc l d e) (h : w0EpiPe (w0Fin l).2 ≠ .pred false) :
    ∃ p : ℝ, 0 ≤ p ∧ Rd d.b.pe p ∧ (w0MxCarry sc (w0Fin l).1 = ⊥ → p = 0) := by
  have hv' : W0Valid sc l := by simpa using c.hv.take (j := l.length)
  obtain ⟨-, h2, -, -⟩ := hv'.epi
  rw [w0Fin_snd] at h
  rw [c.hE.pe]
  exact h2.resolve_left h

/-- **pc 1157**: the peer's row sum. -/
theorem wc_1157 (c : WCtx L g sc l d e) : d.c.site = .eld →
    ∀ x bs, e.kind = .rd x bs → ∃ v, rebuild 3 bs = .ok v ∧ eldCond (L := L) (g := g) d.b v := by
  intro hs x bs hk
  have hp : e.pc = 1157 := by rw [c.hpc, hs]; rfl
  obtain ⟨v, p, hr, hp0, hrd, hrp⟩ := c.hpay.rowSum x bs hk hp
  obtain ⟨hm, hl, hmx⟩ := c.carry (by rw [hs]; rfl) (by rw [hs]; rfl)
  have hl0 := w0Carry_l_nonneg sc (w0Fin l).1
  exact ⟨v, hr, w0k_e3 _ v hmx hm hl hrd,
    fun _ => w0k_e4 _ v hmx hm hl hrd hl0 hp0⟩

/-- **pc 1187**: the factor. -/
theorem wc_1187 (c : WCtx L g sc l d e) : d.c.site = .efa →
    facCond (lookupD (f_car (scX L) d.b.m d.b.l d.b.mx d.b.sk)) d.b.pe := by
  intro hs
  have hp : e.pc = 1187 := by rw [c.hpc, hs]; rfl
  obtain ⟨hm, hl, hmx⟩ := c.carry (by rw [hs]; rfl) (by rw [hs]; rfl)
  obtain ⟨sk, hsk⟩ := c.sink
  obtain ⟨p, hp0, hrd, hrp⟩ := c.rowSum (c.hld.rowSum (by simp [hp]))
  have hl0 := w0Carry_l_nonneg sc (w0Fin l).1
  obtain ⟨h482, -⟩ := w0k_ew (lookupD (f_car (scX L) d.b.m d.b.l d.b.mx d.b.sk)) d.b.pe
    hmx hm hl hrd
  refine ⟨w0k_e5 _ _ hmx hm hl hrd, fun hf => ?_, w0k_e7 _ _ hmx hm hl hsk hrd hl0 hp0 hrp⟩
  have h0 := w0e_pred_zero (lookupD (f_ew (lookupD (f_car (scX L) d.b.m d.b.l d.b.mx d.b.sk))
    d.b.pe)) (s := w0ESum (w0MxCarry sc (w0Fin l).1) (w0Carry sc (w0Fin l).1).2 + p)
    (by rw [h482]; exact rd_float _)
  rw [h0] at hf
  exact w0k_e6 _ _ hmx hm hl hsk hrd hl0 hp0 hrp (by simpa using hf)

/-- **pc 1202**. -/
theorem wc_1202 (c : WCtx L g sc l d e) : d.c.site = (.oldw 0) →
    Gen.es0_cond (lookupD (f_ow 0 (lookupD (f_car (scX L) d.b.m d.b.l d.b.mx d.b.sk)) (d.b.pe)
    (d.b.o))) := by
  intro hs
  have hp : e.pc = 1202 := by rw [c.hpc, hs]; rfl
  obtain ⟨hm, hl, hmx⟩ := c.carry (by rw [hs]; rfl) (by rw [hs]; rfl)
  obtain ⟨sk, hsk⟩ := c.sink
  obtain ⟨p, hp0, hrd, hrp⟩ := c.rowSum (c.hld.rowSum (by simp [hp]))
  have hl0 := w0Carry_l_nonneg sc (w0Fin l).1
  obtain ⟨ho, O, hO⟩ := c.acc (c.hld.acc (by simp [hp]))
  exact w0k_es 0 _ _ _ hmx hm hl hsk hrd hl0 hp0 hrp ho hO

/-- **pc 1362**. -/
theorem wc_1362 (c : WCtx L g sc l d e) : d.c.site = (.oldw 1) →
    Gen.es1_cond (lookupD (f_ow 1 (lookupD (f_car (scX L) d.b.m d.b.l d.b.mx d.b.sk)) (d.b.pe)
    (d.b.o))) := by
  intro hs
  have hp : e.pc = 1362 := by rw [c.hpc, hs]; rfl
  obtain ⟨hm, hl, hmx⟩ := c.carry (by rw [hs]; rfl) (by rw [hs]; rfl)
  obtain ⟨sk, hsk⟩ := c.sink
  obtain ⟨p, hp0, hrd, hrp⟩ := c.rowSum (c.hld.rowSum (by simp [hp]))
  have hl0 := w0Carry_l_nonneg sc (w0Fin l).1
  obtain ⟨ho, O, hO⟩ := c.acc (c.hld.acc (by simp [hp]))
  exact w0k_es 1 _ _ _ hmx hm hl hsk hrd hl0 hp0 hrp ho hO

/-- **pc 1520**. -/
theorem wc_1520 (c : WCtx L g sc l d e) : d.c.site = (.oldw 2) →
    Gen.es2_cond (lookupD (f_ow 2 (lookupD (f_car (scX L) d.b.m d.b.l d.b.mx d.b.sk)) (d.b.pe)
    (d.b.o))) := by
  intro hs
  have hp : e.pc = 1520 := by rw [c.hpc, hs]; rfl
  obtain ⟨hm, hl, hmx⟩ := c.carry (by rw [hs]; rfl) (by rw [hs]; rfl)
  obtain ⟨sk, hsk⟩ := c.sink
  obtain ⟨p, hp0, hrd, hrp⟩ := c.rowSum (c.hld.rowSum (by simp [hp]))
  have hl0 := w0Carry_l_nonneg sc (w0Fin l).1
  obtain ⟨ho, O, hO⟩ := c.acc (c.hld.acc (by simp [hp]))
  exact w0k_es 2 _ _ _ hmx hm hl hsk hrd hl0 hp0 hrp ho hO

/-- **pc 1677**. -/
theorem wc_1677 (c : WCtx L g sc l d e) : d.c.site = (.oldw 3) →
    Gen.es3_cond (lookupD (f_ow 3 (lookupD (f_car (scX L) d.b.m d.b.l d.b.mx d.b.sk)) (d.b.pe)
    (d.b.o))) := by
  intro hs
  have hp : e.pc = 1677 := by rw [c.hpc, hs]; rfl
  obtain ⟨hm, hl, hmx⟩ := c.carry (by rw [hs]; rfl) (by rw [hs]; rfl)
  obtain ⟨sk, hsk⟩ := c.sink
  obtain ⟨p, hp0, hrd, hrp⟩ := c.rowSum (c.hld.rowSum (by simp [hp]))
  have hl0 := w0Carry_l_nonneg sc (w0Fin l).1
  obtain ⟨ho, O, hO⟩ := c.acc (c.hld.acc (by simp [hp]))
  exact w0k_es 3 _ _ _ hmx hm hl hsk hrd hl0 hp0 hrp ho hO

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Data
