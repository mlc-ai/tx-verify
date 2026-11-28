-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Spec
public import Kernels.InklingRelDecode.Proof.Lib.WideBits
import Kernels.InklingRelDecode.Proof.Lib.Rows

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX

variable {Q : Params} {L : Launch} {m : Mem0}

/-- The token index of a split fits a signed word with room for the padding rows. -/
theorem split_index_small (hp : Pre Q L m) {s : Nat} (hs : s < Q.splits) :
    Q.nTok * s + 11 < 2^31 := by
  have out := hp.outRange
  have pos := hp.nTokPos
  have h1 : Q.nTok * s ≤ Q.splits * Q.nTok := by
    rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ (le_of_lt hs)
  have h2 : Q.splits * Q.nTok ≤ Q.splits * Q.nTok * (heads * headDim) :=
    Nat.le_mul_of_pos_right _ (by decide)
  have h3 : Q.splits * Q.nTok * (heads * headDim) = Q.splits * Q.nTok * heads * headDim := by ring
  have h4 : heads * headDim = 1536 := by decide
  rw [h4] at h2 h3
  omega

/-- The element index of a stored word, and the byte address it names, stay below the
array end: `oLoc` of a valid row. -/
theorem output_word_small (hp : Pre Q L m) {s n h d : Nat} (hs : s < Q.splits)
    (hh : h < heads) (hd : d < headDim) (tn : n < Q.nTok) :
    ((s * Q.nTok + n) * heads + h) * headDim + d < 2^31 := by
  have out := hp.outRange
  have h1 : s * Q.nTok + n + 1 ≤ Q.splits * Q.nTok := by
    have := Nat.mul_le_mul_right Q.nTok (show s + 1 ≤ Q.splits by omega)
    rw [Nat.succ_mul] at this
    omega
  have hh' : h < 12 := hh
  have hd' : d < 128 := hd
  have h2 : (s * Q.nTok + n) * 12 + h + 1 ≤ Q.splits * Q.nTok * 12 := by nlinarith
  have h3 : ((s * Q.nTok + n) * 12 + h) * 128 + d + 1 ≤
      Q.splits * Q.nTok * 12 * 128 := by nlinarith
  have out' : Q.splits * Q.nTok * 12 * 128 < 2^31 := by simpa [heads, headDim] using out
  simp only [heads, headDim]
  omega

/-- The address a register holds for output word `j`, as `oLoc` places it. -/
theorem word_address (hp : Pre Q L m) {s f tok h hb j : Nat} (hs : s < Q.splits)
    (hh : h < 12) (tn : f + tok < Q.nTok) (hbit : hb < 2) (hj : j < 64) :
    (Q.oBase + sx ((((f + (Q.nTok * s + tok)) * 12 + h) % 2^32) * 128 % 2^32) * 4 +
      hb * 256 + 4 * j) % 2^64 =
      (oLoc Q s (f + tok) h (64 * hb + j)).addr ∧ (oLoc Q s (f + tok) h (64 * hb + j)).addr < 2^64
      ∧ (oLoc Q s (f + tok) h (64 * hb + j)).addr % 4 = 0 := by
  have bd := output_word_small hp (h := h) (d := 127) hs (by simp only [heads]; omega)
    (by simp only [headDim]; omega) tn
  simp only [heads, headDim] at bd
  have rng := oLoc_range (Q := Q) s (f + tok) h (64 * hb + j) hs tn (by simp only [heads]; omega)
    (by simp only [headDim]; omega)
  have o := hp.oRange
  have al := hp.oAlign
  have e1 : (f + (Q.nTok * s + tok)) * 12 + h = (s * Q.nTok + (f + tok)) * 12 + h := by ring
  have tb : ((f + (Q.nTok * s + tok)) * 12 + h) * 128 < 2^31 := by rw [e1]; omega
  have small : (((f + (Q.nTok * s + tok)) * 12 + h) % 2^32) * 128 % 2^32 =
      ((f + (Q.nTok * s + tok)) * 12 + h) * 128 := by
    rw [Nat.mod_eq_of_lt (show (f + (Q.nTok * s + tok)) * 12 + h < 2^32 by omega),
      Nat.mod_eq_of_lt (by omega)]
  rw [small, sx_small tb]
  simp only [oLoc] at rng ⊢
  simp only [heads, headDim] at rng ⊢
  rw [e1]
  rw [e1] at tb
  refine ⟨?_, by omega, by omega⟩
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- The address the register of the LSE store holds, as `lseLoc` places it. -/
theorem lse_address (hp : Pre Q L m) {s f tok h : Nat} (hs : s < Q.splits)
    (hh : h < 12) (tn : f + tok < Q.nTok) :
    (Q.lseBase + sx (((f + (Q.nTok * s + tok)) * 12 + h) % 2^32) * 4) % 2^64 =
      (lseLoc Q s (f + tok) h).addr ∧ (lseLoc Q s (f + tok) h).addr < 2^64 ∧
      (lseLoc Q s (f + tok) h).addr % 4 = 0 := by
  have bd := output_word_small hp (h := h) (d := 127) hs (by simp only [heads]; omega)
    (by simp only [headDim]; omega) tn
  simp only [heads, headDim] at bd
  have rng := lseLoc_range (Q := Q) s (f + tok) h hs tn (by simp only [heads]; omega)
  have o := hp.lseRange
  have al := hp.lseAlign
  have e1 : (f + (Q.nTok * s + tok)) * 12 + h = (s * Q.nTok + (f + tok)) * 12 + h := by ring
  have tb : (f + (Q.nTok * s + tok)) * 12 + h < 2^31 := by rw [e1]; omega
  rw [Nat.mod_eq_of_lt (show (f + (Q.nTok * s + tok)) * 12 + h < 2^32 by omega), sx_small tb]
  simp only [lseLoc, heads] at rng ⊢
  rw [e1]
  rw [e1] at tb
  refine ⟨?_, by omega, by omega⟩
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

end PTX.Kernels.InklingRelDecode.Proof.Lib
