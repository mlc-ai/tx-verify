-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Interface.SvDef

@[expose] public section

/-!
# The score stage's words are the row's masked logits

At the wait on the S tile's load the machine holds the S words (`D.sv`: the loaded scores) and the
bias words of the block (`D.w`). The score stage turns them into the final score words `D.fin`: the
scores as they are (a block before `n_bias`: no bias, all keys visible), the scores plus the bias
(a block whose last key is visible) or the biased scores with the invisible keys masked to `-inf`.
`fin_sv` states the three cases in one form: every word is the float of the key's logit where the
key is visible, `-inf` where it is not, for the words of a thread whose S words are the exact
scores (`Spec.score`) and whose bias words are the keys' biases (`Spec.bias`). `own_fin` is the
list of the visible logits, `halfScores`.
-/

namespace PTX.Kernels.InklingRelDecode.Proof.Sv
open PTX PTX.Proof PTX.Flow PTX.Kernels.InklingRelDecode.Proof.Sm

noncomputable section
open Classical

theorem nBias_mul_le (Q : Params) (r : Nat) : Q.nBias r * 128 ≤ Q.past r := by
  unfold Params.nBias
  omega

variable {Q : Params} {L : Launch} {g r s kvh : Nat} {d : D}

/-- The machine's visibility test is `visB`. -/
theorem visK_iff (hE : EntFull Q r s kvh d.e) (k : Nat) :
    visK d.e (g % L.block) d.n k = true ↔ visB Q r s (tokOf (g % L.block)) d.i
      (half (g % L.block)) k := by
  unfold visK visB D.n
  rw [keyB_eq hE, hE.past]
  simp only [decide_eq_true_eq]

/-- **The final score words.** For a state at the wait on the S tile's load with the 64 bias words
loaded, whose S words are the exact scores of the keys of the thread's half of the block
and whose bias words are their biases: word `k` of `D.fin` is the float of the key's logit where
the key is visible and `-inf` where it is not. -/
theorem fin_sv (hE : EntFull Q r s kvh d.e) (hsv : ∀ k < 64, (d.sv k).1 = Value.float .f32
      (score Q r (tokOf (g % L.block)) (kvh * 6 + remOf (g % L.block))
        (keyB Q s d.i (half (g % L.block)) k)))
    (hbw : ∀ k < 64, bfR (d.w k) =
      biasB Q r s (tokOf (g % L.block)) (kvh * 6 + remOf (g % L.block)) d.i
        (half (g % L.block)) k)
    (hcw : d.cw = 64) :
    ∀ k < 64, ((D.fin L g d).sv k).1 =
      if visB Q r s (tokOf (g % L.block)) d.i (half (g % L.block)) k then
        Value.float .f32 (logitB Q r s (tokOf (g % L.block)) (kvh * 6 + remOf (g % L.block)) d.i
          (half (g % L.block)) k)
      else infB := by
  intro k hk
  have hscd : d.scd k = logitB Q r s (tokOf (g % L.block)) (kvh * 6 + remOf (g % L.block)) d.i
      (half (g % L.block)) k := by
    unfold D.scd D.bR D.wd logitB
    have hkc : k < d.cw := by omega
    simp only [hkc, ↓reduceIte]
    rw [hbw k hk, hsv k hk, hE.sc]
    simp only [bfR, biasB]
    ring
  have hnb := nBias_mul_le Q r
  unfold D.fin
  by_cases h96 : pr96 d.e d.n = true
  · -- no bias: every key is visible and the bias is zero
    simp only [h96, ↓reduceIte]
    have hn : d.n < Q.nBias r := by
      have := h96
      unfold pr96 at this
      rw [hE.nbias] at this
      simpa using this
    have hkey : keyB Q s d.i (half (g % L.block)) k < Q.nBias r * 128 := by
      have h1 := hE.blk d.i
      unfold keyB D.n blkOf at *
      have := Nat.mul_lt_mul_of_pos_right hn (by norm_num : 0 < 128)
      have h2 : half (g % L.block) < 2 := by unfold Sm.half; omega
      omega
    have hvis : visB Q r s (tokOf (g % L.block)) d.i (half (g % L.block)) k := by
      unfold visB
      omega
    simp only [hvis, ↓reduceIte]
    rw [hsv k hk]
    unfold logitB
    have hb0 : bias Q r (tokOf (g % L.block)) (kvh * 6 + remOf (g % L.block))
        (keyB Q s d.i (half (g % L.block)) k) = 0 := by
      unfold bias
      have hlt : ¬ Q.nBias r * 128 ≤ keyB Q s d.i (half (g % L.block)) k := by omega
      simp only [hlt, ↓reduceIte]
    rw [hb0]
    simp
  · simp only [h96]
    by_cases h97 : pr97 d.e d.n = true
    · simp only [h97, ↓reduceIte]
      have hvis : visB Q r s (tokOf (g % L.block)) d.i (half (g % L.block)) k := by
        have h := h97
        unfold pr97 at h
        simp only [decide_eq_true_eq] at h
        unfold visB
        rw [keyB_eq hE]
        unfold D.n at h
        rw [hE.past] at h
        have h2 : half (g % L.block) < 2 := by unfold Sm.half; omega
        omega
      simp only [hvis, ↓reduceIte]
      show (scSv d 32 k).1 = _
      unfold scSv
      have hk2 : k / 2 < 32 := by omega
      simp only [hk2, ↓reduceIte, hscd]
    · simp only [h97]
      show (mSv L g d 32 k).1 = _
      unfold mSv
      have hm : msk 32 (k / 2) = true := by
        unfold msk
        simp only [show (32 : Nat) ≠ 1 by norm_num, ↓reduceIte, decide_eq_true_eq]
        omega
      simp only [hm, ↓reduceIte]
      show mw d.e (g % L.block) d.n d.scd k = _
      unfold mw
      by_cases hv : visK d.e (g % L.block) d.n k = true
      · have hv' := (visK_iff hE k).mp hv
        simp only [hv, hv', ↓reduceIte, hscd]
      · have hv' : ¬ visB Q r s (tokOf (g % L.block)) d.i (half (g % L.block)) k :=
          fun h => hv ((visK_iff hE k).mpr h)
        simp only [hv, hv', ↓reduceIte, Bool.false_eq_true]

/-- **The visible logits are the thread's scores.** For the final words of `fin_sv` the floats
among the 64 words are the logits of the visible keys, in column order. -/
theorem own_fin {tok head b h : Nat} (f : Nat → { v : Value // v.bytes = 4 })
    (hf : ∀ k < 64, (f k).1 = if visB Q r s tok b h k then
      Value.float .f32 (logitB Q r s tok head b h k) else infB) :
    (List.range 64).filterMap (fun k => match (f k).1 with
      | .float _ x => some x
      | _ => none) = halfScores Q r s tok head b h := by
  unfold halfScores
  rw [← filterMap_range_eq (fun k => decide (visB Q r s tok b h k))
    (logitB Q r s tok head b h) 64]
  apply List.filterMap_congr
  intro k hk
  rw [hf k (List.mem_range.mp hk)]
  by_cases hv : visB Q r s tok b h k <;> simp [hv, infB, b32]

end
end PTX.Kernels.InklingRelDecode.Proof.Sv
