-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Data.InverseResidual
public import Kernels.FlashKdaFwd.Proof.InverseStability
import Mathlib.Tactic

/-! Certify all 768 inverse entries recorded from the three preparation tiles. -/
@[expose] public section
namespace FlashKda.Sample.InverseCheck
open Chunk Block Inverse Sequence Stability InverseStability Algorithm Finset Matrix
noncomputable section
def tokens (b : Fin 3) : Tokens 128 := activate
  (fun _ _ => 0) (fun t => embed (raw (sourceKey b t))) (fun _ _ => 0)
  (fun _ => 0) (fun _ => 0) 0 0 (fun _ => 0)
theorem norm_key (b : Fin 3) (i : ℕ) :
    (tokens b).key i = embed (normalized (sourceKey b i)) := by
  by_cases hi : offset b i < 33
  · apply normalization
    simpa [sourceKey,hi] using (checked ⟨offset b i,hi⟩).2.1
  · funext j
    simp [tokens, activate, sourceKey, hi, raw, normalized, Triple.scale, embed,
      OneToken.four, Algorithm.normalize, dot]

theorem system_cast (b : Fin 3) :
    system 16 (lower (tokens b)) = (coefficientQ b).map (Rat.cast : ℚ → ℝ) := by
  ext i j
  by_cases h : j < i
  · have rest (t : Nat) : restored (cum (tokens b).logDecay) (tokens b).key t =
        embed (normalized (sourceKey b t)) := by
      rw [← norm_key]
      funext l
      simp [restored, cum, tokens, activate, logGate]
    have weightedKey (t : Nat) : weighted (cum (tokens b).logDecay) (tokens b).key t =
        embed (normalized (sourceKey b t)) := by
      rw [← norm_key]
      funext l
      simp [weighted, cum, tokens, activate, logGate]
    simp only [system, show j.val < i.val from h, ite_true, lower, coefficient, rest, weightedKey,
      embed_inner, Matrix.map_apply, coefficientQ, ite_eq_left h]
    norm_num [tokens, activate, sigmoid]
    ring
  · by_cases e : i = j
    · subst j
      simp [system, coefficientQ, Inverse.delta]
    · have v : i.val ≠ j.val := fun z => e (Fin.ext z)
      simp [system, show ¬(j.val < i.val) from h, h, coefficientQ, Inverse.delta, e, v]

theorem bounded (b : Fin 3) :
    let j := (stored b).map (Rat.cast : ℚ → ℝ)
    ∑ c, ∑ i, (j i c - blockInverse (lower (tokens b)) i c)^2 ≤ (cap b : ℝ)^2 := by
  have good : admissible (tokens b) := activated_admissible _ _ _ _ _ _ _ _ le_rfl
  have h := inverse_residual (tokens b) good ((stored b).map (Rat.cast : ℚ → ℝ))
  have budget : tested b := by
    fin_cases b
    · exact first
    · exact second
    · exact tail_tile
  unfold tested at budget
  rw [system_cast] at h
  apply h.trans
  have cast := (Rat.cast_le (K := ℝ)).2 budget
  have castIf (i j : Full) : ((if i=j then 1 else 0 : ℚ) : ℝ) = if i=j then 1 else 0 := by
    split_ifs <;> simp
  simpa [Matrix.mul_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply,
    castIf] using cast

end
end FlashKda.Sample.InverseCheck
