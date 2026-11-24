-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Audit.ResidualSample
public import Kernels.FlashKdaFwd.Proof.ValuePerturbation
import Mathlib.Tactic

/-! End-to-end error certificates derived from the recorded bfloat16 corrections and binary32
tile boundary states. All rational checks run in the Lean kernel. -/
@[expose] public section
namespace FlashKda.Sample.Weighted
open Sequence Chunk Algorithm Stability Finset ValuePerturbation

def carryWord (b : ℕ) := carryWords.getD b (0,0,0)
def row (b : ℕ) : Triple :=
  let w := carryWord b
  ⟨(PTX.f32Value w.1).getD 0, (PTX.f32Value w.2.1).getD 0, (PTX.f32Value w.2.2).getD 0⟩
def correction (t : ℕ) := (PTX.FloatFmt.bf16.decode (correctionWords.getD t 0)).getD 0
def gapBudget (b : ℕ) := gapBounds.getD b 0
def gapSum (n : ℕ) := ∑ b ∈ range n, gapBudget b
def key (t : ℕ) := normalized (measurement t).key
def query (t : ℕ) := normalized (measurement t).query
def reconstructed (b : ℕ) : ℕ → Triple
  | 0 => row b
  | j+1 => (reconstructed b j).add ((key (16*b+j)).scale (correction (16*b+j)))
def mismatch (t : ℕ) :=
  correction t - (value t - (reconstructed (t/16) (t%16)).inner (key t))/2
def weightedSum (n : ℕ) := ∑ t ∈ range n, 2*(mismatch t)^2
def readoutGap (t : ℕ) :=
  |outputValue t - (reconstructed (t/16) (t%16+1)).inner (query t)|
def outputSlack (t : ℕ) := 7576/1000000 - readoutGap t - gapSum (t/16)
def finalSlack := 7354/1000000 - gapSum 3

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

theorem finite : carryWords.size = 4 ∧ correctionWords.size = 33 ∧ gapBounds.size = 3 ∧
    (∀ b : Fin 4, PTX.f32Value (carryWord b).1 = some (row b).a ∧
      PTX.f32Value (carryWord b).2.1 = some (row b).b ∧
      PTX.f32Value (carryWord b).2.2 = some (row b).c) ∧
    ∀ t : Fin 33, PTX.FloatFmt.bf16.decode (correctionWords.getD t 0) = some (correction t) := by
  decide +kernel

theorem checked_gaps : ∀ b : Fin 3, 0 ≤ gapBudget b ∧
    ((row (b.val+1)).sub (reconstructed b (liveRows 33 b))).squared ≤ (gapBudget b)^2 := by
  decide +kernel

theorem checked_outputs : ∀ t : Fin 33, 0 ≤ outputSlack t ∧
    weightedSum (t.val+1) ≤ (outputSlack t)^2 := by decide +kernel

theorem checked_final : 0 ≤ finalSlack ∧ weightedSum 33 ≤ finalSlack^2 := by decide +kernel

noncomputable section

def carries (b : ℕ) := embed (row b)
def updates (b j : ℕ) := (correction (16*b+j) : ℝ)

private theorem norm_key {t : ℕ} (ht : t < 33) : input.key t = embed (key t) :=
  normalization _ (Sample.checked ⟨t,ht⟩).2.1

private theorem decay (s : Row 128) (off t : ℕ) : Residual.decayed (suffix input off) s t = s := by
  funext i
  simp [Residual.decayed, suffix, input, activate, logGate]

theorem state_eq (b j : ℕ) (live : j ≤ liveRows 33 b) :
    Residual.state (suffix input (cursor 33 b)) (carries b) (updates b) j =
      embed (reconstructed b j) := by
  induction j with
  | zero => exact Residual.state_zero _ _ _
  | succ j ih =>
    have start : cursor 33 b = 16*b := by unfold liveRows cursor at *; omega
    have hr : 16*b+j < 33 := by unfold liveRows cursor at live; omega
    rw [Residual.state_succ, decay, ih (by omega)]
    funext i
    change _ + _ * input.key (cursor 33 b+j) i = _
    rw [start, norm_key hr]
    simp only [reconstructed, embed_add, embed_scale, updates]
    ring

theorem residual_eq {t : ℕ} (ht : t < 33) :
    atToken input 33 carries updates t = (mismatch t : ℝ) := by
  let b := t/16
  have start : cursor 33 b+t%16=t := by dsimp [cursor,b]; omega
  have live : t%16 ≤ liveRows 33 b := by dsimp [liveRows,cursor,b]; omega
  unfold atToken
  rw [Residual.local_residual, decay, state_eq b _ live]
  change updates b (t%16) - input.strength (cursor 33 b+t%16) *
    (input.value (cursor 33 b+t%16) - dot _ (input.key (cursor 33 b+t%16))) = _
  rw [start, norm_key ht, embed_inner]
  have index : 16*b+t%16=t := by dsimp [b]; omega
  simp only [updates, index, mismatch, b]
  change _ - (1/(1+Real.exp (-0))) * ((value t : ℝ) - _) = _
  push_cast
  norm_num
  ring

theorem charge_eq {n : ℕ} (hn : n ≤ 33) :
    charge input 33 carries updates n = (weightedSum n : ℝ) := by
  simp only [charge, weightedSum, Rat.cast_sum, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow]
  apply sum_congr rfl
  intro t ht
  rw [residual_eq (lt_of_lt_of_le (mem_range.mp ht) hn)]
  have beta : input.strength t = 1/2 := by norm_num [input,activate,sigmoid]
  rw [beta]
  ring

theorem gaps_le {n : ℕ} (hn : n ≤ 3) : gaps input 33 carries updates n ≤ (gapSum n : ℝ) := by
  simp only [gaps, gapSum, Rat.cast_sum]
  apply sum_le_sum
  intro b hb
  have p := checked_gaps ⟨b,lt_of_lt_of_le (mem_range.mp hb) hn⟩
  unfold Residual.exitGap
  rw [state_eq b _ le_rfl]
  exact magnitude p.1 p.2

theorem bounds :
    (∀ t : Fin 33, |(outputValue t : ℝ) - output input (embed (approx 0)) 33 1 t| ≤ 7576/1000000) ∧
    distance (embed finalValue) (tokenState input (embed (approx 0)) 33) ≤ 7354/1000000 := by
  have start : carries 0 = embed (approx 0) := by
    simp [carries, row, show carryWord 0 = initialWords by rfl, initial_words.1,
      initial_words.2.1, initial_words.2.2]
  have finish : carries 3 = embed finalValue := by rfl
  rw [← start, ← finish]
  have good : admissible input := activated_admissible _ _ _ _ _ _ _ _ le_rfl
  have h := ValuePerturbation.forward input good (fun t => normalized_energy _) 33
    (fun t _ => positive_strength _ _ _ _ _ _ _ _ t) (carries 0) carries updates
    (fun t => (outputValue t : ℝ)) 1
  have zero : distance (carries 0) (carries 0) = 0 := by simp [distance, length, energy]
  constructor
  · intro t
    have a := h.1 t t.isLt
    have live : t.val%16+1 ≤ liveRows 33 (t.val/16) := by dsimp [liveRows,cursor]; omega
    have qt : input.query t = embed (query t) := normalization _ (Sample.checked t).1
    simp only [zero, zero_pow (by decide : 2 ≠ 0), zero_add, one_mul, abs_one, state_eq _ _ live,
      qt, embed_inner, charge_eq t.isLt] at a
    have costs := checked_outputs t
    have sq : √(weightedSum (t.val+1) : ℝ) ≤ (outputSlack t : ℝ) := by
      apply Real.sqrt_le_iff.mpr
      exact_mod_cast costs
    have g := gaps_le (n := t.val/16) (by omega)
    have rd :
        |(outputValue t : ℝ) - ((reconstructed (t.val/16) (t.val%16+1)).inner (query t) : ℝ)| =
        (readoutGap t : ℝ) := by simp [readoutGap]
    rw [rd] at a
    unfold outputSlack at sq
    push_cast at sq
    linarith
  · have a := h.2
    change distance (carries 3) _ ≤ gaps input 33 carries updates 3 + _ at a
    rw [zero, zero_pow (by decide : 2 ≠ 0), zero_add, charge_eq le_rfl] at a
    have sq : √(weightedSum 33 : ℝ) ≤ (finalSlack : ℝ) := by
      apply Real.sqrt_le_iff.mpr
      exact_mod_cast checked_final
    have g := gaps_le (n := 3) le_rfl
    unfold finalSlack at sq
    push_cast at sq
    linarith

end
end FlashKda.Sample.Weighted
