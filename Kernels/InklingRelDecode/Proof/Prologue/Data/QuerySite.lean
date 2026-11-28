-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Steps.QuerySkip

@[expose] public section

/-! # The query site after a load or a gate

The successor of a query load, or the first query site of a launch, is the first load whose group
is on, or the first store; the groups it passes are off. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Data
open PTX PTX.Proof PTX.Flow Control

/-- **The first query site from group `g0`** is load or store `hi`, and the groups before it are
off. -/
theorem querySite_spec (tid : Nat) (d : Control.D) (g0 : Nat) (hg : g0 ≤ 4) :
    ∃ hi : Nat, hi ≤ 64 ∧ 16 * g0 ≤ hi ∧ querySite tid d g0 = qSiteAt hi ∧
      (∀ n, 16 * g0 ≤ n → n < hi → queryOn tid (n / 16) d = false) ∧
      (hi < 64 → queryOn tid (hi / 16) d = true) := by
  unfold querySite
  split_ifs with h0 h1 h2 h3
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h0
    exact ⟨0, by omega, by omega, rfl, fun n h1 h2 => by omega, fun _ => h0.2⟩
  · simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at h0 h1
    refine ⟨16, by omega, by omega, rfl, fun n h1' h2 => ?_, fun _ => h1.2⟩
    have : n / 16 = 0 := by omega
    rw [this]; simpa using h0 (by omega)
  · simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at h0 h1 h2
    refine ⟨32, by omega, by omega, rfl, fun n h1' h2' => ?_, fun _ => h2.2⟩
    by_cases hn : n / 16 = 0
    · rw [hn]; simpa using h0 (by omega)
    · have : n / 16 = 1 := by omega
      rw [this]; simpa using h1 (by omega)
  · simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at h0 h1 h2 h3
    refine ⟨48, by omega, by omega, rfl, fun n h1' h2' => ?_, fun _ => h3.2⟩
    by_cases hn : n / 16 = 0
    · rw [hn]; simpa using h0 (by omega)
    · by_cases hn1 : n / 16 = 1
      · rw [hn1]; simpa using h1 (by omega)
      · have : n / 16 = 2 := by omega
        rw [this]; simpa using h2 (by omega)
  · simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at h0 h1 h2 h3
    refine ⟨64, le_rfl, by omega, rfl, fun n h1' h2' => ?_, fun h => absurd h (by omega)⟩
    by_cases hn : n / 16 = 0
    · rw [hn]; simpa using h0 (by omega)
    · by_cases hn1 : n / 16 = 1
      · rw [hn1]; simpa using h1 (by omega)
      · by_cases hn2 : n / 16 = 2
        · rw [hn2]; simpa using h2 (by omega)
        · have : n / 16 = 3 := by omega
          rw [this]; simpa using h3 (by omega)

/-- **The site after the load `j`** is a load or the store `hi`; the loads between are off. -/
theorem after_site (d : Control.D) (tid : Nat) (j : Fin 64)
    (hon : queryOn tid (j.val / 16) d = true) :
    ∃ hi : Nat, hi ≤ 64 ∧ j.val < hi ∧ afterQuery d tid j = qSiteAt hi ∧
      (∀ n, j.val < n → n < hi → queryOn tid (n / 16) d = false) ∧
      (hi < 64 → queryOn tid (hi / 16) d = true) := by
  unfold afterQuery
  split_ifs with h h2
  · obtain ⟨hi, h1, h3, h4, h5, h6⟩ := querySite_spec tid d ((j.val + 1) / 16) (by omega)
    exact ⟨hi, h1, by omega, h4, fun n a b => h5 n (by omega) b, h6⟩
  · refine ⟨j.val + 1, by omega, by omega, by simp [qSiteAt, h], fun n a b => by omega, fun _ => ?_⟩
    rwa [show (j.val + 1) / 16 = j.val / 16 by omega]
  · exact ⟨64, le_rfl, by omega, by simp [qSiteAt], fun n a b => by omega, fun h => by omega⟩

end PTX.Kernels.InklingRelDecode.Proof.Prologue.Data
