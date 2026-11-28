-- SPDX-License-Identifier: Apache-2.0
-- domain: valid-rows
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.W0Value

@[expose] public section

/-! # A row-maximum word is a finite number or negative infinity

A clean four-byte word that reads as a real number reads as a finite number (`W0Fin`); a word of the
kind `SK.ni` (`Lemmas/Flow/OutKinds`) is such a word or the pattern of negative infinity, which
is what the exchange word of a valid block is (`W0Ok.pm`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Flow

/-- A value that the ideal rule reads as a real number reads as a finite number. -/
theorem w0Fin_of_readEReal {v : Value} {r : ℝ}
    (h : PTX.Assumption.readEReal .f32 v = some (.ok (r : EReal))) : W0Fin v := by
  by_cases hf : ∃ y : ℝ, v = .float .f32 y
  · obtain ⟨y, rfl⟩ := hf
    exact ⟨y, by simp [valFloat, pure, Except.pure]⟩
  have hv : valFloat .f32 v = bitsAsFloat .f32 v := by
    cases v with
    | float f y =>
      by_cases hff : f = .f32
      · subst hff; exact absurd ⟨y, rfl⟩ hf
      · simp [valFloat, hff]
    | _ => rfl
  have hr : PTX.Assumption.readEReal .f32 v =
      PTX.Assumption.readEReal.ofDatum (classify .f32 v) := by
    cases v with
    | float f y =>
      by_cases hff : f = .f32
      · subst hff; exact absurd ⟨y, rfl⟩ hf
      · simp [PTX.Assumption.readEReal, hff]
    | _ => rfl
  rw [hr] at h
  unfold W0Fin
  rw [hv]
  unfold bitsAsFloat
  cases hc : classify .f32 v with
  | error e => rw [hc] at h; simp [PTX.Assumption.readEReal.ofDatum] at h
  | ok f =>
    rw [hc] at h
    cases f with
    | zero neg => exact ⟨0, rfl⟩
    | fin q => exact ⟨q, rfl⟩
    | inf neg =>
      exfalso
      simp only [PTX.Assumption.readEReal.ofDatum, pure, Except.pure, Option.some.injEq,
        Except.ok.injEq] at h
      split_ifs at h with hn
      · exact EReal.coe_ne_bot r h.symm
      · exact EReal.coe_ne_top r h.symm
    | nan n => simp [PTX.Assumption.readEReal.ofDatum] at h

/-- **A word of the kind `SK.ni` is valid for `W0Ok.pm`.** -/
theorem w0Ok_pm_of_has {v : Value} (h : SK.ni.Has v) :
    PTX.Flow.Clean v ∧ (W0Fin v ∨ v = w0NegInf) := by
  rcases h with ⟨hc, r, hr⟩ | rfl
  · exact ⟨hc, Or.inl (w0Fin_of_readEReal hr)⟩
  · exact ⟨clean_negInf, Or.inr rfl⟩

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
