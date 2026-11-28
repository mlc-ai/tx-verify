-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Prologue.Ledger
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Prologue
open PTX Control

private theorem init_not_bar2 (i : Fin 12) : afterInit i ≠ .bar2 := by
  simp only [afterInit]
  split <;> simp

private theorem head_site (s : Site) (h : s.rank < Site.bar2.rank) :
    s = .sMax ∨ (∃ i, s = .ld i) ∨ (∃ i, s = .el i) ∨ (∃ i, s = .init i) ∨ s = .fnc0 := by
  revert h
  cases s <;> first | (intro _; exact .inl rfl) | (intro _; exact .inr (.inr (.inr (.inr rfl)))) |
    (intro _; exact .inr (.inl ⟨_,rfl⟩)) | (intro _; exact .inr (.inr (.inl ⟨_,rfl⟩))) |
    (intro _; exact .inr (.inr (.inr (.inl ⟨_,rfl⟩)))) |
    (repeat' first | decide +kernel | (rename_i j; revert j))

/-- The first barrier of the preload follows only the shared proxy fence of the prologue. -/
theorem barrier_predecessor {Q L g d ev dn} (hn : Control.next Q L g d ev = some (some dn))
    (site : dn.site = .bar2) : d.site = .fnc0 := by
  have lt := rank_next hn
  rw [site] at lt
  obtain ⟨s,a,b,c,w⟩ := d
  rcases head_site s lt with rfl|⟨i,rfl⟩|⟨i,rfl⟩|⟨i,rfl⟩|rfl
  · cases hn; cases site
  · fin_cases i <;> simp only [Control.next] at hn <;> split at hn <;> cases hn <;> cases site
  · simp only [Control.next] at hn
    split at hn <;> try contradiction
    cases hn
    split at site
    · cases site
    · exact absurd site (init_not_bar2 i)
  · cases hn; exact absurd site (init_not_bar2 i)
  · rfl

end PTX.Kernels.InklingRelDecode.Proof.Prologue
