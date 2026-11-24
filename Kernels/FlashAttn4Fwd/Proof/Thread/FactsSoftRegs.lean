-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxEvents

@[expose] public section

/-! # The softmax registers of the polls and arrivals

At each poll site the address register holds the barrier's shared address and the parity
register the parity of the poll's index (the statistics index `statsIdx` or the score tile
index `tileIdx`); at each arrival site the pointer register holds the leader's barrier through
its `mapa` pointer and the count register `1`; at each load or store site the address register
holds the stage's columns of the access; at the statistics stores the address register holds
the thread's word and the source register the rescale factor or the row sum. Read off the
state's facts (`SoftmaxTable`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat} {d : D}

theorem regs_statsW0 {t : TState} (hs : d.site = .statsW 0) (h : Holds t.regs (facts L g d)) :
    t.regs 1006 = some (Prologue.sb L (240 + 8 * stOf L g)) ∧
      t.regs 3934 = some (b32 (statsIdx L d % 2)) := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  exact ⟨regv h 1006, regv h 3934⟩

theorem regs_statsW1 {t : TState} (hs : d.site = .statsW 1) (h : Holds t.regs (facts L g d)) :
    t.regs 1974 = some (Prologue.sb L (240 + 8 * stOf L g)) ∧
      t.regs 1975 = some (b32 ((statsIdx L d + 1) % 2)) := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  exact ⟨regv h 1974, regv h 1975⟩

theorem regs_statsW2 {t : TState} (hs : d.site = .statsW 2) (h : Holds t.regs (facts L g d)) :
    t.regs 2687 = some (Prologue.sb L (240 + 8 * stOf L g)) ∧
      t.regs 3934 = some (b32 (statsIdx L d % 2)) := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  exact ⟨regv h 2687, regv h 3934⟩

theorem regs_statsW3 {t : TState} (hs : d.site = .statsW 3) (h : Holds t.regs (facts L g d)) :
    t.regs 2700 = some (Prologue.sb L (240 + 8 * stOf L g)) ∧
      t.regs 3934 = some (b32 (statsIdx L d % 2)) := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  exact ⟨regv h 2700, regv h 3934⟩

theorem regs_sW0 {t : TState} (hs : d.site = .sW false) (h : Holds t.regs (facts L g d)) :
    t.regs 1007 = some (Prologue.sb L (128 + 8 * stOf L g)) ∧
      t.regs 3935 = some (b32 (tileIdx L d % 2)) := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  exact ⟨regv h 1007, regv h 3935⟩

theorem regs_sW1 {t : TState} (hs : d.site = .sW true) (h : Holds t.regs (facts L g d)) :
    t.regs 1980 = some (Prologue.sb L (128 + 8 * stOf L g)) ∧
      t.regs 3935 = some (b32 (tileIdx L d % 2)) := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  exact ⟨regv h 1980, regv h 3935⟩

theorem regs_pArr0 {t : TState} (hs : d.site = .pArr false) (h : Holds t.regs (facts L g d)) :
    t.regs 405 = some (leadPtr L g (144 + 8 * stOf L g)) ∧
      t.regs 1955 = some (b32 1) := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  exact ⟨regv h 405, regv h 1955⟩

theorem regs_pArr1 {t : TState} (hs : d.site = .pArr true) (h : Holds t.regs (facts L g d)) :
    t.regs 405 = some (leadPtr L g (144 + 8 * stOf L g)) ∧
      t.regs 2668 = some (b32 1) := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  exact ⟨regv h 405, regv h 2668⟩

theorem regs_p2Arr0 {t : TState} (hs : d.site = .p2Arr false) (h : Holds t.regs (facts L g d)) :
    t.regs 406 = some (leadPtr L g (160 + 8 * stOf L g)) ∧
      t.regs 1973 = some (b32 1) := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  exact ⟨regv h 406, regv h 1973⟩

theorem regs_p2Arr1 {t : TState} (hs : d.site = .p2Arr true) (h : Holds t.regs (facts L g d)) :
    t.regs 406 = some (leadPtr L g (160 + 8 * stOf L g)) ∧
      t.regs 2686 = some (b32 1) := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  exact ⟨regv h 406, regv h 2686⟩

theorem regs_ldF0 {t : TState} (hs : d.site = .ld false 0) (h : Holds t.regs (facts L g d))
    : t.regs 1094 = some (b32 (tmem L g 0)) := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  exact regv h 1094

theorem regs_ldF1 {t : TState} (hs : d.site = .ld false 1) (h : Holds t.regs (facts L g d))
    : t.regs 1096 = some (b32 (tmem L g 32)) := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  exact regv h 1096

theorem regs_ldF2 {t : TState} (hs : d.site = .ld false 2) (h : Holds t.regs (facts L g d))
    : t.regs 1097 = some (b32 (tmem L g 64)) := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  exact regv h 1097

theorem regs_ldF3 {t : TState} (hs : d.site = .ld false 3) (h : Holds t.regs (facts L g d))
    : t.regs 1095 = some (b32 (tmem L g 96)) := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  exact regv h 1095

theorem regs_ldT0 {t : TState} (hs : d.site = .ld true 0) (h : Holds t.regs (facts L g d))
    : t.regs 2057 = some (b32 (tmem L g 0)) := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  exact regv h 2057

theorem regs_ldT1 {t : TState} (hs : d.site = .ld true 1) (h : Holds t.regs (facts L g d))
    : t.regs 2059 = some (b32 (tmem L g 32)) := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  exact regv h 2059

theorem regs_ldT2 {t : TState} (hs : d.site = .ld true 2) (h : Holds t.regs (facts L g d))
    : t.regs 2060 = some (b32 (tmem L g 64)) := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  exact regv h 2060

theorem regs_ldT3 {t : TState} (hs : d.site = .ld true 3) (h : Holds t.regs (facts L g d))
    : t.regs 2058 = some (b32 (tmem L g 96)) := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  exact regv h 2058

/-- The rescale factor has four bytes. -/
theorem alphaV_bytes (L : Launch) (d : D) : (alphaV L d).bytes = 4 := by
  unfold alphaV
  split
  · rfl
  · cases h : ex2E true (gapV L d.m d.w) with
    | ok v => exact ex2E_four true _ v h
    | error e => rfl

theorem regs_alphaSt {t : TState} (hs : d.site = .alphaSt) (h : Holds t.regs (facts L g d)) :
    t.regs 2395 = some (Prologue.sb L (4 * tidOf L g)) ∧ t.regs 513 = some (alphaV L d) := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  exact ⟨regv h 2395, regv h 513⟩

theorem regs_lSt {t : TState} (hs : d.site = .lSt) (h : Holds t.regs (facts L g d)) :
    t.regs 2699 = some (Prologue.sb L (4 * tidOf L g)) ∧ t.regs 3933 = some d.l := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  exact ⟨regv h 2699, regv h 3933⟩

theorem regs_gen {t : TState} {j : Fin 3} (hs : d.site = .gen j) (h : Holds t.regs (facts L g d)) :
    t.regs 1017 = some (b32 (kOf L g + 3 + 4 * stOf L g)) := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  rcases fin3_cases j with rfl | rfl | rfl
  · exact regv h 1017
  · exact regv h 1017
  · exact regv h 1017

theorem regs_pstF0 {t : TState} (hs : d.site = .pst false 0) (h : Holds t.regs (facts L g d))
    : t.regs 1097 = some (b32 (tmem L g 64)) := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  exact regv h 1097

theorem regs_pstF1 {t : TState} (hs : d.site = .pst false 1) (h : Holds t.regs (facts L g d))
    : t.regs 1099 = some (b32 (tmem L g 80)) := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  exact regv h 1099

theorem regs_pstF2 {t : TState} (hs : d.site = .pst false 2) (h : Holds t.regs (facts L g d))
    : t.regs 1095 = some (b32 (tmem L g 96)) := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  exact regv h 1095

theorem regs_pstF3 {t : TState} (hs : d.site = .pst false 3) (h : Holds t.regs (facts L g d))
    : t.regs 1098 = some (b32 (tmem L g 112)) := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  exact regv h 1098

theorem regs_pstT0 {t : TState} (hs : d.site = .pst true 0) (h : Holds t.regs (facts L g d))
    : t.regs 2060 = some (b32 (tmem L g 64)) := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  exact regv h 2060

theorem regs_pstT1 {t : TState} (hs : d.site = .pst true 1) (h : Holds t.regs (facts L g d))
    : t.regs 2062 = some (b32 (tmem L g 80)) := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  exact regv h 2062

theorem regs_pstT2 {t : TState} (hs : d.site = .pst true 2) (h : Holds t.regs (facts L g d))
    : t.regs 2058 = some (b32 (tmem L g 96)) := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  exact regv h 2058

theorem regs_pstT3 {t : TState} (hs : d.site = .pst true 3) (h : Holds t.regs (facts L g d))
    : t.regs 2061 = some (b32 (tmem L g 112)) := by
  obtain ⟨site, ii, tt, w, mm, l⟩ := d
  simp only at hs
  subst hs
  exact regv h 2061

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
