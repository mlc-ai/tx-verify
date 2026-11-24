-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Export.Region
public import Kernels.TmlFa4Fwd.Proof.Softmax.Data.RoundFrame

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Values
open Softmax

/-- The portion of the round after the chosen load and through the fourth P store. -/
def readRegion (r : Rd) (load s : Site) : Bool :=
  decide (load.pos < s.pos ∧ s.pos ≤ (Site.pst r 3).pos)

private theorem score_cut (r : Rd) (c : Fin 4) (lz : Bool) :
    entersOnly (readRegion r (.sld r c)) (· == .sld r c) lz = true := by
  cases r <;> revert c lz <;> decide +kernel

private theorem bias_cut (z : Bool) (b : Fin 16) (lz : Bool) :
    entersOnly (readRegion (rdOf z) (.bld z b)) (· == .bld z b) lz = true := by
  cases z <;> revert b lz <;> decide +kernel

private theorem region_body (r : Rd) (s : Site) (load : Site)
    (lb : (Site.sld r 0).pos ≤ load.pos) (inside : readRegion r load s = true) :
    Data.body s = true ∧ pollOff s ≠ 80 := by
  have tab : ∀ r : Rd, allSites.all (fun s => !(readRegion r (.sld r 0) s) ||
      (Data.body s && (pollOff s != 80))) = true := by intro r; cases r <;> decide +kernel
  have h := List.all_eq_true.mp (tab r) s (mem_allSites _)
  have hr : readRegion r (.sld r 0) s = true := by
    simp only [readRegion,decide_eq_true_eq] at inside ⊢
    exact ⟨lt_of_le_of_lt lb inside.1,inside.2⟩
  simpa only [hr,Bool.not_true,Bool.false_or,Bool.and_eq_true,bne_iff_ne] using h

theorem score_region (r : Rd) (c : Fin 4) (lz : Bool) :
    entersOnly (readRegion r (.sld r c)) (· == .sld r c) lz = true ∧
    (∀ q : Fin 4, readRegion r (.sld r c) (.pst r q) = true) ∧
    ∀ s, readRegion r (.sld r c) s = true →
      Data.body s = true ∧ pollOff s ≠ 80 ∧ ∀ r', s ≠ .sld r' c := by
  refine ⟨score_cut r c lz,?_,?_⟩
  · cases r <;> revert c <;> decide +kernel
  · intro s hs
    have lb : ∀ r (c : Fin 4), (Site.sld r 0).pos ≤ (Site.sld r c).pos := by
      intro r; cases r <;> decide +kernel
    obtain ⟨body,off⟩ := region_body r s _ (lb r c) hs
    refine ⟨body,off,?_⟩
    rintro r' rfl
    have no : ∀ r r' (c : Fin 4), readRegion r (.sld r c) (.sld r' c) = false := by
      intro r r'; cases r <;> cases r' <;> decide +kernel
    rw [no] at hs
    cases hs

theorem bias_region (z : Bool) (b : Fin 16) (lz : Bool) :
    entersOnly (readRegion (rdOf z) (.bld z b)) (· == .bld z b) lz = true ∧
    (∀ q : Fin 4, readRegion (rdOf z) (.bld z b) (.pst (rdOf z) q) = true) ∧
    ∀ s, readRegion (rdOf z) (.bld z b) s = true →
      Data.body s = true ∧ pollOff s ≠ 80 ∧ ∀ z', s ≠ .bld z' b := by
  refine ⟨bias_cut z b lz,?_,?_⟩
  · cases z <;> revert b <;> decide +kernel
  · intro s hs
    have lb : ∀ z (b : Fin 16), (Site.sld (rdOf z) 0).pos ≤ (Site.bld z b).pos := by
      intro z; cases z <;> decide +kernel
    obtain ⟨body,off⟩ := region_body (rdOf z) s _ (lb z b) hs
    refine ⟨body,off,?_⟩
    rintro z' rfl
    have no : ∀ z z' (b : Fin 16), readRegion (rdOf z) (.bld z b) (.bld z' b) = false := by
      decide +kernel
    rw [no] at hs
    cases hs

end PTX.Kernels.TmlFa4Fwd.Proof.Values
