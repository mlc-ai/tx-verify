-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.Machine
public import Kernels.InklingRelDecode.Proof.Lib.BarOne
import Kernels.InklingRelDecode.Proof.Loader.RefNext

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX

/-- Barrier-1 count relative to the start of the current dispatch round. -/
def publicationPhase : Site → Nat
  | .dec | .first | .second | .beginBar => 1
  | .inc | .dispatch => 3
  | _ => 2

private theorem site_hit (s : Site) : s.pc ∈ Lib.barOneSites ↔ s = .beginBar ∨ s = .endBar := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

theorem publication_next {L g d ev dn} (hn : next L g d ev = some (some dn)) :
    publicationPhase dn.site = publicationPhase d.site +
      (if d.site.pc ∈ Lib.barOneSites then 1 else 0) := by
  simp only [site_hit]
  obtain ⟨s,c,l,p,q⟩ := d
  cases s
  case first | second =>
    obtain ⟨_,_,_,_,_,rfl⟩ := read_next hn
    rfl
  case page b =>
    cases b <;> obtain ⟨_,_,_,_,_,rfl⟩ := read_next hn <;> rfl
  case copy j b =>
    cases b <;> simp only [next,finishPair] at hn
    all_goals repeat' split at hn
    all_goals cases hn
    all_goals rfl
  all_goals simp only [next,finishPair] at hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals rfl

end PTX.Kernels.InklingRelDecode.Proof.Loader
