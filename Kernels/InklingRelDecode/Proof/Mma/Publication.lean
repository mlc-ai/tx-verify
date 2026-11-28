-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.Machine
public import Kernels.InklingRelDecode.Proof.Lib.BarOne

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX

/-- Barrier-1 count relative to the start of the current dispatch round. -/
def publicationPhase : Site → Nat
  | .setMaxReg | .ldNum | .bar0 => 1
  | .setMaxRegInc | .dispatch => 3
  | _ => 2

private theorem site_hit (s : Site) : s.pc ∈ Lib.barOneSites ↔ s = .bar0 ∨ s = .bar1 := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

theorem publication_next {L g d ev dn} (hn : next L g d ev = some (some dn)) :
    publicationPhase dn.site = publicationPhase d.site +
      (if d.site.pc ∈ Lib.barOneSites then 1 else 0) := by
  simp only [site_hit]
  obtain ⟨s,i,v⟩ := d
  cases s
  case ldNum =>
    simp only [next] at hn
    split at hn <;> try contradiction
    rename_i bs _
    cases hw : (rebuild 3 bs).toOption <;> simp [hw] at hn
    subst dn
    rfl
  all_goals simp only [next,issueNext,afterQk,iterNext,startSite] at hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals rfl

end PTX.Kernels.InklingRelDecode.Proof.Mma
