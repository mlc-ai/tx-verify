-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Control.Machine
public import Kernels.InklingRelDecode.Proof.Lib.BarOne

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax
open PTX Control

/-- The prologue has already published the count pair on entry. The second
rendezvous at pc 575 lets the reduction reuse its bytes at pc 2250. -/
def publicationPhase : Site → Nat
  | .setMaxReg | .bar0 => 1
  | _ => 2

private theorem site_hit (s : Site) : s.pc ∈ Lib.barOneSites ↔ s = .bar0 := by
  cases s <;> first | decide | (rename_i j; revert j; decide +kernel)

/-- A continuing softmax step increments the publication phase exactly once. -/
theorem publication_next {entry L g d ev dn}
    (hn : Control.next entry L g d ev = some (some dn)) :
    publicationPhase dn.site = publicationPhase d.site +
      (if d.site.pc ∈ Lib.barOneSites then 1 else 0) := by
  simp only [site_hit]
  obtain ⟨s,i,v⟩ := d
  cases s <;> simp only [Control.next,advance,loopSite] at hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals rfl

end PTX.Kernels.InklingRelDecode.Proof.Softmax
