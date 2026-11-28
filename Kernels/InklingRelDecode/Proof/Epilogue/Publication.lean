-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Control.Machine
public import Kernels.InklingRelDecode.Proof.Lib.BarOne

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue
open PTX Control

/-- The epilogue enters at phase two and publishes the exit word during phase three. -/
def publicationPhase : Site → Nat
  | .setMax | .roleWord | .sync1 => 3
  | .sync0 | .dealloc | .exit => 4
  | _ => 2

private theorem site_hit (s : Site) : s.pc ∈ Lib.barOneSites ↔ s = .join ∨ s = .sync1 := by
  cases s <;> first | decide | (rename_i j; revert j; decide +kernel)

/-- A continuing epilogue step counts the two whole-CTA barriers. -/
theorem publication_next {entry L g d ev dn}
    (hn : Control.next entry L g d ev = some (some dn)) :
    publicationPhase dn.site = publicationPhase d.site +
      (if d.site.pc ∈ Lib.barOneSites then 1 else 0) := by
  simp only [site_hit]
  obtain ⟨s,v⟩ := d
  cases s <;> simp only [Control.next,firstStore,storeAt] at hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals rfl

end PTX.Kernels.InklingRelDecode.Proof.Epilogue
