-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Epilogue.Control.Machine
public import Kernels.InklingRelDecode.Proof.Lib.RequestSites

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Epilogue
open PTX Control

/-- The epilogue enters with two requests made and makes the third at its `setMax`. -/
def requestPhase : Site → Nat
  | .roleWord | .sync1 | .sync0 | .dealloc | .exit => 3
  | _ => 2

private theorem site_hit (s : Site) : s.pc ∈ Lib.requestPcs ↔ s = .setMax := by
  cases s <;> first | decide | (rename_i j; revert j; decide +kernel)

/-- A continuing epilogue step counts the request. -/
theorem request_next {entry L g d ev dn}
    (hn : Control.next entry L g d ev = some (some dn)) :
    requestPhase dn.site = requestPhase d.site +
      (if d.site.pc ∈ Lib.requestPcs then 1 else 0) := by
  simp only [site_hit]
  obtain ⟨s,v⟩ := d
  cases s <;> simp only [Control.next,firstStore,storeAt] at hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals rfl

end PTX.Kernels.InklingRelDecode.Proof.Epilogue
