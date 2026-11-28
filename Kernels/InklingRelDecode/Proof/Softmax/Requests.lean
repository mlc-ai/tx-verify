-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Softmax.Control.Machine
public import Kernels.InklingRelDecode.Proof.Lib.RequestSites

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax
open PTX Control

/-- Requests before a state: the prologue's, then this role's own at its entry. -/
def requestPhase : Site → Nat
  | .setMaxReg => 1
  | _ => 2

private theorem site_hit (s : Site) : s.pc ∈ Lib.requestPcs ↔ s = .setMaxReg := by
  cases s <;> first | decide | (rename_i j; revert j; decide +kernel)

/-- A continuing softmax step counts the request of its entry. -/
theorem request_next {entry L g d ev dn}
    (hn : Control.next entry L g d ev = some (some dn)) :
    requestPhase dn.site = requestPhase d.site +
      (if d.site.pc ∈ Lib.requestPcs then 1 else 0) := by
  simp only [site_hit]
  obtain ⟨s,i,v⟩ := d
  cases s <;> simp only [Control.next,advance,loopSite] at hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals rfl

end PTX.Kernels.InklingRelDecode.Proof.Softmax
