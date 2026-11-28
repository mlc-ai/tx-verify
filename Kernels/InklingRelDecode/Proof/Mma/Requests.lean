-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.Machine
public import Kernels.InklingRelDecode.Proof.Lib.RequestSites

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX

/-- Requests relative to the start of the current dispatch round, which has made the head's. -/
def requestPhase : Site → Nat
  | .setMaxReg => 1
  | .setMaxRegInc => 2
  | .dispatch => 3
  | _ => 2

private theorem site_hit (s : Site) : s.pc ∈ Lib.requestPcs ↔
    s = .setMaxReg ∨ s = .setMaxRegInc ∨ s = .dispatch := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

theorem request_next {L g d ev dn} (step : next L g d ev = some (some dn)) :
    requestPhase dn.site = requestPhase d.site +
      (if d.site.pc ∈ Lib.requestPcs then 1 else 0) := by
  simp only [site_hit]
  obtain ⟨s,i,v⟩ := d
  cases s
  case ldNum =>
    simp only [next] at step
    split at step <;> try contradiction
    rename_i bs _
    cases hw : (rebuild 3 bs).toOption <;> simp [hw] at step
    subst dn
    rfl
  all_goals simp only [next,issueNext,afterQk,iterNext,startSite] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals rfl

end PTX.Kernels.InklingRelDecode.Proof.Mma
