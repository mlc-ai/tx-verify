-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.Machine
public import Kernels.InklingRelDecode.Proof.Lib.RequestSites
import Kernels.InklingRelDecode.Proof.Loader.RefNext

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX

/-- Requests relative to the start of the current dispatch round, which has made the head's. -/
def requestPhase : Site → Nat
  | .dec => 1
  | .inc => 2
  | .dispatch => 3
  | _ => 2

private theorem site_hit (s : Site) :
    s.pc ∈ Lib.requestPcs ↔ s = .dec ∨ s = .inc ∨ s = .dispatch := by
  cases s <;> repeat' first | decide +kernel | (rename_i j; revert j)

theorem request_next {L g d ev dn} (step : next L g d ev = some (some dn)) :
    requestPhase dn.site = requestPhase d.site +
      (if d.site.pc ∈ Lib.requestPcs then 1 else 0) := by
  simp only [site_hit]
  obtain ⟨s,c,l,p,q⟩ := d
  cases s
  case first | second =>
    obtain ⟨_,_,_,_,_,rfl⟩ := read_next step
    rfl
  case page b =>
    cases b <;> obtain ⟨_,_,_,_,_,rfl⟩ := read_next step <;> rfl
  case copy j b =>
    cases b <;> simp only [next,finishPair] at step
    all_goals repeat' split at step
    all_goals cases step
    all_goals rfl
  all_goals simp only [next,finishPair] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals rfl

end PTX.Kernels.InklingRelDecode.Proof.Loader
