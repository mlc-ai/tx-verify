-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Softmax.Control.Machine

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
open PTX PTX.Flow Control

set_option maxRecDepth 10000 in
/-- The mandatory rendezvous follows a skipped decision, the store wait, or the setup. -/
public theorem pred_bar20 {ent L g ev} {d dn : D}
    (step : Control.next ent L g d ev=some (some dn)) (site : dn.site=.bar20) :
    (d.site=.shfl12 ∧ ∃ m sent b c recv ok, ev.kind=.shfl m sent b c recv ok ∧
      skipRescale L g sent recv=true) ∨ d.site=.waitStO ∨ (d.site=.shfl6 ∧ dn.i=0) := by
  obtain ⟨s,i,v⟩ := d
  cases s <;> simp only [Control.next,advance,loopSite] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals first | (simp at site; done) | exact .inr (.inr ⟨rfl,‹_›⟩) | exact .inr (.inl rfl) |
    exact .inl ⟨rfl,_,_,_,_,_,_,by assumption,by simpa using ‹skipRescale _ _ _ _ = true›⟩

set_option maxRecDepth 10000 in
/-- The P store follows the rendezvous, in one round. -/
public theorem pred_tmemSt {ent L g ev} {d dn : D}
    (step : Control.next ent L g d ev=some (some dn)) (site : dn.site=.tmemSt) :
    d.site=.bar20 ∧ d.i=dn.i := by
  obtain ⟨s,i,v⟩ := d
  cases s <;> simp only [Control.next,advance,loopSite] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals first | (simp at site; done) | exact ⟨rfl,rfl⟩

set_option maxRecDepth 10000 in
public theorem pred_stO {ent L g ev} {d dn : D}
    (step : Control.next ent L g d ev=some (some dn)) (site : dn.site=.stO) :
    d.site=.bar24 := by
  obtain ⟨s,i,v⟩ := d
  cases s <;> simp only [Control.next,advance,loopSite] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals first | (simp at site; done) | rfl

set_option maxRecDepth 10000 in
public theorem pred_waitStO {ent L g ev} {d dn : D}
    (step : Control.next ent L g d ev=some (some dn)) (site : dn.site=.waitStO) :
    d.site=.stO := by
  obtain ⟨s,i,v⟩ := d
  cases s <;> simp only [Control.next,advance,loopSite] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals first | (simp at site; done) | rfl

end PTX.Kernels.InklingRelDecode.Proof.Softmax.Export
