-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Dispatch.Machine

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Dispatch
open PTX PTX.Flow PTX.Proof

theorem inv_next {L g d dn ev} (step : next L g d ev=some (some dn)) :
    dn.site=.exitDealloc → g%L.block<32 := by
  obtain ⟨s,r⟩ := d
  cases s
  case read =>
    simp only [next] at step
    split at step <;> try contradiction
    obtain ⟨dest,h,eq⟩ := Option.map_eq_some_iff.mp step
    cases eq
    unfold readTarget at h
    rename_i bs _
    cases h₁ : (rebuild 3 bs).toOption with
    | none => simp [h₁] at h
    | some v =>
      cases h₂ : (extendLoaded (.zero 32) 8 v).toOption with
      | none => simp [h₁,h₂] at h
      | some x =>
        simp [h₁,h₂] at h
        split at h <;> try contradiction
        cases h
        change target _=.exitDealloc → _
        unfold target
        split <;> nofun
  all_goals simp only [next] at step
  all_goals repeat' split at step
  all_goals cases step
  all_goals simp_all

end PTX.Kernels.InklingRelDecode.Proof.Dispatch
