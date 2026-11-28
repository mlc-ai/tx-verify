-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Dispatch.Machine
public import Kernels.InklingRelDecode.Proof.Lib.ExitPC

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Dispatch
open PTX

private theorem target_post (n) : Lib.afterFinal (target n).pc = 0 := by
  unfold target
  split <;> rfl

private theorem read_post {bs s} (h : readTarget bs = some s) : Lib.afterFinal s.pc = 0 := by
  unfold readTarget at h
  cases hr : (rebuild 3 bs).toOption with
  | none => simp [hr] at h
  | some v =>
    cases hx : (extendLoaded (.zero 32) 8 v).toOption with
    | none => simp [hr,hx] at h
    | some x =>
      simp [hr,hx] at h
      split at h <;> try contradiction
      cases h
      exact target_post _

theorem final_step {L g d ev dn} (hn : next L g d ev = some (some dn)) :
    Lib.afterFinal dn.site.pc = Lib.afterFinal d.site.pc + (Lib.finalSync d.site.pc).toNat := by
  obtain ⟨s,r⟩ := d
  cases s
  case read =>
    simp only [next] at hn
    split at hn <;> try contradiction
    rename_i bs _
    cases hr : readTarget bs with
    | none => simp [hr] at hn
    | some dest =>
      simp only [hr,Option.map_some,Option.some.injEq] at hn
      subst dn
      exact read_post hr
  all_goals simp only [next] at hn
  all_goals repeat' split at hn
  all_goals cases hn
  all_goals rfl

end PTX.Kernels.InklingRelDecode.Proof.Dispatch
