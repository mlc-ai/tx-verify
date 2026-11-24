-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Assumptions
public import Lemmas.Flow.HavocSegment
import Kernels.TmlFa4Fwd.Proof.Softmax.GenRules

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Proof.KernelHavoc
open PTX.Assumption PTX.Flow PTX.Proof

/-- Only software-exponent instances override a stretch of the frozen kernel. -/
noncomputable def hooks (pc : Nat) : Option Havoc.Hook :=
  if Assumptions.swExp2Sites.contains pc then
    (cuteExp2.matchAt kernel pc).map Havoc.ofMatch
  else none

theorem hooks_ok {L : Launch} {g : Nat} : Havoc.Hooks Assumptions.all L g hooks := by
  intro t a u hsub hacc ha hr
  simp only [Assumptions.all, Assumptions.numeric, Assumptions.synchronization, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  on_goal 5 =>
    change (if _ then (cuteExp2.matchAt kernel t.pc).map (fun m => Assumptions.execSwExp2 m t)
      else none) = some (.ok u) at hr
    split at hr
    · rename_i h
      obtain ⟨m, hm, hex⟩ := Option.map_eq_some_iff.mp hr
      obtain ⟨hp, hs, ha, hf, _, hregs⟩ := Havoc.execSegmentLane_frame
        (lane := Assumptions.swExp2Lane) (m := m) (t := t) hex
      exact ⟨Havoc.ofMatch m, by simp only [hooks, h.1, ↓reduceIte, hm, Option.map_some],
        hp, hs, ha, hf, hregs⟩
    · cases hr
  all_goals cases hr

theorem rules_frame : RulesFrame Assumptions.all := Softmax.Gen.rulesFrame

end PTX.Kernels.TmlFa4Fwd.Proof.KernelHavoc
