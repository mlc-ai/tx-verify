-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.Machine
import Kernels.InklingRelDecode.Gen.StepMma
import Lemmas.Flow.Step.SiteCases

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Flow PTX.Proof

/-- A successful read carries the exact returned value through the named barrier. -/
theorem iter_read_step {L : Launch} {g : Nat} {w : Value} {regs : Nat → Value}
    (i : Nat) (v : Value) : (code L g regs w).StepAt ⟨.ldNum,i,v⟩ := by
  let start : D := ⟨.ldNum,i,v⟩
  let finish := fun val => ({start with word := val, site := .bar0} : D)
  apply Code.StepAt.of (C := code L g regs w) (d := start)
  · exact fun _ => ⟨_, Flow.code_2423, rfl, trivial⟩
  refine Code.step_ldv_last_sel (C := code L g regs w) (d := start)
    (nv := fun val => some (some (finish val))) Flow.code_2423 rfl rfl rfl
    (show ¬ 0 + 1 < 1 by decide) (by decide) ?_ ?_ (by simp) ?_
  · intro x bs val hv
    change ((rebuild 3 bs).toOption.bind _) = _
    rw [hv]
    rfl
  · intro x bs f hf
    left
    change ((rebuild 3 bs).toOption.bind _) = _
    rw [hf]
    rfl
  · intro val d' he
    cases he
    refine ⟨fun _ => ⟨0, ?_⟩, rfl, rfl, fun hi => hi⟩
    apply Seg.weaken_end (Seg.refl _ _)
    intro R hr
    change Holds R (Code.vecFacts [471] [val] (factsFrom (Flow.live 2423) _)) at hr
    change Holds R (factsFrom (Flow.live 2424) _)
    obtain ⟨hv,h3,h462,h463,h464,h465,h466,h528,h529,h530,h531,h532,h534,h1949,h2020,_⟩ := hr
    exact ⟨h3,h462,h463,h464,h465,h466,hv,h528,h529,h530,h531,h532,h534,h1949,h2020,trivial⟩

end PTX.Kernels.InklingRelDecode.Proof.Mma
