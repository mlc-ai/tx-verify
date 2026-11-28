-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Loader.Machine
import Kernels.InklingRelDecode.Gen.StepLoader
import Lemmas.Flow.Step.SiteCases

@[expose] public section

namespace PTX.Kernels.InklingRelDecode.Proof.Loader
open PTX PTX.Flow PTX.Proof
variable {L : Launch} {g : Nat} {w : Value} {regs : Nat → Value} (i n a b : Value)

theorem first_step : (code L g w regs).StepAt ⟨.first, i, n, a, b⟩ := by
  let start : D := ⟨.first, i, n, a, b⟩
  let finish := fun v => ({start with counter := v, site := .second} : D)
  apply Code.StepAt.of (C := code L g w regs) (d := start)
  · intro _
    exact ⟨_, Flow.code_2345, rfl, trivial⟩
  refine Code.step_ldv_mid (C := code L g w regs) (d := start) (dok := finish)
      Flow.code_2345 rfl rfl rfl (show 1 < 2 by decide) ?_ ?_ (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) ?_ (fun _ _ h => by cases h)
  · intro x bs v hv
    change ((rebuild 3 bs).toOption.bind _) = _
    rw [hv]
    rfl
  · intro x bs f hf
    change ((rebuild 3 bs).toOption.bind _) = _
    rw [hf]
    rfl
  · intro v
    rfl

theorem second_step : (code L g w regs).StepAt ⟨.second, i, n, a, b⟩ := by
  let start : D := ⟨.second, i, n, a, b⟩
  let finish := fun v => ({start with limit := v, site := .beginBar} : D)
  apply Code.StepAt.of (C := code L g w regs) (d := start)
  · intro _
    exact ⟨_, Flow.code_2345, rfl, trivial⟩
  refine Code.step_ldv_last_sel (C := code L g w regs) (d := start)
    (nv := fun v => some (some (finish v))) Flow.code_2345 rfl rfl rfl
    (show ¬ 2 < 2 by decide) (by decide) ?_ ?_ (by simp) ?_
  · intro x bs v hv
    change ((rebuild 3 bs).toOption.bind _) = _
    rw [hv]
    rfl
  · intro x bs f hf
    left
    change ((rebuild 3 bs).toOption.bind _) = _
    rw [hf]
    rfl
  · intro v d' he
    cases he
    refine ⟨fun _ => ⟨0, ?_⟩, rfl, rfl, fun _ h => by cases h⟩
    apply Seg.weaken_end (Seg.refl _ _)
    intro R hr
    have old : Flow.live 2345 = [3,462,463,464,465,466,528,529,530,531,532,534,1949,2020] := by
      decide +kernel
    have new : Flow.live 2346 =
        [3,462,463,464,465,466,467,528,529,530,531,532,534,1905,1949,2020] := by
      decide +kernel
    change Holds R (Code.vecFacts [1905, 467] [i, v] (factsFrom (Flow.live 2345) _)) at hr
    change Holds R (factsFrom (Flow.live 2346) _)
    rw [old] at hr
    rw [new]
    obtain ⟨hi, hn, h3, h462, h463, h464, h465, h466, h528, h529, h530,
      h531, h532, h534, h1949, h2020, _⟩ := hr
    exact ⟨h3, h462, h463, h464, h465, h466, hn, h528, h529, h530, h531, h532,
      h534, hi, h1949, h2020, trivial⟩

end PTX.Kernels.InklingRelDecode.Proof.Loader
