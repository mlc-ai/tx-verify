-- SPDX-License-Identifier: Apache-2.0
module
public import Kernels.FlashKdaFwd.Packed.ElectionResult
public import Kernels.FlashKdaFwd.Packed.OneTokenInput
public import Kernels.FlashKdaFwd.Packed.OneTokenLaunch

@[expose] public section
namespace FlashKda.Packed
open PTX

theorem one_token_counterexample (base : Nat → Nat → Nat) :
    Workspace.Inputs OneToken.problem OneToken.bases OneToken.memory ∧
    OneToken.launch.Valid kernel ∧
    ¬Correct kernel (Prologue.assumptions base) OneToken.launch OneToken.memory
      (Post OneToken.problem OneToken.memory) := by
  refine ⟨OneToken.inputs,valid_launch _ OneToken.grid_valid rfl,?_⟩
  apply no_correct_single_token base _ _ _ _ OneToken.inputs (by decide) rfl rfl
  · intro a outer d h
    exact OneToken.map_bound h
  · exact OneToken.host_offset
  · rfl
  · rfl
  · rfl
  · rfl
  · exact OneToken.grid_valid

end FlashKda.Packed
