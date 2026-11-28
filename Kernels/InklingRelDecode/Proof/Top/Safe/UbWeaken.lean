-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.UbPrefix

@[expose] public section

/-! # Consumers derive the weaker forms from the global hypothesis -/

namespace PTX.Kernels.InklingRelDecode.Proof
open PTX

theorem NoUbOutside.of_noUb {L : Launch} {X : Execution} (h : ¬HasUb X) : NoUbOutside L X :=
  fun _ _ _ _ he => absurd ⟨_,_,_,he⟩ h

theorem NoUbBefore.of_noUb {X : Execution} (h : ¬HasUb X) (g k : Nat) : Frame.NoUbBefore X g k := by
  rintro j _ ⟨pc,kd⟩ he f rfl
  exact h ⟨_,_,_,he⟩

theorem NoUbLane.of_noUb {X : Execution} (h : ¬HasUb X) (g : Nat) : NoUbLane X g :=
  NoUbBefore.of_noUb h g _

end PTX.Kernels.InklingRelDecode.Proof
