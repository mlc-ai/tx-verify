-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Machine

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.SmWarp
open PTX.Flow Softmax.Control

/-- The control fragment carries the warp bound established at dispatch. -/
@[reducible] noncomputable def control (p : Params) (L : Launch) (g : Nat) :
    Code kernel Assumptions.all L g :=
  { Softmax.Control.code p L g with inv := fun d => Inv d ∧ g % L.block / 32 < 8 }

theorem control_step {p L g d}
    (h : g % L.block / 32 < 8 → (Softmax.Control.code p L g).StepAtU d) :
    (control p L g).StepAtU d where
  site := fun ⟨hi,hw⟩ => (h hw).site hi
  step := by
    intro t e u ins hat hi hc hf
    rcases (h hi.2).step ins hat hi.1 hc hf with (hn | ⟨d',t',hn,ht,hg⟩) | hd
    · exact .inl (.inl hn)
    · refine .inl (.inr ⟨d',t',hn,ht,?_⟩)
      rcases hg with ⟨hat',hi'⟩ | hu
      · exact .inl ⟨hat',hi',hi.2⟩
      · exact .inr hu
    · exact .inr hd

end PTX.Kernels.TmlFa4Fwd.Proof.SmWarp
