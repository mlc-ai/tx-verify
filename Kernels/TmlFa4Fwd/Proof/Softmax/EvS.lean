-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Shape

@[expose] public section

/-! # The softmax warps' shapes without undefined behaviour -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- **The shape table without undefined behaviour.** -/
abbrev EvS (p : Params) (L : Launch) (g : Nat) (d : D) (e : Event) : Prop :=
  Ev p L g d e ∧ ∀ f, e.kind ≠ .ub f

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
