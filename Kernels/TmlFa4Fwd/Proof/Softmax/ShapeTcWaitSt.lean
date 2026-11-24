-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Shape
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Assumptions.Transparency
import Kernels.TmlFa4Fwd.Proof.Softmax.Base
import Kernels.TmlFa4Fwd.Proof.Softmax.ShapeTcProof
import Tactics.KernelRfl

@[expose] public section

/-! # Event shapes after a P store's implicit wait -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem shapeAt_tc1_st (_hp : Pre p L m) (d : D) (hk : d.k = 1)
    (hs : d.site = .pst .first 0 ∨ d.site = .pst .bias 0) :
    (code p L g).ShapeAt (Ev p L g) d := by
  obtain ⟨s, v, k, acc⟩ := d
  cases hk
  rcases hs with hs | hs <;> cases hs
  all_goals
    intro t ins e o hat hi hc hf
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
    exact shape_tcStStore
      (P := fun e => (∃ a vals sh, e.kind = .tc (.st a vals sh)) ∨ ∃ f, e.kind = .ub f)
      hf (by rw [hat.1, Assumptions.all_tcStWaitLd]; kernel_rfl)
      (fun h => Nat.succ_ne_zero 0 ((show t.sub = 1 from hat.2.1).symm.trans h)) (by tm_reg)
      (by with_reducible exact or32_lt _ _)
      (fun a vals => .inl ⟨a, vals, _, rfl⟩) (fun f => .inr ⟨f, rfl⟩)

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
