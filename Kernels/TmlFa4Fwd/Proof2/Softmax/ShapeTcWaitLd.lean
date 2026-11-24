-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.Shape

@[expose] public section

/-! # Event shapes at the plain score load's wait -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem shapeAt_tc1_ld (_hp : Pre p L m) (d : D) (hk : d.k = 1)
    (hs : ∃ c, d.site = .sldw c) :
    (code p L g).ShapeAt (Ev p L g) d := by
  obtain ⟨c, hs⟩ := hs
  obtain ⟨s, v, k, acc⟩ := d
  cases hk
  cases hs
  fin_cases c <;>
    intro t ins e o hat hi hc hf <;>
    obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup)) <;>
    exact shape_tcLdWait (P := fun e => e.kind = .tc .waitLd ∨ ∃ f, e.kind = .ub f)
      hf (by rw [hat.1, Assumptions.all_tcLdWait]; kernel_rfl)
      (fun h => Nat.succ_ne_zero 0 ((show t.sub = 1 from hat.2.1).symm.trans h))
      (.inl rfl) (fun f => .inr ⟨f, rfl⟩)

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
