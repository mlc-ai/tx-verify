-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.Shape

@[expose] public section

/-! # Event shapes at probability elections and warp barriers -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem shapeAt_pElect (_hp : Pre p L m) (d : D) (hk : d.k = 0)
    (hs : (∃ r, d.site = .pws r) ∨ ∃ r, d.site = .pel r) :
    (code p L g).ShapeAt (Ev p L g) d := by
  obtain ⟨s, v, k, acc⟩ := d
  cases hk
  rcases hs with ⟨r, hs⟩ | ⟨r, hs⟩
  · cases hs
    cases r <;>
      intro t ins e o hat hi hc hf <;>
      obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup)) <;>
      exact shape_warpBar
        (P := fun e => (∃ inst, e.kind = .warpBar 4294967295 inst) ∨ ∃ f, e.kind = .ub f)
        hf (fun inst => .inl ⟨inst, rfl⟩) (fun f => .inr ⟨f, rfl⟩)
  · cases hs
    cases r <;>
      intro t ins e o hat hi hc hf <;>
      obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup)) <;>
      rcases fires_elect_mask (bits := BitVec.ofNat 64 4294967295) rfl hf with
        ⟨inst, ld, rfl⟩ | ⟨f, rfl⟩
    all_goals first
      | exact Or.inl ⟨_, _, rfl, rfl⟩
      | exact Or.inr ⟨_, rfl⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
