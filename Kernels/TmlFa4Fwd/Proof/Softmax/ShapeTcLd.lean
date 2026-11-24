-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Shape
import Kernels.TmlFa4Fwd.Assumptions.Transparency
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Common.LdWait
import Kernels.TmlFa4Fwd.Proof.Softmax.Base
import Kernels.TmlFa4Fwd.Proof.Softmax.ShapeTcProof
import Std.Tactic.BVDecide.Normalize.Prop
import Tactics.KernelRfl

@[expose] public section

/-! # Event shapes at score-load instructions -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem shapeAt_tc0_ld (_hp : Pre p L m) (d : D) (hk : d.k = 0)
    (hs : (∃ r c, d.site = .sld r c) ∨ ∃ c, d.site = .sldw c) :
    (code p L g).ShapeAt (Ev p L g) d := by
  obtain ⟨s, v, k, acc⟩ := d
  cases hk
  rcases hs with ⟨r, c, hs⟩ | ⟨c, hs⟩
  · cases hs
    cases r
    case first | bias =>
      all_goals fin_cases c
      all_goals
        intro t ins e o hat hi hc hf
        obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
        exact shape_tcLd (P := tcLdOrUb) hf (by intro s hs; cases hs)
          (by rw [hat.1]; ld_wait)
          (fun a vals => .inl ⟨a, vals, _, rfl⟩) (fun f => .inr ⟨f, rfl⟩)
    case plain =>
      fin_cases c
      all_goals
        intro t ins e o hat hi hc hf
        obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
        exact shape_tcLdLoad (P := tcLdOrUb) hf (by intro s hs; cases hs)
          (by rw [hat.1]; ld_wait)
          (hat.2.1.trans rfl) (by tm_reg)
          (by with_reducible exact or32_lt _ _)
          (fun a vals => .inl ⟨a, vals, _, rfl⟩) (fun f => .inr ⟨f, rfl⟩)
  · cases hs
    exact shapeAt_junk (by simp [Site.first, Site.midOk])

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
