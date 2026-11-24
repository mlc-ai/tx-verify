-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Shape
import Kernels.TmlFa4Fwd.Flow.Code
import Lemmas.Flow.Step.ShapeAsync
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader warps' events by state: the rows of the steady period's packets

The shuffles of each row's address words (`load_shape`) and its two `cp.async` copies
(`load_cp`), in the K and V packets (`Shape.lean`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

variable {p : Params} {L : Launch} {m : Mem0} {g w : Nat} {ent : Nat → Value}

theorem shapeAt_shflSteady (hp : Pre p L m) (d : D) (hk : d.k = 0)
    (hs : (∃ b i, d.site = .xl .steady b i) ∨ ∃ b i, d.site = .xh .steady b i) :
    (code p L g w ent).ShapeAt (Ev p L g w) d := by
  obtain ⟨s, v, k⟩ := d
  cases hk
  load_shape

theorem shapeAt_cpSteady (hp : Pre p L m) (d : D) (hk : d.k = 0)
    (hs : ∃ b i c, d.site = .cp .steady b i c) :
    (code p L g w ent).ShapeAt (Ev p L g w) d := by
  obtain ⟨s, v, k⟩ := d
  cases hk
  obtain ⟨b, i, c, hs⟩ := hs
  cases hs
  cases b <;> fin_cases i <;> fin_cases c <;> load_cp

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
