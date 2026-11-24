-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Shape
import Kernels.TmlFa4Fwd.Flow.Code
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The softmax warps' shape table at the control sites: the named-barrier arrivals

The arrivals at the warp group's named barrier with the correction warps (`narr` per round kind,
`finarr` after the final stores) are proved by hand rather than by `site_shape`: the barrier id
`%r5127` is the table's word `nbW`, read once from the facts, and `shape_barArriveR` takes it
with `nbW_tlt`; `nbW_tval` names the id in the shape table. Through `site_shape`'s alternatives
the three `narr` sites took 941 s and `finarr` most of `ShapeCtl8`'s 390 s (risk R2). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

set_option hygiene false in
/-- The arrival at the named barrier `nbW` with 64 threads. -/
macro "soft_narr" : tactic => `(tactic| (
  intro t ins e o hat hi hc hf
  obtain rfl := Option.some.inj (hc.symm.trans (by code_lookup))
  have hr : t.regs 5127 = some (.bits 32 (nbW L g)) :=
    (PTX.Flow.regs_of_factsFrom hat.2.2.2.2 (by lit_mem)).trans
      (by simp only [valueOf, values, valuesStart, valuesRole, valuesTile, valuesP1, valuesBias,
        valuesPlain, valuesFin, lookupLit, Option.getD_some, Option.getD_none] <;> rfl)
  refine PTX.Flow.shape_barArriveR hf (by simp only [readBits, readReg, hr] <;> rfl)
    (nbW_tlt ‹Pre _ _ _›) (by simp only [readBits] <;> rfl) (by decide) (by decide)
    (by rw [‹Pre _ _ _›.block]; decide) ?_
  all_goals simp only [Ev, nbW_tval ‹Pre _ _ _›, trunc_imm64]))

theorem shapeAt_ctl6 (hp : Pre p L m) (d : D) (hk : d.k = 0)
    (hs : (∃ r, d.site = .narr r) ∨ d.site = .finarr) :
    (code p L g).ShapeAt (Ev p L g) d := by
  obtain ⟨s, v, k, acc⟩ := d
  cases hk
  cases s <;> simp at hs
  · rename_i r
    cases r <;> soft_narr
  · soft_narr

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
