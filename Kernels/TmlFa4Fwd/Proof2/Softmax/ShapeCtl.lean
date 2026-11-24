-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Softmax.ShapeCtl1
public import Kernels.TmlFa4Fwd.Proof2.Softmax.ShapeCtl2
public import Kernels.TmlFa4Fwd.Proof2.Softmax.ShapeCtl3
public import Kernels.TmlFa4Fwd.Proof2.Softmax.ShapeCtl4
public import Kernels.TmlFa4Fwd.Proof2.Softmax.ShapeCtl5
public import Kernels.TmlFa4Fwd.Proof2.Softmax.ShapeCtl6
public import Kernels.TmlFa4Fwd.Proof2.Softmax.ShapeCtl7
public import Kernels.TmlFa4Fwd.Proof2.Softmax.ShapeCtl8

@[expose] public section

/-! # The softmax warps' shape table at the control sites

The control sites' families are checked in eight files (`ShapeCtl1` … `ShapeCtl8`) so that they
check in parallel. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {g : Nat}

theorem shapeAt_ctl (hp : Pre p L m) (d : D) (hk : d.k = 0)
    (hs : d.site = .setmax ∨ d.site = .bar1 ∨ d.site = .q0 ∨ d.site = .q1 ∨ d.site = .uk ∨
      d.site = .wq ∨ (∃ r, d.site = .ws r) ∨ (∃ b, d.site = .wb b) ∨ (∃ b, d.site = .fence b) ∨
      (∃ b, d.site = .bsync b) ∨ (∃ b, d.site = .barr b) ∨ (∃ b, d.site = .stat b) ∨
      (∃ r, d.site = .narr r) ∨ (∃ r k, d.site = .pwst r k) ∨ (∃ r, d.site = .parr r) ∨
      (∃ r, d.site = .pws r) ∨ (∃ r, d.site = .pel r) ∨ (∃ r, d.site = .parr2 r) ∨
      (∃ r, d.site = .pwend r) ∨ (∃ k, d.site = .fin k) ∨ d.site = .finarr ∨
      (∃ l, d.site = .wend l) ∨ (∃ l, d.site = .barEnd l) ∨ (∃ l, d.site = .exit l)) :
    (code p L g).ShapeAt (Ev p L g) d := by
  obtain ⟨s, v, k, acc⟩ := d
  simp only at hk hs
  cases s <;>
    first
    | (refine shapeAt_ctl1 hp _ hk ?_; simp; done)
    | (refine shapeAt_ctl2 hp _ hk ?_; simp; done)
    | (refine shapeAt_ctl3 hp _ hk ?_; simp; done)
    | (refine shapeAt_ctl4 hp _ hk ?_; simp; done)
    | (refine shapeAt_ctl5 hp _ hk ?_; simp; done)
    | (refine shapeAt_ctl6 hp _ hk ?_; simp; done)
    | (refine shapeAt_ctl7 hp _ hk ?_; simp; done)
    | (refine shapeAt_ctl8 hp _ hk ?_; simp; done)
    | (simp at hs)

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Softmax
