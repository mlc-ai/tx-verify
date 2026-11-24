-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Loader.Shape
import Kernels.TmlFa4Fwd.Flow.Code
import Lemmas.Flow.Step.ShapeAsync
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The loader warps' events by state: all sites but the packets' rows

The scheduler, the drain, the page and pointer rounds, the address loads, the packets' ends and
the TMA groups.

`site_shape` over the families of sites named in each theorem (`load_shape`, `Shape.lean`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Loader
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

variable {p : Params} {L : Launch} {m : Mem0} {g w : Nat} {ent : Nat → Value}

theorem shapeAt_sched (hp : Pre p L m) (d : D) (hk : d.k = 0)
    (hs : d.site = .setmax ∨ (∃ k, d.site = .word k) ∨ (∃ k, d.site = .down k) ∨
      (∃ k j, d.site = .up k j) ∨ (∃ k, d.site = .total k) ∨ (∃ l, d.site = .vote l) ∨
      (∃ l, d.site = .pre l) ∨ (∃ l, d.site = .tiles l) ∨ d.site = .q0 ∨ d.site = .q1 ∨
      d.site = .uk ∨ d.site = .exit) :
    (code p L g w ent).ShapeAt (Ev p L g w) d := by
  obtain ⟨s, v, k⟩ := d
  cases hk
  load_shape

theorem shapeAt_drain (hp : Pre p L m) (d : D) (hk : d.k = 0)
    (hs : (∃ k, d.site = .dw k) ∨ d.site = .dq ∨ d.site = .de ∨ d.site = .da) :
    (code p L g w ent).ShapeAt (Ev p L g w) d := by
  obtain ⟨s, v, k⟩ := d
  cases hk
  load_shape

theorem shapeAt_pg (hp : Pre p L m) (d : D) (hk : d.k = 0)
    (hs : (∃ per it, d.site = .pgLd per it) ∨ (∃ per it, d.site = .pgSt per it) ∨
      ∃ per it, d.site = .rwSt per it) :
    (code p L g w ent).ShapeAt (Ev p L g w) d := by
  obtain ⟨s, v, k⟩ := d
  cases hk
  load_shape

theorem shapeAt_pt (hp : Pre p L m) (d : D) (hk : d.k = 0)
    (hs : (∃ per b, d.site = .slot per b) ∨ (∃ per b it, d.site = .ptP per b it) ∨
      (∃ per b it, d.site = .ptR per b it) ∨ ∃ per b it, d.site = .ptS per b it) :
    (code p L g w ent).ShapeAt (Ev p L g w) d := by
  obtain ⟨s, v, k⟩ := d
  cases hk
  load_shape

theorem shapeAt_lw (hp : Pre p L m) (d : D)
    (hs : ∃ per b h, d.site = .lw per b h) :
    (code p L g w ent).ShapeAt (Ev p L g w) d := by
  obtain ⟨s, v, k⟩ := d
  load_shape

theorem shapeAt_end (hp : Pre p L m) (d : D) (hk : d.k = 0)
    (hs : (∃ per b, d.site = .commit per b) ∨ ∃ per b, d.site = .arrive per b) :
    (code p L g w ent).ShapeAt (Ev p L g w) d := by
  obtain ⟨s, v, k⟩ := d
  cases hk
  load_shape

theorem shapeAt_tma (hp : Pre p L m) (d : D) (hk : d.k = 0)
    (hs : (∃ t, d.site = .tw t) ∨ (∃ t e, d.site = .te t e) ∨ ∃ t, d.site = .ta t) :
    (code p L g w ent).ShapeAt (Ev p L g w) d := by
  obtain ⟨s, v, k⟩ := d
  cases hk
  load_shape

theorem shapeAt_tc (hp : Pre p L m) (d : D) (hk : d.k = 0) (hs : ∃ t c, d.site = .tc t c) :
    (code p L g w ent).ShapeAt (Ev p L g w) d := by
  obtain ⟨s, v, k⟩ := d
  cases hk
  obtain ⟨t, c, hs⟩ := hs
  cases hs
  fin_cases t <;> fin_cases c <;> load_with PTX.Flow.shape_cpTensorAt

end
end PTX.Kernels.TmlFa4Fwd.Proof.Loader
