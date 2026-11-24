-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Rings
public import Lemmas.Protocol.RingSlot

@[expose] public section

/-! # The cluster launch control response as a ring slot

One slot per cluster. The producer is the leader CTA's scheduler (warp 10, the selector of
consumer 2), polling the acknowledgement barrier; its cancellation request completes on the response
barrier of both CTAs. The ten consumers are, per CTA, its loader (warp 11) and its scheduler, the
leader CTA's two MMA warps (8 and 9), and per CTA the first threads of the two consumer warpgroups
(warps 0 and 4, lane 0). Consumer `b` polls the response barrier of its CTA (`owner b`) and
acknowledges each response it observed by one arrival of its own on the acknowledgement
barrier (`selectedArrival`). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.ClcRing
open PTX MBarrier AsyncCopy

noncomputable section

/-- Consumer `b`'s CTA within the cluster. -/
def ctaOf (b : Fin 10) : Nat := [0, 1, 0, 1, 0, 0, 0, 0, 1, 1].getD b.val 0

/-- Consumer `b`'s warp. -/
def warpOf (b : Fin 10) : Nat := [11, 11, 10, 10, 8, 9, 0, 4, 0, 4].getD b.val 0

/-- Whether consumer `b` is lane 0 of its warp rather than the warp's elected lane. -/
def laneZero (b : Fin 10) : Bool :=
  [false, false, false, false, false, false, true, true, true, true].getD b.val false

theorem ctaOf_lt : ∀ b, ctaOf b < 2 := by decide

/-- Consumers differ in CTA or warp. -/
theorem ctaOf_warpOf_inj : ∀ b q, ctaOf b = ctaOf q → warpOf b = warpOf q → b = q := by decide

/-- The threads of consumer `b`'s selector. -/
def consumerSel (L : Launch) (cluster : Nat) (b : Fin 10) (g : Nat) : Bool :=
  decide (g / L.block = 2 * cluster + ctaOf b ∧ g % L.block / 32 = warpOf b ∧
    (laneZero b = true → g % 32 = 0))

/-- An arrival of a thread of a selector. -/
def selectedArrival (sel : Nat → Bool) (r : Record Ref) : Bool :=
  match r.id, r.action with
  | .thread i, .arrive _ _ => sel i.1
  | _, _ => false

/-- The slot of cluster `cluster`. -/
def slot (L : Launch) (cluster : Nat) : MbarRing.RingSlot 1 10 2 where
  full k := Bar.loc L (2 * cluster + k.val) ⟨.clc, 0, true⟩
  empty _ := Bar.loc L (2 * cluster) ⟨.clc, 0, false⟩
  owner b := ⟨ctaOf b, ctaOf_lt b⟩
  producer _ := consumerSel L cluster 2
  consumer := consumerSel L cluster
  notification _ b := selectedArrival (consumerSel L cluster b)

/-- Different consumers select different threads. -/
theorem consumerSel_disjoint {L : Launch} {cluster : Nat} {b q : Fin 10}
    {g : Nat} (hg : consumerSel L cluster b g = true) (hq : consumerSel L cluster q g = true) :
    b = q := by
  simp only [consumerSel, decide_eq_true_eq] at hg hq
  exact ctaOf_warpOf_inj b q (by omega) (hg.2.1.symm.trans hq.2.1)

end
end PTX.Kernels.Fp16Gemm8192.Proof.ClcRing
