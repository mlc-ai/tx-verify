-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBBK
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.RunLand
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBBE2
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBBE3
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBBI
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBBL2
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBBS
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBBS2
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBBS3
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBBS4
import Tactics.KernelRfl
import Kernels.TmlFa4Fwd.Gen.StepSoftmax

@[expose] public section

/-! # The bias round's exponents: the software path as one segment

The nine runs (their conditions by the kind chains) and the eight software `exp2` instances
(`instB<k>`, lane kinds from the previous run's end kinds, `laneK<k>`) composed: from the start
facts of run 0 (values `W` of the kinds `bK0`) at pc 5977 to the end facts of run 8 at pc 6299. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.TmlFa4Fwd

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

variable {L : Launch} {g : Nat}

/-- **The software path.** -/
theorem expoBB_seg (W : Nat → Value)
    (k0 : ∀ r, (kOf bK0 r).Has (lookupD (Gen.expoBB0_facts0 W) r)) :
    ∃ n, Seg kernel Assumptions.all L g n 5977 (Gen.expoBB0_facts0 W) 6299
      (Gen.expoBB8_facts1 (vB8 W)) := by
  have e0 := expoBB0_chain (vB0 W) k0
  have e1 := expoBB1_chain (vB1 W) (k0_1 W e0.2)
  have e2 := expoBB2_chain (vB2 W) (k0_2 W e1.2)
  have e3 := expoBB3_chain (vB3 W) (k0_3 W e2.2)
  have e4 := expoBB4_chain (vB4 W) (k0_4 W e3.2)
  have e5 := expoBB5_chain (vB5 W) (k0_5 W e4.2)
  have e6 := expoBB6_chain (vB6 W) (k0_6 W e5.2)
  have e7 := expoBB7_chain (vB7 W) (k0_7 W e6.2)
  have e8 := expoBB8_chain (vB8 W) (k0_8 W e7.2)
  obtain ⟨_, r0⟩ := seg_of_segD (L := L) (g := g) (Gen.expoBB0_run L g (vB0 W)) e0.1
  rw [expoBB0_end_eq] at r0
  obtain ⟨_, r1⟩ := seg_of_segD (L := L) (g := g) (Gen.expoBB1_run L g (vB1 W)) e1.1
  rw [expoBB1_end_eq] at r1
  obtain ⟨_, r2⟩ := seg_of_segD (L := L) (g := g) (Gen.expoBB2_run L g (vB2 W)) e2.1
  rw [expoBB2_end_eq] at r2
  obtain ⟨_, r3⟩ := seg_of_segD (L := L) (g := g) (Gen.expoBB3_run L g (vB3 W)) e3.1
  rw [expoBB3_end_eq] at r3
  obtain ⟨_, r4⟩ := seg_of_segD (L := L) (g := g) (Gen.expoBB4_run L g (vB4 W)) e4.1
  rw [expoBB4_end_eq] at r4
  obtain ⟨_, r5⟩ := seg_of_segD (L := L) (g := g) (Gen.expoBB5_run L g (vB5 W)) e5.1
  rw [expoBB5_end_eq] at r5
  obtain ⟨_, r6⟩ := seg_of_segD (L := L) (g := g) (Gen.expoBB6_run L g (vB6 W)) e6.1
  rw [expoBB6_end_eq] at r6
  obtain ⟨_, r7⟩ := seg_of_segD (L := L) (g := g) (Gen.expoBB7_run L g (vB7 W)) e7.1
  rw [expoBB7_end_eq] at r7
  obtain ⟨_, r8⟩ := seg_of_segD (L := L) (g := g) (Gen.expoBB8_run L g (vB8 W)) e8.1
  obtain ⟨_, i0⟩ := instB0 (L := L) (g := g) (vB0 W)
    (ni_of_kLeNi (e0.2 1407) laneK0.1) (ni_of_kLeNi (e0.2 1408) laneK0.2)
  obtain ⟨_, i1⟩ := instB1 (L := L) (g := g) (vB1 W) (by kernel_rfl)
    (ni_of_kLeNi (e1.2 1409) laneK1.1) (ni_of_kLeNi (e1.2 1410) laneK1.2)
  obtain ⟨_, i2⟩ := instB2 (L := L) (g := g) (vB2 W) (by kernel_rfl)
    (ni_of_kLeNi (e2.2 1423) laneK2.1) (ni_of_kLeNi (e2.2 1424) laneK2.2)
  obtain ⟨_, i3⟩ := instB3 (L := L) (g := g) (vB3 W) (by kernel_rfl)
    (ni_of_kLeNi (e3.2 1425) laneK3.1) (ni_of_kLeNi (e3.2 1426) laneK3.2)
  obtain ⟨_, i4⟩ := instB4 (L := L) (g := g) (vB4 W) (by kernel_rfl)
    (ni_of_kLeNi (e4.2 1439) laneK4.1) (ni_of_kLeNi (e4.2 1440) laneK4.2)
  obtain ⟨_, i5⟩ := instB5 (L := L) (g := g) (vB5 W) (by kernel_rfl)
    (ni_of_kLeNi (e5.2 1441) laneK5.1) (ni_of_kLeNi (e5.2 1442) laneK5.2)
  obtain ⟨_, i6⟩ := instB6 (L := L) (g := g) (vB6 W) (by kernel_rfl)
    (ni_of_kLeNi (e6.2 1455) laneK6.1) (ni_of_kLeNi (e6.2 1456) laneK6.2)
  obtain ⟨_, i7⟩ := instB7 (L := L) (g := g) (vB7 W) (by kernel_rfl)
    (ni_of_kLeNi (e7.2 1457) laneK7.1) (ni_of_kLeNi (e7.2 1458) laneK7.2)
  have c0 := (r0.comp i0).comp r1
  have c1 := (c0.comp i1).comp r2
  have c2 := (c1.comp i2).comp r3
  have c3 := (c2.comp i3).comp r4
  have c4 := (c3.comp i4).comp r5
  have c5 := (c4.comp i5).comp r6
  have c6 := (c5.comp i6).comp r7
  have c7 := (c6.comp i7).comp r8
  exact ⟨_, c7⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
