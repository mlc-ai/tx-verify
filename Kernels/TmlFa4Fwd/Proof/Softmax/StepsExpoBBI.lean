-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBBK
import Kernels.TmlFa4Fwd.Flow.Code
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBBE1
import Kernels.TmlFa4Fwd.Proof.Softmax.StepsExpoBBE2
import Kernels.TmlFa4Fwd.Gen.StepSoftmax

@[expose] public section

/-! # The bias round's exponents: the software path as one segment

The nine runs (their conditions by the kind chains) and the eight software `exp2` instances
(`seg_swExp2`, lane kinds from the previous run's end kinds) composed: from the start facts of
run 0 (values `W` of the kinds `bK0`) at pc 5977 to the end facts of run 8 at pc 6299. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow PTX.Assumption PTX.Kernels.TmlFa4Fwd

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

/-- The key lists of the runs' end and start facts. -/
abbrev eKeys0 : List Nat := (Gen.expoBB0_facts3 fun _ => .pred false).map Prod.fst
abbrev eKeys1 : List Nat := (Gen.expoBB1_facts1 fun _ => .pred false).map Prod.fst
abbrev eKeys2 : List Nat := (Gen.expoBB2_facts1 fun _ => .pred false).map Prod.fst
abbrev eKeys3 : List Nat := (Gen.expoBB3_facts1 fun _ => .pred false).map Prod.fst
abbrev eKeys4 : List Nat := (Gen.expoBB4_facts1 fun _ => .pred false).map Prod.fst
abbrev eKeys5 : List Nat := (Gen.expoBB5_facts1 fun _ => .pred false).map Prod.fst
abbrev eKeys6 : List Nat := (Gen.expoBB6_facts1 fun _ => .pred false).map Prod.fst
abbrev eKeys7 : List Nat := (Gen.expoBB7_facts1 fun _ => .pred false).map Prod.fst
abbrev sKeys1 : List Nat := (Gen.expoBB1_facts0 fun _ => .pred false).map Prod.fst
abbrev sKeys2 : List Nat := (Gen.expoBB2_facts0 fun _ => .pred false).map Prod.fst
abbrev sKeys3 : List Nat := (Gen.expoBB3_facts0 fun _ => .pred false).map Prod.fst
abbrev sKeys4 : List Nat := (Gen.expoBB4_facts0 fun _ => .pred false).map Prod.fst
abbrev sKeys5 : List Nat := (Gen.expoBB5_facts0 fun _ => .pred false).map Prod.fst
abbrev sKeys6 : List Nat := (Gen.expoBB6_facts0 fun _ => .pred false).map Prod.fst
abbrev sKeys7 : List Nat := (Gen.expoBB7_facts0 fun _ => .pred false).map Prod.fst
abbrev sKeys8 : List Nat := (Gen.expoBB8_facts0 fun _ => .pred false).map Prod.fst

variable {L : Launch} {g : Nat}

/-- The software `exp2` instance at pc 6059. -/
theorem instB0 (U : Nat → Value) (hk0 : SK.ni.Has (lookupD (Gen.expoBB0_facts3 U) 1407))
    (hk1 : SK.ni.Has (lookupD (Gen.expoBB0_facts3 U) 1408)) :
    ∃ n, Seg kernel Assumptions.all L g n 6059
      (factsFrom eKeys0 (lookupD (Gen.expoBB0_facts3 U))) 6090
      (Gen.expoBB1_facts0 (nextB0 U)) := by
  have hx := mB6059_regs
  simp only [Prod.mk.injEq] at hx
  obtain ⟨-, -, hxs, hxe⟩ := hx
  have h := seg_swExp2 (L := L) (g := g) (keys := eKeys0)
    (liveT := sKeys1)
    (W := lookupD (Gen.expoBB0_facts3 U))
    Flow.code_6059 rfl hmB6059 (by decide)
    (by decide +kernel) (.inl (by decide +kernel)) (by rw [hxs]; decide)
    (by rw [hxs]; exact hk0)
    (by rw [hxe]; decide) (by rw [hxe]; exact hk1) (by decide +kernel) (by decide +kernel)
    (by seg_free_pc)
  rw [hxs, hxe, show mB6059.stop = 6090 by decide +kernel] at h
  rw [expoBB1_facts0_eq]
  exact ⟨1, h⟩

/-- The software `exp2` instance at pc 6091. -/
theorem instB1 (U : Nat → Value)
    (hc : mB6091.shape.consts.map
        (fun p => valueEx (lookupD (Gen.expoBB1_facts1 U)) [] (mB6091.regOf p.1)) =
      mB6091.shape.consts.map Prod.snd)
    (hk0 : SK.ni.Has (lookupD (Gen.expoBB1_facts1 U) 1409))
    (hk1 : SK.ni.Has (lookupD (Gen.expoBB1_facts1 U) 1410)) :
    ∃ n, Seg kernel Assumptions.all L g n 6091
      (factsFrom eKeys1 (lookupD (Gen.expoBB1_facts1 U))) 6112
      (Gen.expoBB2_facts0 (nextB1 U)) := by
  have hx := mB6091_regs
  simp only [Prod.mk.injEq] at hx
  obtain ⟨-, -, hxs, hxe⟩ := hx
  have h := seg_swExp2 (L := L) (g := g) (keys := eKeys1)
    (liveT := sKeys2)
    (W := lookupD (Gen.expoBB1_facts1 U))
    Flow.code_6091 rfl hmB6091 (by decide)
    (by decide +kernel) (.inr ⟨by decide +kernel, hc⟩) (by rw [hxs]; decide)
    (by rw [hxs]; exact hk0)
    (by rw [hxe]; decide) (by rw [hxe]; exact hk1) (by decide +kernel) (by decide +kernel)
    (by seg_free_pc)
  rw [hxs, hxe, show mB6091.stop = 6112 by decide +kernel] at h
  rw [expoBB2_facts0_eq]
  exact ⟨1, h⟩

/-- The software `exp2` instance at pc 6131. -/
theorem instB2 (U : Nat → Value)
    (hc : mB6131.shape.consts.map
        (fun p => valueEx (lookupD (Gen.expoBB2_facts1 U)) [] (mB6131.regOf p.1)) =
      mB6131.shape.consts.map Prod.snd)
    (hk0 : SK.ni.Has (lookupD (Gen.expoBB2_facts1 U) 1423))
    (hk1 : SK.ni.Has (lookupD (Gen.expoBB2_facts1 U) 1424)) :
    ∃ n, Seg kernel Assumptions.all L g n 6131
      (factsFrom eKeys2 (lookupD (Gen.expoBB2_facts1 U))) 6152
      (Gen.expoBB3_facts0 (nextB2 U)) := by
  have hx := mB6131_regs
  simp only [Prod.mk.injEq] at hx
  obtain ⟨-, -, hxs, hxe⟩ := hx
  have h := seg_swExp2 (L := L) (g := g) (keys := eKeys2)
    (liveT := sKeys3)
    (W := lookupD (Gen.expoBB2_facts1 U))
    Flow.code_6131 rfl hmB6131 (by decide)
    (by decide +kernel) (.inr ⟨by decide +kernel, hc⟩) (by rw [hxs]; decide)
    (by rw [hxs]; exact hk0)
    (by rw [hxe]; decide) (by rw [hxe]; exact hk1) (by decide +kernel) (by decide +kernel)
    (by seg_free_pc)
  rw [hxs, hxe, show mB6131.stop = 6152 by decide +kernel] at h
  rw [expoBB3_facts0_eq]
  exact ⟨1, h⟩

/-- The software `exp2` instance at pc 6153. -/
theorem instB3 (U : Nat → Value)
    (hc : mB6153.shape.consts.map
        (fun p => valueEx (lookupD (Gen.expoBB3_facts1 U)) [] (mB6153.regOf p.1)) =
      mB6153.shape.consts.map Prod.snd)
    (hk0 : SK.ni.Has (lookupD (Gen.expoBB3_facts1 U) 1425))
    (hk1 : SK.ni.Has (lookupD (Gen.expoBB3_facts1 U) 1426)) :
    ∃ n, Seg kernel Assumptions.all L g n 6153
      (factsFrom eKeys3 (lookupD (Gen.expoBB3_facts1 U))) 6174
      (Gen.expoBB4_facts0 (nextB3 U)) := by
  have hx := mB6153_regs
  simp only [Prod.mk.injEq] at hx
  obtain ⟨-, -, hxs, hxe⟩ := hx
  have h := seg_swExp2 (L := L) (g := g) (keys := eKeys3)
    (liveT := sKeys4)
    (W := lookupD (Gen.expoBB3_facts1 U))
    Flow.code_6153 rfl hmB6153 (by decide)
    (by decide +kernel) (.inr ⟨by decide +kernel, hc⟩) (by rw [hxs]; decide)
    (by rw [hxs]; exact hk0)
    (by rw [hxe]; decide) (by rw [hxe]; exact hk1) (by decide +kernel) (by decide +kernel)
    (by seg_free_pc)
  rw [hxs, hxe, show mB6153.stop = 6174 by decide +kernel] at h
  rw [expoBB4_facts0_eq]
  exact ⟨1, h⟩

/-- The software `exp2` instance at pc 6193. -/
theorem instB4 (U : Nat → Value)
    (hc : mB6193.shape.consts.map
        (fun p => valueEx (lookupD (Gen.expoBB4_facts1 U)) [] (mB6193.regOf p.1)) =
      mB6193.shape.consts.map Prod.snd)
    (hk0 : SK.ni.Has (lookupD (Gen.expoBB4_facts1 U) 1439))
    (hk1 : SK.ni.Has (lookupD (Gen.expoBB4_facts1 U) 1440)) :
    ∃ n, Seg kernel Assumptions.all L g n 6193
      (factsFrom eKeys4 (lookupD (Gen.expoBB4_facts1 U))) 6214
      (Gen.expoBB5_facts0 (nextB4 U)) := by
  have hx := mB6193_regs
  simp only [Prod.mk.injEq] at hx
  obtain ⟨-, -, hxs, hxe⟩ := hx
  have h := seg_swExp2 (L := L) (g := g) (keys := eKeys4)
    (liveT := sKeys5)
    (W := lookupD (Gen.expoBB4_facts1 U))
    Flow.code_6193 rfl hmB6193 (by decide)
    (by decide +kernel) (.inr ⟨by decide +kernel, hc⟩) (by rw [hxs]; decide)
    (by rw [hxs]; exact hk0)
    (by rw [hxe]; decide) (by rw [hxe]; exact hk1) (by decide +kernel) (by decide +kernel)
    (by seg_free_pc)
  rw [hxs, hxe, show mB6193.stop = 6214 by decide +kernel] at h
  rw [expoBB5_facts0_eq]
  exact ⟨1, h⟩

/-- The software `exp2` instance at pc 6215. -/
theorem instB5 (U : Nat → Value)
    (hc : mB6215.shape.consts.map
        (fun p => valueEx (lookupD (Gen.expoBB5_facts1 U)) [] (mB6215.regOf p.1)) =
      mB6215.shape.consts.map Prod.snd)
    (hk0 : SK.ni.Has (lookupD (Gen.expoBB5_facts1 U) 1441))
    (hk1 : SK.ni.Has (lookupD (Gen.expoBB5_facts1 U) 1442)) :
    ∃ n, Seg kernel Assumptions.all L g n 6215
      (factsFrom eKeys5 (lookupD (Gen.expoBB5_facts1 U))) 6236
      (Gen.expoBB6_facts0 (nextB5 U)) := by
  have hx := mB6215_regs
  simp only [Prod.mk.injEq] at hx
  obtain ⟨-, -, hxs, hxe⟩ := hx
  have h := seg_swExp2 (L := L) (g := g) (keys := eKeys5)
    (liveT := sKeys6)
    (W := lookupD (Gen.expoBB5_facts1 U))
    Flow.code_6215 rfl hmB6215 (by decide)
    (by decide +kernel) (.inr ⟨by decide +kernel, hc⟩) (by rw [hxs]; decide)
    (by rw [hxs]; exact hk0)
    (by rw [hxe]; decide) (by rw [hxe]; exact hk1) (by decide +kernel) (by decide +kernel)
    (by seg_free_pc)
  rw [hxs, hxe, show mB6215.stop = 6236 by decide +kernel] at h
  rw [expoBB6_facts0_eq]
  exact ⟨1, h⟩

/-- The software `exp2` instance at pc 6255. -/
theorem instB6 (U : Nat → Value)
    (hc : mB6255.shape.consts.map
        (fun p => valueEx (lookupD (Gen.expoBB6_facts1 U)) [] (mB6255.regOf p.1)) =
      mB6255.shape.consts.map Prod.snd)
    (hk0 : SK.ni.Has (lookupD (Gen.expoBB6_facts1 U) 1455))
    (hk1 : SK.ni.Has (lookupD (Gen.expoBB6_facts1 U) 1456)) :
    ∃ n, Seg kernel Assumptions.all L g n 6255
      (factsFrom eKeys6 (lookupD (Gen.expoBB6_facts1 U))) 6276
      (Gen.expoBB7_facts0 (nextB6 U)) := by
  have hx := mB6255_regs
  simp only [Prod.mk.injEq] at hx
  obtain ⟨-, -, hxs, hxe⟩ := hx
  have h := seg_swExp2 (L := L) (g := g) (keys := eKeys6)
    (liveT := sKeys7)
    (W := lookupD (Gen.expoBB6_facts1 U))
    Flow.code_6255 rfl hmB6255 (by decide)
    (by decide +kernel) (.inr ⟨by decide +kernel, hc⟩) (by rw [hxs]; decide)
    (by rw [hxs]; exact hk0)
    (by rw [hxe]; decide) (by rw [hxe]; exact hk1) (by decide +kernel) (by decide +kernel)
    (by seg_free_pc)
  rw [hxs, hxe, show mB6255.stop = 6276 by decide +kernel] at h
  rw [expoBB7_facts0_eq]
  exact ⟨1, h⟩

/-- The software `exp2` instance at pc 6277. -/
theorem instB7 (U : Nat → Value)
    (hc : mB6277.shape.consts.map
        (fun p => valueEx (lookupD (Gen.expoBB7_facts1 U)) [] (mB6277.regOf p.1)) =
      mB6277.shape.consts.map Prod.snd)
    (hk0 : SK.ni.Has (lookupD (Gen.expoBB7_facts1 U) 1457))
    (hk1 : SK.ni.Has (lookupD (Gen.expoBB7_facts1 U) 1458)) :
    ∃ n, Seg kernel Assumptions.all L g n 6277
      (factsFrom eKeys7 (lookupD (Gen.expoBB7_facts1 U))) 6298
      (Gen.expoBB8_facts0 (nextB7 U)) := by
  have hx := mB6277_regs
  simp only [Prod.mk.injEq] at hx
  obtain ⟨-, -, hxs, hxe⟩ := hx
  have h := seg_swExp2 (L := L) (g := g) (keys := eKeys7)
    (liveT := sKeys8)
    (W := lookupD (Gen.expoBB7_facts1 U))
    Flow.code_6277 rfl hmB6277 (by decide)
    (by decide +kernel) (.inr ⟨by decide +kernel, hc⟩) (by rw [hxs]; decide)
    (by rw [hxs]; exact hk0)
    (by rw [hxe]; decide) (by rw [hxe]; exact hk1) (by decide +kernel) (by decide +kernel)
    (by seg_free_pc)
  rw [hxs, hxe, show mB6277.stop = 6298 by decide +kernel] at h
  rw [expoBB8_facts0_eq]
  exact ⟨1, h⟩
end
end PTX.Kernels.TmlFa4Fwd.Proof.Softmax
