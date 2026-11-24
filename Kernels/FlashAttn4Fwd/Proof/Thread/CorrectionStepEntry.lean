-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionStepSetup
public import Lemmas.Flow.Selp

@[expose] public section

/-! # The entry to the correction warps' item loop

After stage 1's first O-free arrival the thread computes its stage barriers' ids, its staging
addresses (the 128-byte swizzle: chunk `c` of row `ρ` at `16 (ρ % 8 ^^^ c)`, as `±16`, `±32`,
`±64` selected by the bits of the lane), the Tensor Memory addresses of its lanes, and the trip
count `n = ceil (sk / 128)` (the signed ceiling sequence; its rounding predicate is false,
`sk` being a multiple of `128`). `@%p291 bra` skips the loop when the cluster has no item. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- The cluster has an item exactly when its index is below the item count. -/
theorem items_pos (hpre : Pre P L mem0) : 0 < items L g ↔ clusterOf L g < totOf L := by
  have hG : 0 < nClusters L := by
    simp only [nClusters, hpre.grid, hpre.cluster]; have := hpre.clustersPos; omega
  simp only [items, StaticSchedule.count, Nat.div_pos_iff]
  omega

/-- The trip count is `sk / 128`. -/
theorem trips_eq (hpre : Pre P L mem0) : trips L = skOf L / 128 := by
  have := hpre.skDiv128
  rw [trips, skOf_eq hpre]
  omega

/-- The state the setup computes the facts of (the first item, before its first barrier). -/
abbrev dS (aw : Value) (a : ℝ) (o : List Value) : D := ⟨.sync 0 .first, 0, 0, aw, a, o⟩

/-- The selections of the swizzle: bits 2, 1 and 0 of the thread's index. -/
abbrev bit2 (L : Launch) (g : Nat) : Bool := decide (tidOf L g / 4 % 2 = 0)
abbrev bit1 (L : Launch) (g : Nat) : Bool := decide (tidOf L g / 2 % 2 = 0)
abbrev bit0 (L : Launch) (g : Nat) : Bool := decide (tidOf L g % 2 ≠ 0)

theorem entry_a (hpre : Pre P L mem0) (hg : g < L.threads) (tt : Nat) (aw : Value) (a : ℝ)
    (o : List Value) :
    Seg kernel asms L g 18 3766 (facts L g ⟨.free 1, 0, tt, aw, a, o⟩) 3784
      (factsX L g 3784 (dS aw a o)
        [(291, .pred (decide ¬ 0 < items L g)), (624, b32 (kOf L g))]) := by
  intro t h
  have hcl := clusterOf_lt hpre hg
  have hcl2 := clusters_le hpre
  have htot := totOf_lt hpre
  corr_segx h hpre [items_pos hpre, work]

/-- To the ceiling's `selp`. -/
theorem entry_b (hpre : Pre P L mem0) (aw : Value) (a : ℝ) (o : List Value) :
    Seg kernel asms L g 8 3785
      (factsX L g 3784 (dS aw a o)
        [(291, .pred (decide ¬ 0 < items L g)), (624, b32 (kOf L g))]) 3793
      (factsX L g 3793 (dS aw a o)
        [(294, .pred false), (624, b32 (kOf L g)), (2721, b32 (trips L))]) := by
  intro t h
  have hsk := hpre.skRange
  have hskd := hpre.skDiv128
  have hsk' := skOf_eq hpre
  corr_segx h hpre [trips_eq hpre]

/-- The ceiling, the stage-1 staging row and the first selection. -/
theorem entry_c (hpre : Pre P L mem0) (aw : Value) (a : ℝ) (o : List Value) :
    Seg kernel asms L g 8 3793
      (factsX L g 3793 (dS aw a o)
        [(294, .pred false), (624, b32 (kOf L g)), (2721, b32 (trips L))]) 3801
      (factsX L g 3801 (dS aw a o)
        [(295, .pred (bit2 L g)), (2721, b32 (trips L)), (2723, b32 0),
          (2725, b32 (2097152 * kOf L g))]) := by
  intro t h
  corr_segx h hpre

/-- Between the first and the second selection. -/
theorem entry_d (hpre : Pre P L mem0) (aw : Value) (a : ℝ) (o : List Value) :
    Seg kernel asms L g 2 3802
      ((2727, b32 (selN (bit2 L g) 64 4294967232)) :: factsX L g 3801 (dS aw a o)
        [(295, .pred (bit2 L g)), (2721, b32 (trips L)), (2723, b32 0),
          (2725, b32 (2097152 * kOf L g))]) 3804
      (factsX L g 3804 (dS aw a o)
        [(296, .pred (bit1 L g)), (2721, b32 (trips L)), (2723, b32 0),
          (2725, b32 (2097152 * kOf L g)), (2727, b32 (selN (bit2 L g) 64 4294967232))]) := by
  intro t h
  corr_segx h hpre

/-- Between the second and the third selection. -/
theorem entry_e (hpre : Pre P L mem0) (aw : Value) (a : ℝ) (o : List Value) :
    Seg kernel asms L g 2 3805
      ((2729, b32 (selN (bit1 L g) 32 4294967264)) :: factsX L g 3804 (dS aw a o)
        [(296, .pred (bit1 L g)), (2721, b32 (trips L)), (2723, b32 0),
          (2725, b32 (2097152 * kOf L g)), (2727, b32 (selN (bit2 L g) 64 4294967232))]) 3807
      (factsX L g 3807 (dS aw a o)
        [(297, .pred (bit0 L g)), (2721, b32 (trips L)), (2723, b32 0),
          (2725, b32 (2097152 * kOf L g)), (2727, b32 (selN (bit2 L g) 64 4294967232)),
          (2729, b32 (selN (bit1 L g) 32 4294967264))]) := by
  intro t h
  corr_segx h hpre

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
