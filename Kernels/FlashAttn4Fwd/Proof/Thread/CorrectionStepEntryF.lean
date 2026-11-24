-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionStepEntry
public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionStepTrip

@[expose] public section

/-! # The addresses of the correction warps' chunks

From the third selection of the swizzle to stage 0's first barrier: the Tensor Memory address
of each chunk (`or` of the warp's lane field and the column), the swizzled staging address of
each chunk (the row's chunk-0 address plus the selected `±16`, `±32`, `±64`), the trip count's
negation (the loop counter's start), `n - 1` and its test, and the item's parities. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- Chunk `c0 + 2^k` of the swizzled row from chunk `c0` (bit `k` clear): `16 · 2^k` up when
bit `k` of the thread index is clear, down when it is set. -/
theorem stage_flip (L : Launch) (g st c0 k : Nat) (hk : k < 3) (hc0 : c0 < 8)
    (hb : c0 / 2 ^ k % 2 = 0) :
    (tidOf L g / 2 ^ k % 2 = 0 → stage L g st c0 + 16 * 2 ^ k = stage L g st (c0 + 2 ^ k)) ∧
      (tidOf L g / 2 ^ k % 2 = 1 → stage L g st c0 = stage L g st (c0 + 2 ^ k) + 16 * 2 ^ k) :=
    by
  have hf := xor_flip (x := lnOf L g % 8) (Nat.mod_lt _ (by decide)) hc0 hk hb
  have e : lnOf L g % 8 / 2 ^ k % 2 = tidOf L g / 2 ^ k % 2 := by
    simp only [lnOf]; interval_cases k <;> omega
  rw [e] at hf
  unfold stage
  constructor
  · intro h; have := hf.1 h; omega
  · intro h; have := hf.2 h; omega

/-- The staging addresses fit a word. -/
theorem stage_lt (hpre : Pre P L mem0) (st c : Nat) (hst : st < 2) (hc : c < 8) :
    stage L g st c < 2 ^ 31 := by
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  have hx : lnOf L g % 8 ^^^ c < 2 ^ 3 :=
    Nat.xor_lt_two_pow (Nat.mod_lt _ (by decide)) (by omega)
  have hk : kOf L g < 4 := Nat.mod_lt _ (by decide)
  have hl : lnOf L g < 32 := Nat.mod_lt _ (by decide)
  unfold stage
  simp only [sb]
  omega

/-- The selections and steps of the chunk addresses of stage `st`. -/
syntax "stage_facts" term:max term:max term:max term:max : tactic
macro_rules
  | `(tactic| stage_facts $hpre $L $g $st) => `(tactic| (
      have h0 := stage_flip $L $g $st 0 0 (by decide) (by decide) (by decide)
      have h1 := stage_flip $L $g $st 2 0 (by decide) (by decide) (by decide)
      have h2 := stage_flip $L $g $st 4 0 (by decide) (by decide) (by decide)
      have h3 := stage_flip $L $g $st 6 0 (by decide) (by decide) (by decide)
      have h4 := stage_flip $L $g $st 0 1 (by decide) (by decide) (by decide)
      have h5 := stage_flip $L $g $st 4 1 (by decide) (by decide) (by decide)
      have h6 := stage_flip $L $g $st 0 2 (by decide) (by decide) (by decide)
      have := stage_lt (g := $g) $hpre $st 0 (by decide) (by decide)
      have := stage_lt (g := $g) $hpre $st 1 (by decide) (by decide)
      have := stage_lt (g := $g) $hpre $st 2 (by decide) (by decide)
      have := stage_lt (g := $g) $hpre $st 3 (by decide) (by decide)
      have := stage_lt (g := $g) $hpre $st 4 (by decide) (by decide)
      have := stage_lt (g := $g) $hpre $st 5 (by decide) (by decide)
      have := stage_lt (g := $g) $hpre $st 6 (by decide) (by decide)
      have := stage_lt (g := $g) $hpre $st 7 (by decide) (by decide)
      have htid : tidOf $L $g = $g % 512 := by simp only [tidOf, ($hpre).block]
      simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.pow_zero, Nat.div_one]
        at h0 h1 h2 h3 h4 h5 h6))

/-- The Tensor Memory addresses of stage 0's chunks. -/
theorem entry_f1 (hpre : Pre P L mem0) (aw : Value) (a : ℝ) (o : List Value) :
    Seg kernel asms L g 8 3808
      ((2731, b32 (selN (bit0 L g) 4294967280 16)) :: factsX L g 3807 (dS aw a o)
        [(297, .pred (bit0 L g)), (2721, b32 (trips L)), (2723, b32 0),
          (2725, b32 (2097152 * kOf L g)), (2727, b32 (selN (bit2 L g) 64 4294967232)),
          (2729, b32 (selN (bit1 L g) 32 4294967264))]) 3816
      (factsX L g 3816 (dS aw a o)
        [(2721, b32 (trips L)), (2723, b32 0), (2725, b32 (2097152 * kOf L g)),
          (2727, b32 (selN (bit2 L g) 64 4294967232)), (2729, b32 (selN (bit1 L g) 32 4294967264)),
          (2731, b32 (selN (bit0 L g) 4294967280 16))]) := by
  intro t h
  corr_segx h hpre

/-- The Tensor Memory addresses of stage 1's chunks. -/
theorem entry_f2 (hpre : Pre P L mem0) (aw : Value) (a : ℝ) (o : List Value) :
    Seg kernel asms L g 7 3816
      (factsX L g 3816 (dS aw a o)
        [(2721, b32 (trips L)), (2723, b32 0), (2725, b32 (2097152 * kOf L g)),
          (2727, b32 (selN (bit2 L g) 64 4294967232)), (2729, b32 (selN (bit1 L g) 32 4294967264)),
          (2731, b32 (selN (bit0 L g) 4294967280 16))]) 3823
      (factsX L g 3823 (dS aw a o)
        [(2721, b32 (trips L)), (2723, b32 0), (2727, b32 (selN (bit2 L g) 64 4294967232)),
          (2729, b32 (selN (bit1 L g) 32 4294967264)),
          (2731, b32 (selN (bit0 L g) 4294967280 16))]) := by
  intro t h
  corr_segx h hpre

/-- The trip count. -/
theorem entry_f5 (hpre : Pre P L mem0) (aw : Value) (a : ℝ) (o : List Value) :
    Seg kernel asms L g 1 3837
      (factsX L g 3837 (dS aw a o) [(2721, b32 (trips L)), (2723, b32 0)]) 3838
      (factsX L g 3838 (dS aw a o) [(2732, b32 (trips L))]) := by
  intro t h
  have hn := trips_lt hpre
  have hn1 : 1 ≤ trips L := by
    have := hpre.skPos; have := hpre.skDiv128; rw [trips, skOf_eq hpre]; omega
  have hcs := clusters_le hpre
  have hnc : L.grid / L.clusterSize.val = P.clusters := by
    rw [hpre.grid, hpre.cluster]; omega
  corr_segx h hpre [nClusters, hnc]

/-- Its negation (the loop counter's start) and the number of clusters. -/
theorem entry_f6 (hpre : Pre P L mem0) (aw : Value) (a : ℝ) (o : List Value) :
    Seg kernel asms L g 2 3838
      (factsX L g 3838 (dS aw a o) [(2732, b32 (trips L))]) 3840
      (factsX L g 3840 (dS aw a o) [(2732, b32 (trips L))]) := by
  intro t h
  have hn := trips_lt hpre
  have hn1 : 1 ≤ trips L := by
    have := hpre.skPos; have := hpre.skDiv128; rw [trips, skOf_eq hpre]; omega
  have hcs := clusters_le hpre
  have hnc : L.grid / L.clusterSize.val = P.clusters := by
    rw [hpre.grid, hpre.cluster]; omega
  corr_segx h hpre [nClusters, hnc]

/-- Two barrier addresses, `n - 1` and the item's parities. -/
theorem entry_f7 (hpre : Pre P L mem0) (aw : Value) (a : ℝ) (o : List Value) :
    Seg kernel asms L g 5 3840
      (factsX L g 3840 (dS aw a o) [(2732, b32 (trips L))]) 3845
      (factsAt L g 3845 (dS aw a o)) := by
  intro t h
  have hn := trips_lt hpre
  have hn1 : 1 ≤ trips L := by
    have := hpre.skPos; have := hpre.skDiv128; rw [trips, skOf_eq hpre]; omega
  have hcs := clusters_le hpre
  have hnc : L.grid / L.clusterSize.val = P.clusters := by
    rw [hpre.grid, hpre.cluster]; omega
  corr_segx h hpre [nClusters, hnc]

/-- The test of a single trip. -/
theorem entry_f8 (hpre : Pre P L mem0) (aw : Value) (a : ℝ) (o : List Value) :
    Seg kernel asms L g 1 3845
      (factsAt L g 3845 (dS aw a o)) (Site.sync 0 .first).pc
      (facts L g (dS aw a o)) := by
  intro t h
  have hn := trips_lt hpre
  have hn1 : 1 ≤ trips L := by
    have := hpre.skPos; have := hpre.skDiv128; rw [trips, skOf_eq hpre]; omega
  have hcs := clusters_le hpre
  have hnc : L.grid / L.clusterSize.val = P.clusters := by
    rw [hpre.grid, hpre.cluster]; omega
  corr_segx h hpre [nClusters, hnc]

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
