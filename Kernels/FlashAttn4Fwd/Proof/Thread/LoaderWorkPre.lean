-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.LoaderWork
public import Lemmas.Flow.SignedBits

@[expose] public section

/-! # The schedule under `Pre`

What the code's schedule registers mean for a launch satisfying `Pre`: the number of clusters
is `P.clusters`, the cluster index is below it, the item count is `P.items`, the item register
of item `i` is `c + i·G` while it is below the count, and the branches of the item loop
(`setp.ge.s32` at the start, `setp.lt.s32` after an item) decide `0 < T` and `i + 1 < T`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Work
open PTX PTX.Proof

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0}

theorem G_eq (hpre : Pre P L mem0) : G L = P.clusters := by
  simp only [G, hpre.grid, hpre.cluster]
  omega

theorem cid_lt (hpre : Pre P L mem0) {g : Nat} (hg : g < L.threads) : cid L g < P.clusters := by
  have hb := hpre.block
  have hgr := hpre.grid
  simp only [Launch.threads] at hg
  simp only [cid, clusterOf, ctaOf, Launch.oneDim_clusterOfCta hpre.oneDimLaunch.1, hpre.cluster]
  have : g / L.block < L.grid := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hg)
  omega

theorem items_lt (hpre : Pre P L mem0) : P.items < 2 ^ 31 := by
  have := hpre.scheduleRange
  have := hpre.clustersPos
  omega

theorem totOf_eq' (hpre : Pre P L mem0) : totOf L = P.items := by
  have h := items_lt hpre
  simp only [totOf, hpre.paramItems, Option.getD_some, BitVec.toNat_ofNat]
  omega

theorem totW_eq (hpre : Pre P L mem0) : totW L = BitVec.ofNat 64 P.items := by
  rw [totW, totOf_eq' hpre]

theorem rd_ofNat {a : Nat} (ha : a < 2 ^ 32) : rd (BitVec.ofNat 64 a) = BitVec.ofNat 64 a :=
  truncBits_ofNat ha (by omega)

theorem toSigned_of_lt {a : Nat} (ha : a < 2 ^ 31) : toSigned 32 (BitVec.ofNat 64 a) = a := by
  rw [toSigned_eq_toInt32, CeilDiv.toInt32_of_lt ha]

/-- Item `i` exists (`i < T`) exactly when its index is below the item count. -/
theorem lt_T_iff {g i : Nat} (hpre : Pre P L mem0) :
    i < T L g ↔ cid L g + i * G L < P.items := by
  have hG : 0 < G L := by rw [G_eq hpre]; exact hpre.clustersPos
  have htot : totOf L = P.items := totOf_eq' hpre
  simp only [T, StaticSchedule.count, htot]
  constructor
  · intro h
    have h1 : (i + 1) * G L ≤ P.items - cid L g + G L - 1 :=
      (Nat.le_div_iff_mul_le hG).mp h
    rw [Nat.add_mul, Nat.one_mul] at h1
    omega
  · intro h
    apply (Nat.le_div_iff_mul_le hG).mpr
    rw [Nat.succ_mul]
    omega

/-- The item register of item `i` is its index while that index fits a word. -/
theorem workW_eq {g : Nat} (hpre : Pre P L mem0) :
    ∀ i, cid L g + i * G L < 2 ^ 32 → workW L g i = BitVec.ofNat 64 (cid L g + i * G L)
  | 0, _ => by simp [workW]
  | i + 1, h => by
    have he : (i + 1) * G L = i * G L + G L := Nat.succ_mul i (G L)
    have hG : G L < 2 ^ 32 := by omega
    have hi : cid L g + i * G L < 2 ^ 32 := by omega
    rw [workW, workW_eq hpre i hi, GW, addW, rd_ofNat hi, truncBits_ofNat hG (by omega),
      rd_ofNat hG, ← BitVec.ofNat_add, he, ← Nat.add_assoc]
    exact truncBits_ofNat (by omega) (by omega)

/-- The branch past the item loop at the start: the cluster has no item. -/
theorem start_branch {g : Nat} (hpre : Pre P L mem0) (hg : g < L.threads) :
    PTX.compare .ge .s 32 (rd (BitVec.ofNat 64 (cid L g))) (rd (totW L)) =
      decide ¬ 0 < T L g := by
  have hc := cid_lt hpre hg
  have hit := items_lt hpre
  have hcl : P.items + P.clusters ≤ 2 ^ 31 := hpre.scheduleRange
  have h0 := lt_T_iff (g := g) (i := 0) hpre
  rw [Nat.zero_mul, Nat.add_zero] at h0
  rw [totW_eq hpre, rd_ofNat (by omega), rd_ofNat (by omega)]
  simp only [PTX.compare, toSigned_of_lt (show cid L g < 2 ^ 31 by omega),
    toSigned_of_lt (show P.items < 2 ^ 31 by omega), h0]
  simp only [ge_iff_le, Nat.cast_le, not_lt]

/-- The branch back into the item loop after item `i`: item `i + 1` exists. -/
theorem loop_branch {g i : Nat} (hpre : Pre P L mem0) (hi : i < T L g) :
    PTX.compare .lt .s 32 (rd (workW L g (i + 1))) (rd (totW L)) = decide (i + 1 < T L g) := by
  have hit := items_lt hpre
  have hcl : P.items + P.clusters ≤ 2 ^ 31 := hpre.scheduleRange
  have h0 := (lt_T_iff (g := g) hpre).mp hi
  have h1 := lt_T_iff (g := g) (i := i + 1) hpre
  have hG := G_eq hpre
  have hw : cid L g + (i + 1) * G L < 2 ^ 31 := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  rw [totW_eq hpre, workW_eq hpre (i + 1) (by omega), rd_ofNat (by omega), rd_ofNat (by omega)]
  simp only [PTX.compare, toSigned_of_lt hw, toSigned_of_lt (show P.items < 2 ^ 31 by omega), h1]
  simp only [Nat.cast_lt]

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Work
