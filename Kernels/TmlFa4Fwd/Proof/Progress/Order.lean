-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Progress.Time
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The inequalities of the time table, by wait

For every wait of the pipeline, the time of its blocker's latest state is before the time of the
wait (`Progress/Time.lean` lists the waits). `clk` times are stated with the sites' bands; the MMA
warp's places (`Mma.Site.ord`) are numbers. `u` is the softmax round or MMA block, `k` a loader
packet, `i` a ring index.

`Mm.pipeT p q r` is the MMA warp's time at place `q` with `r` rounds done: places 1 to 16 are the
first block (slot 0), 20 to 49 loop round `r` (slot `r + 1`), 60 to 85 the tail (slot `r + 1`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Progress
open PTX PTX.Proof PTX.Flow

noncomputable section

variable (p : Params)

/-! ### The MMA warp's places -/

theorem pipeT_pre {q r : Nat} (h : q < 20) : Mm.pipeT p q r = clk p 0 (2 * q) := by
  simp [Mm.pipeT, h]

theorem pipeT_round {q r : Nat} (h : 20 ≤ q) : Mm.pipeT p q r = clk p (r + 1) (2 * q) := by
  simp [Mm.pipeT, show ¬ q < 20 by omega]

/-- Every place of slot `s` is before every offset from 512 on. -/
theorem pipeT_lt {q r s o : Nat} (hq : q ≤ 100) (hs : (if q < 20 then 0 else r + 1) ≤ s)
    (ho : 512 ≤ o) : Mm.pipeT p q r < clk p s o := by
  unfold Mm.pipeT
  rcases Nat.lt_or_eq_of_le hs with h | h
  · exact clk_lt_of_slot h (by unfold span; omega)
  · rw [h]; exact clk_lt_of_off (by omega)

/-- A state of an earlier slot is before every place of the MMA warp's loop and tail. -/
theorem clk_lt_pipeT {q r s o : Nat} (hq : 20 ≤ q) (hs : s ≤ r) (ho : o < span) :
    clk p s o < Mm.pipeT p q r := by
  rw [pipeT_round p hq]
  exact clk_lt_of_slot (by omega) ho

/-! ### S full, P full, the statistics barriers, the credits -/

/-- **S full**: the MMA warp's QK commits of block `u` (places 8 and 14 for block 0, 34 and 47 of
loop round `u - 1`) are before the S-full polls of softmax round `u`. -/
theorem sfull_order (st : Nat) (hst : st < 2) :
    Mm.pipeT p 14 0 < clk p 0 (bandS st + 2) ∧
      ∀ r, Mm.pipeT p 47 r < clk p (r + 1) (bandS st + 2) :=
  ⟨pipeT_lt p (by omega) (by simp) (by simp only [bandS]; omega),
    fun r => pipeT_lt p (by omega) (by simp) (by simp only [bandS]; omega)⟩

/-- **P full and the second P**: every state of softmax round `u` and of the correction's rescale
round `u` is before the MMA warp's P polls of block `u` (places 21, 27, 35, 40 of loop round `u`,
65, 71, 73, 78 of the tail after `u` rounds). -/
theorem pfull_order {q u o : Nat} (hq : 20 ≤ q) (ho : o < span) :
    clk p u o < Mm.pipeT p q u := clk_lt_pipeT p hq le_rfl ho

/-- **Statistics barrier**: softmax stage `st`'s arrival of round `u` is before the correction's
sync of generation `u`. -/
theorem stat_order (st u : Nat) : clk p u (bandS st + 42) < clk p u (bandC st) :=
  clk_lt_of_off (by simp only [bandS, bandC]; omega)

/-- **Stage 0's credit**: the correction's part of stage 1 of round `u` is before softmax stage 0's
closing poll of round `u`. -/
theorem credit0_order (u o : Nat) (ho : o < 256) : clk p u (bandC 1 + o) < clk p u (bandP 0 + 20) :=
  clk_lt_of_off (by simp only [bandC, bandP]; omega)

/-- **Stage 1's credit**: the correction's part of stage 0 of round `u + 1` up to its credit arrival
(offset 60, the final stage's at 100) is before softmax stage 1's closing poll of round `u`, which
opens slot `u + 1`. -/
theorem credit1_order (u o : Nat) (ho : o < 256) : clk p u (bandC 0 + o) < clk p u (bandS 1) :=
  clk_lt_of_off (by simp only [bandC, bandS]; omega)

/-- **Correction's O polls**: the MMA warp's tail commits (places 83 and 85) after `r` rounds are
before the final stage of slot `r + 1`. -/
theorem o_order (r st o : Nat) : Mm.pipeT p 85 r < clk p (r + 1) (bandC st + o) :=
  pipeT_lt p (by omega) (by simp) (by simp only [bandC]; omega)

/-! ### The loader -/

/-- **Ring empty** (`R(k - 3) < T(k)`): the MMA warp's release of index `i` (places 16, 43, 49, 81)
is before every loader time of packet `i + 3`. -/
theorem empty_order {q r i o : Nat} (hq : q = 16 ∨ q = 43 ∨ q = 49 ∨ q = 81)
    (hr : q < 20 → r = 0) (hi : Mma.ringRel q r = i) (hb : (i + 1) / 2 ≤ bmax p) :
    Mm.pipeT p q r < clk p (Ld.slot p (i + 3)) (bandL + o) := by
  have hs : Ld.slot p (i + 3) = (i + 1) / 2 := by
    simp only [Ld.slot, show (i + 3 - 2) / 2 = (i + 1) / 2 by omega]
    exact slotOf_eq hb
  rw [hs]
  refine pipeT_lt p (by omega) ?_ (by simp only [bandL]; omega)
  rcases hq with rfl | rfl | rfl | rfl <;> simp [Mma.ringRel, Mma.pq] at hi hr ⊢ <;> omega

/-- **Ring full** (`T(k) < P(i)` for `k ≤ i`): a loader state of packet `k ≥ 2` is before the MMA
warp's poll of ring index `i ≥ k`; the first block is before the pipeline. -/
theorem full_order {d : Loader.D} {n : Cls → Nat} {q r : Nat} {v : Mma.V}
    (h : Ld.prime d.site = true ∨ (Ld.pipe d.site = true ∧ 2 ≤ Ld.idx d.site n ∧
      Ld.idx d.site n ≤ Mma.ringAcq q r))
    (hq : q = 2 ∨ q = 20 ∨ q = 29 ∨ q = 64) (hp : v.ps = Mma.shAt q r) (hr : q < 20 → r = 0) :
    Ld.time p d n < Mm.pipeT p q (Mm.round q v) := by
  have h1 := (Ld.bound_le p _).trans (Mm.kv_time p hq hp hr)
  rcases h with h | ⟨h, h2, h3⟩
  · have := Ld.time_prime (p := p) (n := n) h
    have := Ld.pipeBase_le_bound p (Mma.ringAcq q r)
    omega
  · have := Ld.time_pipe (p := p) h h2 h3
    omega

/-- **Bias full**: the loader's TMA groups of packets up to `2 u + 1` (warm round `u - 1`, group 6)
are before softmax round `u ≥ 1`'s Bias poll. -/
theorem biasFull_order {k u o o' : Nat} (hk : k ≤ 2 * u + 1) (hu : 1 ≤ u) (ho : o < span) :
    clk p (Ld.slot p k) o < clk p u o' := by
  refine clk_lt_of_slot ?_ ho
  simp only [Ld.slot, slotOf]; omega

/-- **Bias empty**: softmax round `j`'s Bias arrivals are before the loader's waits of TMA groups 4
and 5 of warm round `j` (packet `2 j + 3`) and of group 6. -/
theorem biasEmpty_order {j k st o : Nat} (hk : 2 * j + 2 ≤ k) (hj : j ≤ bmax p) (hst : st < 2) :
    clk p j (bandS st + 38) < clk p (Ld.slot p k) (bandL + o) := by
  have hs : j ≤ Ld.slot p k := by simp only [Ld.slot, slotOf]; omega
  rcases Nat.lt_or_eq_of_le hs with h | h
  · exact clk_lt_of_slot h (by simp only [bandS, span]; omega)
  · rw [← h]; exact clk_lt_of_off (by simp only [bandS, bandL]; omega)

/-- **The drain**: every pipeline state and every state of the tail is before the loader's drain
and every lane's end. -/
theorem drain_order {s o : Nat} (hs : s ≤ bmax p + 1) (ho : o < span) :
    clk p s o < doneBase p := by
  have h : clk p s o ≤ clk p (bmax p + 1) (span - 1) := by
    unfold clk
    have := Nat.mul_le_mul_left span hs
    omega
  have h2 : clk p (bmax p + 1) (span - 1) < endBase p := by
    unfold endBase tailBase clk span; omega
  unfold doneBase
  omega

end
end PTX.Kernels.TmlFa4Fwd.Proof.Progress
