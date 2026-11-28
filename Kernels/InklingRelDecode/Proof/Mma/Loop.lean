-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.Branches

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Flow PTX.Proof

variable {L : Launch} {g : Nat} {regs : Nat → Value} {w : Value} {d : D}
local notation "F" => liveFacts L regs w
local notation "S" => SegU kernel Assumptions.all L g

theorem pv_tail (hs : L.sharedBase + 213340 ≤ 2 ^ 18) (hi : 0 < d.i) (hn : d.i < 2 ^ 31) :
    S 2500 (F d 2500) 2509 (F {d with site := .pvBar} 2509) := by
  apply (SegU.of_seg (first_iter hn)).comp
  apply (enter_pv (Nat.ne_of_gt hi)).comp
  exact SegU.of_seg (p_head hs hn hi)

theorem loop_back (hs : L.sharedBase + 213340 ≤ 2 ^ 18) (hi : d.i ≤ d.limit)
    (hn : d.limit ≤ 2147483646) :
    S 2447 (F d 2447) (iterNext d).site.pc (F (iterNext d) (iterNext d).site.pc) := by
  apply (SegU.of_seg (bump_cursors hi hn)).comp
  by_cases he : d.i = d.limit
  · rw [show iterNext d = {d with i := d.i + 1, site := .finBar} by simp [iterNext, he]]
    exact end_iter he
  · apply (next_iter he).comp
    let d1 := {d with i := d.i + 1}
    have h1 : d1.i < 2 ^ 31 := by dsimp [d1]; omega
    have h2 : d1.limit < 2 ^ 31 := by change d.limit < _; omega
    apply (index_check (d := d1) h1 h2).comp
    by_cases hq : d.i + 1 < d.limit
    · apply (qk_branch (d := d1) hq).comp
      simp only [iterNext, he, hq, ↓reduceIte]
      exact SegU.of_seg (ready_head (d := d1) hs h1)
    · apply (pv_branch (d := d1) (Nat.le_of_not_gt hq)).comp
      simp only [iterNext, he, hq, ↓reduceIte]
      exact pv_tail (d := d1) hs (Nat.zero_lt_succ _) h1

theorem after_qk (hs : L.sharedBase + 213340 ≤ 2 ^ 18) (hi : d.i < d.limit)
    (hn : d.limit ≤ 2147483646) :
    S 2500 (F d 2500) (afterQk d).site.pc (F (afterQk d) (afterQk d).site.pc) := by
  by_cases hz : d.i = 0
  · simp only [afterQk, hz, ↓reduceIte]
    apply (SegU.of_seg (first_iter (by omega : d.i < 2 ^ 31))).comp
    exact (skip_pv hz).comp (loop_back hs hi.le hn)
  · simp only [afterQk, hz, ↓reduceIte]
    exact pv_tail hs (by omega) (by omega)

end PTX.Kernels.InklingRelDecode.Proof.Mma
