-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Mma.NoUbLeaf

@[expose] public section

/-! # The strict loop spans of the MMA warp

The spans of `StepsStart` and `Loop` again, as strict pieces: the loop bound has a bit pattern
and so has the recorded base word. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Flow PTX.Proof

variable {L : Launch} {g : Nat} {regs : Nat → Value} {w : Value} {d : D}
local notation "F" => liveFacts L regs w

theorem pv_tail_s (hs : L.sharedBase + 213340 ≤ 2 ^ 18) (hi : 0 < d.i) (hn : d.i < 2 ^ 31) :
    SegE L g 2500 (F d 2500) 2509 (F {d with site := .pvBar} 2509) :=
  (SegE.of_seg (first_iter hn)).comp ((enter_pv_s (Nat.ne_of_gt hi)).comp
    (SegE.of_seg (p_head hs hn hi)))

theorem loop_back_s (hs : L.sharedBase + 213340 ≤ 2 ^ 18) (hi : d.i ≤ d.limit)
    (hn : d.limit ≤ 2147483646) (hw : d.word.regBits.isSome) :
    SegE L g 2447 (F d 2447) (iterNext d).site.pc (F (iterNext d) (iterNext d).site.pc) := by
  apply (SegE.of_seg (bump_cursors hi hn)).comp
  by_cases he : d.i = d.limit
  · rw [show iterNext d = {d with i := d.i + 1, site := .finBar} by simp [iterNext, he]]
    exact end_iter_s he
  · apply (next_iter_s he).comp
    let d1 := {d with i := d.i + 1}
    have h1 : d1.i < 2 ^ 31 := by dsimp [d1]; omega
    have h2 : d1.limit < 2 ^ 31 := by change d.limit < _; omega
    apply (index_check_s (d := d1) hw h1 h2).comp
    by_cases hq : d.i + 1 < d.limit
    · apply (qk_branch_s (d := d1) hq).comp
      simp only [iterNext, he, hq, ↓reduceIte]
      exact SegE.of_seg (ready_head (d := d1) hs h1)
    · apply (pv_branch_s (d := d1) (Nat.le_of_not_gt hq)).comp
      simp only [iterNext, he, hq, ↓reduceIte]
      exact pv_tail_s (d := d1) hs (Nat.zero_lt_succ _) h1

theorem after_qk_s (hs : L.sharedBase + 213340 ≤ 2 ^ 18) (hi : d.i < d.limit)
    (hn : d.limit ≤ 2147483646) (hw : d.word.regBits.isSome) :
    SegE L g 2500 (F d 2500) (afterQk d).site.pc (F (afterQk d) (afterQk d).site.pc) := by
  by_cases hz : d.i = 0
  · simp only [afterQk, hz, ↓reduceIte]
    apply (SegE.of_seg (first_iter (by omega : d.i < 2 ^ 31))).comp
    exact (skip_pv_s hz).comp (loop_back_s hs hi.le hn hw)
  · simp only [afterQk, hz, ↓reduceIte]
    exact pv_tail_s hs (by omega) (by omega)

private theorem final_facts (d : D) :
    F {d with i := d.i + 1, site := .finBar} 2550 = F {d with site := .finBar} 2550 := by
  unfold liveFacts
  rw [show Flow.live 2550 = [3,462,463,464,465,466,528,529,530,531,532,534,1949,2020] by decide]
  simp only [factsFrom, List.map_cons, List.map_nil, valueOf, values, lookupLit]

theorem inv_start_s (d : D) (hi : d.i = 0) : Inv {d with site := startSite d.limit} := by
  unfold startSite
  split_ifs
  · trivial
  · change d.i < d.limit ∧ d.limit ≤ 2147483646
    omega

theorem enter_loop_s (hs : L.sharedBase + 213340 ≤ 2 ^ 18) (hi : d.i = 0)
    (hd : d.word.regBits.isSome) (hw : w.regBits.isSome) :
    SegE L g 2425 (F d 2425) (startSite d.limit).pc (F {d with site := startSite d.limit}
      (startSite d.limit).pc) := by
  apply (limit_check_s hd).comp
  by_cases hh : 2147483646 < d.limit
  · rw [show startSite d.limit = .finBar by simp [startSite, hh]]
    exact over_limit_s hh
  have hn : d.limit ≤ 2147483646 := by omega
  apply (within_limit_s hn).comp
  apply (output_base_s hw).comp
  apply (SegE.of_seg (setup_descriptors hs hi)).comp
  apply (iter_limit_s hd hn).comp
  apply (SegE.of_seg (seed_cursors hs hi)).comp
  apply (index_check_s hd (by omega : d.i < 2 ^ 31) (by omega)).comp
  by_cases hz : d.limit = 0
  · rw [show startSite d.limit = .finBar by simp [startSite, hz]]
    apply (pv_branch_s (by omega : d.limit ≤ d.i)).comp
    apply (SegE.of_seg (first_iter (by omega : d.i < 2 ^ 31))).comp
    apply (skip_pv_s hi).comp
    have h := loop_back_s (L := L) (g := g) (regs := regs) (w := w) hs
      (by omega : d.i ≤ d.limit) hn hd
    rw [show iterNext d = {d with site := .finBar, i := d.i + 1} by
      simp [iterNext, hi, hz]] at h
    change SegE L g 2447 (F d 2447) 2550 (F {d with site := .finBar} 2550)
    rw [← final_facts d]
    exact h
  · rw [show startSite d.limit = .qkBar by simp [startSite, hz, hh]]
    apply (qk_branch_s (by omega : d.i < d.limit)).comp
    exact SegE.of_seg (ready_head hs (by omega : d.i < 2 ^ 31))

end PTX.Kernels.InklingRelDecode.Proof.Mma
