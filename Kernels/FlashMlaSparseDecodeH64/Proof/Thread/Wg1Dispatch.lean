-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1Mma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1Index
public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.Wg1Tma

@[expose] public section

/-! # Warpgroup 1 dispatch to the index and TMA roles -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1Mma
open PTX PTX.Proof PTX.Flow

noncomputable section

/-- The prologue's values of the five registers `Wg1Index.Entry` carries: 459, 460, 461, 466,
and 2991. -/
theorem mem_facts1845 {L : Launch} {g w : Nat} {b : Bool} :
    (459, _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.valueOf L g 459) ∈
        facts1845 L g w b ∧
      (460, _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.valueOf L g 460) ∈
        facts1845 L g w b ∧
      (461, _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.valueOf L g 461) ∈
        facts1845 L g w b ∧
      (466, _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.valueOf L g 466) ∈
        facts1845 L g w b ∧
      (2991, _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.valueOf L g 2991) ∈
        facts1845 L g w b := by
  simp [facts1845, queryOf_eq_ctaidX, batchOf_eq_ctaidY,
    _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.valueOf,
    _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.values, PTX.Flow.lookupLit,
    Option.getD_some]

/-- **The dispatch hands warp 7 to the index role**: the warp test at pc 1844 and the branch at
1845 reach `Wg1Index.Entry` at pc 2332. -/
theorem handoff_index {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) {t : TState} (h : At t 1844 (headFacts L g 7)) :
    ∃ t', run kernel asms L g 2 t = some t' ∧ Wg1Index.Entry P L g t' := by
  obtain ⟨t1, hr1, h1⟩ := step_setp11_7 L g h
  obtain ⟨t2, hr2, h2⟩ := head_branch L g (pc := 1845) (target := 2332) (p := 11)
    (pick := true) Flow.code_1845 h1 (by simp [facts1845])
    (by rw [h1.1]; decide) (by rw [h1.1]; decide)
  obtain ⟨h459, h460, h461, h466, h2991⟩ := mem_facts1845 (L := L) (g := g) (w := 7)
    (b := true)
  refine ⟨t2, run_comp hr1 hr2,
    ⟨h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1, ?_, ?_, ?_, ?_⟩⟩
  · exact holds_mem h2.2.2.2.2 (by simp [facts1845])
  · refine holds_of_facts h2.2.2.2.2 fun p hp => ?_
    simp only [factsFrom, List.mem_map] at hp
    obtain ⟨r, hr, rfl⟩ := hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact h459
    · exact h460
    · exact h461
    · exact h466
    · exact h2991
  · rw [← batchOf_eq_ctaidY]; exact batchOf_lt (g := g) hpre hg
  · rw [← queryOf_eq_ctaidX]; exact queryOf_lt (g := g) hpre hg

/-- The prologue's values of the three registers `Wg1Tma.Entry` carries: 460, 2990 and 2991. -/
theorem mem_facts1847 {L : Launch} {g w : Nat} {b11 b12 : Bool} :
    (460, _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.valueOf L g 460) ∈
        facts1847 L g w b11 b12 ∧
      (2990, _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.valueOf L g 2990) ∈
        facts1847 L g w b11 b12 ∧
      (2991, _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.valueOf L g 2991) ∈
        facts1847 L g w b11 b12 := by
  simp [facts1847, batchOf_eq_ctaidY,
    _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.valueOf,
    _root_.PTX.Kernels.FlashMlaSparseDecodeH64.Proof.values, PTX.Flow.lookupLit,
    Option.getD_some]

/-- **The dispatch hands warp 5 to the raw-KV producer**: the warp tests at pcs 1844 and 1846
and the branch at 1847 reach warp 5's entry at pc 2162, with the facts `Wg1Tma.Entry` states. -/
theorem handoff_tma {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) {t : TState} (h : At t 1844 (headFacts L g 5)) :
    ∃ t', run kernel asms L g 4 t = some t' ∧ Wg1Tma.Entry P L g t' := by
  obtain ⟨t1, hr1, h1⟩ := step_setp11_5 L g h
  obtain ⟨t2, hr2, h2⟩ := head_branch L g (pc := 1845) (target := 2332) (p := 11)
    (pick := false) Flow.code_1845 h1 (by simp [facts1845])
    (by rw [h1.1]; decide) (by rw [h1.1]; decide)
  obtain ⟨t3, hr3, h3⟩ := step_setp12_5 L g h2
  obtain ⟨t4, hr4, h4⟩ := head_branch L g (pc := 1847) (target := 2162) (p := 12)
    (pick := true) Flow.code_1847 h3 (by simp [facts1847])
    (by rw [h3.1]; decide) (by rw [h3.1]; decide)
  obtain ⟨h460, h2990, h2991⟩ := mem_facts1847 (L := L) (g := g) (w := 5) (b11 := false)
    (b12 := true)
  refine ⟨t4, run_comp (run_comp (run_comp hr1 hr2) hr3) hr4,
    ⟨h4.1, h4.2.1, h4.2.2.1, h4.2.2.2.1, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact holds_mem h4.2.2.2.2 (by simp [facts1847])
  · exact holds_mem h4.2.2.2.2 (by simp [facts1847])
  · refine holds_of_facts h4.2.2.2.2 fun p hp => ?_
    simp only [factsFrom, List.mem_map] at hp
    obtain ⟨r, hr, rfl⟩ := hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h460
    · exact h2990
    · exact h2991
  · rw [← batchOf_eq_ctaidY]; exact batchOf_lt (g := g) hpre hg
  · rw [← queryOf_eq_ctaidX]; exact queryOf_lt (g := g) hpre hg

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Wg1Mma
