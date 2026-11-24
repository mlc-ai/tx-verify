-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.ProAQ

@[expose] public section

/-! # The branches of the prologue

The sites whose successor the thread's own facts decide: the barrier before the preload (`bar2`:
`num_pre = 0` skips the preload, pc 189), the end of a preload block (`num_pre = 1` or `< 3`
skips the later blocks, pc 233 and 275) and the entries of the query-load chain (`qSite`). -/

namespace PTX.Kernels.InklingRelDecode.Proof.ProA
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {L : Launch} {g : Nat}

/-- The site a query-load entry reaches: the facts the invariant needs of it. -/
theorem qSite_prop {dt : Dat} (G : Nat) (hG : G ≤ 3) :
    (qSite L g dt G).afterSk = true ∧ guardVal L g dt (qSite L g dt G) = true ∧
      16 * G ≤ (qSite L g dt G).qIdx := by
  interval_cases G <;> simp only [qSite] <;> split_ifs <;>
    simp [Site.afterSk, guardVal, Site.qIdx, *]

theorem qSite_sub {dt : Dat} (G : Nat) : (qSite L g dt G).sub = 0 := by
  rcases G with _ | _ | _ | _ | G <;> simp only [qSite] <;> (try split_ifs) <;> rfl

/-- The invariant at a query-load entry, from the invariant at a site of the same data. -/
theorem inv_qSite {s : Site} {dt : Dat} (hi : Inv L g ⟨s, dt⟩)
    {G : Nat} (hG : G ≤ 3) (hq : s.qIdx ≤ 16 * G) : Inv L g ⟨qSite L g dt G, dt⟩ :=
  hi.mv _ dt rfl (qSite_prop G hG).2.1
    (fun j hj => hi.qz j (le_trans hq (le_trans (qSite_prop G hG).2.2 hj))) hi.qb


/-- From the barrier before the preload to the first block's barrier, or (no preload) to the
first site of the query loads; the thread dies at pc 182 when the division has no rule. -/
theorem seg_bar2 (L : Launch) (g : Nat) (dt : Dat) (ha : ArgsOk L g dt.pro)
    (hqz : ∀ j, 0 ≤ j → dt.q j = qZero) (hqb : ∀ j, (dt.q j).bytes = 2) :
    ∃ n, SegD kernel asms L g n 181 (factsAt L g 181 dt)
      (if v_p53 L g dt then Site.pbA0 else qSite L g dt 0).pc
      (factsAt L g (if v_p53 L g dt then Site.pbA0 else qSite L g dt 0).pc dt)
      (div182 L g dt = true ∧ ((!v_p53 L g dt) = true → addOk dt.w = true)) := by
  have hp : valueOf L g dt 53 = .pred (v_p53 L g dt) := rfl
  by_cases hq : v_p53 L g dt = true
  · simp only [hq, ↓reduceIte]
    refine ⟨_, ((SegD.of_seg (seg_181_182 L g dt)).comp ((segD_182_183 L g dt).comp
      (SegD.of_seg (Seg.comp (seg_183_189 L g dt) (Seg.comp (seg_bra_fall Flow.code_189 hp
      (by table_decide) (by simp [hq]) (by table_decide)) (seg_190_192 L g dt)))))).iff ?_⟩
    simp
  · have hq' : v_p53 L g dt = false := by simpa using hq
    simp only [hq', Bool.false_eq_true, ↓reduceIte]
    obtain ⟨n, hn⟩ := qenter L g dt ha hqz hqb
    refine ⟨_, ((SegD.of_seg (seg_181_182 L g dt)).comp ((segD_182_183 L g dt).comp
      ((SegD.of_seg (Seg.comp (seg_183_189 L g dt) (seg_bra_taken Flow.code_189 hp
      (by table_decide) (by simp [hq]) (by table_decide)))).comp hn))).iff ?_⟩
    simp

/-- After the last copy of block 0: the branch on `num_pre` (pc 233). -/
theorem seg_ab0 (L : Launch) (g : Nat) (dt : Dat) (ha : ArgsOk L g dt.pro)
    (hqz : ∀ j, 0 ≤ j → dt.q j = qZero) (hqb : ∀ j, (dt.q j).bytes = 2) :
    ∃ n, SegD kernel asms L g n 232 (factsAt L g 232 dt)
      (if v_p63 L g dt then qSite L g dt 0 else Site.pbA1).pc
      (factsAt L g (if v_p63 L g dt then qSite L g dt 0 else Site.pbA1).pc dt)
      (v_p63 L g dt = true → addOk dt.w = true) := by
  have hp : valueOf L g dt 63 = .pred (v_p63 L g dt) := rfl
  by_cases hq : v_p63 L g dt = true
  · simp only [hq, ↓reduceIte]
    obtain ⟨n, hn⟩ := qenter L g dt ha hqz hqb
    exact ⟨_, Raw.segD_iff (Raw.segD_pre (Seg.comp (seg_232_233 L g dt)
      (seg_bra_taken Flow.code_233 hp (by table_decide) (by simp [hq]) (by table_decide))) hn)
      (by simp)⟩
  · have hq' : v_p63 L g dt = false := by simpa using hq
    simp only [hq', Bool.false_eq_true, ↓reduceIte]
    exact ⟨_, Raw.segD_of_seg (Seg.comp (seg_232_233 L g dt) (Seg.comp
      (seg_bra_fall Flow.code_233 hp (by table_decide) (by simp [hq]) (by table_decide))
      (seg_234_236 L g dt))) (fun h => by simp at h)⟩

/-- After the last copy of block 1: the branch on `num_pre` (pc 275). -/
theorem seg_ab1 (L : Launch) (g : Nat) (dt : Dat) (ha : ArgsOk L g dt.pro)
    (hqz : ∀ j, 0 ≤ j → dt.q j = qZero) (hqb : ∀ j, (dt.q j).bytes = 2) :
    ∃ n, SegD kernel asms L g n 274 (factsAt L g 274 dt)
      (if v_p72 L g dt then qSite L g dt 0 else Site.pbA2).pc
      (factsAt L g (if v_p72 L g dt then qSite L g dt 0 else Site.pbA2).pc dt)
      (v_p72 L g dt = true → addOk dt.w = true) := by
  have hp : valueOf L g dt 72 = .pred (v_p72 L g dt) := rfl
  by_cases hq : v_p72 L g dt = true
  · simp only [hq, ↓reduceIte]
    obtain ⟨n, hn⟩ := qenter L g dt ha hqz hqb
    exact ⟨_, Raw.segD_iff (Raw.segD_pre (Seg.comp (seg_274_275 L g dt)
      (seg_bra_taken Flow.code_275 hp (by table_decide) (by simp [hq]) (by table_decide))) hn)
      (by simp)⟩
  · have hq' : v_p72 L g dt = false := by simpa using hq
    simp only [hq', Bool.false_eq_true, ↓reduceIte]
    exact ⟨_, Raw.segD_of_seg (Seg.comp (seg_274_275 L g dt) (Seg.comp
      (seg_bra_fall Flow.code_275 hp (by table_decide) (by simp [hq]) (by table_decide))
      (seg_276_278 L g dt))) (fun h => by simp at h)⟩

end
end PTX.Kernels.InklingRelDecode.Proof.ProA
