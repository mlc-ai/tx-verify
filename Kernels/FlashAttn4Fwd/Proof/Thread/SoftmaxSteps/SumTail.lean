-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.SoftmaxSteps.Signed

@[expose] public section

/-! # After a tile's row sum

After the row sum of a tile the thread either enters the next loop trip (`loop_entry`: the trip
counter, the scale loaded again, the Tensor Memory addresses of the stage, to the score poll)
or leaves the loop (`lSt_entry`: the statistics word's address, to the store of `l`). Both are
entered by a branch, with the facts of the branch's `pc` (`facts_sub`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

theorem lookup_none {ex : List (Nat × Value)} {r : Nat} (h : r ∉ ex.map Prod.fst) :
    ex.lookup r = none := by
  induction ex with
  | nil => rfl
  | cons p ex ih =>
    obtain ⟨k, v⟩ := p
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp only [List.lookup_cons]
    rw [show (r == k) = false from beq_false_of_ne h.1]
    exact ih h.2

/-- The row's word in stage 1, `128 ||| (x & 127)` (after the normal form of the mask). -/
theorem row_word (x : Nat) : (128 ||| x % 128 / 1 * 1 % 4294967296) = 128 + x % 128 := by
  rw [Nat.div_one, Nat.mul_one, Nat.mod_eq_of_lt (show x % 128 < 4294967296 by omega)]
  exact lor_eq_add (k := 7) (by norm_num) (Nat.mod_lt _ (by norm_num))

/-- The facts at `pc` with extra values `ex` (on the registers `ks`) give the facts at `pc'`
when every register live at `pc'` is live at `pc` and has no extra value. -/
theorem facts_sub {pc pc' : Nat} {d : D} {ex : List (Nat × Value)} {ks : List Nat}
    {R : Nat → Option Value} (hks : ex.map Prod.fst = ks)
    (hl : ∀ r ∈ Flow.live pc', r ∈ Flow.live pc ∧ r ∉ ks)
    (h : Holds R (factsX L g pc d ex)) : Holds R (factsAt L g pc' d) := by
  subst hks
  refine holds_of_pointwise fun r hr => ?_
  obtain ⟨h1, h2⟩ := hl r hr
  have := holds_mem h (List.mem_map.mpr ⟨r, h1, rfl⟩)
  simpa [valueX, lookup_none h2] using this

/-- A segment from the facts at `pc'` started from the facts at `pc` with extra values. -/
theorem Seg.sub {n s b pc pc' : Nat} {d : D} {ex : List (Nat × Value)} {ks : List Nat}
    {G : List (Nat × Value)} (hl : ∀ r ∈ Flow.live pc', r ∈ Flow.live pc ∧ r ∉ ks)
    (hs : Seg kernel asms L g n s (factsAt L g pc' d) b G) (hks : ex.map Prod.fst = ks := by rfl) :
    Seg kernel asms L g n s (factsX L g pc d ex) b G :=
  Seg.weaken_start hs fun _ h => facts_sub hks hl h

/-- A segment from the facts at `pc'` started from the facts at `pc`. -/
theorem Seg.subAt {n s b pc pc' : Nat} {d : D} {G : List (Nat × Value)}
    (hl : ∀ r ∈ Flow.live pc', r ∈ Flow.live pc)
    (hs : Seg kernel asms L g n s (factsAt L g pc' d) b G) :
    Seg kernel asms L g n s (factsAt L g pc d) b G :=
  Seg.weaken_start hs fun _ h => holds_of_pointwise fun r hr =>
    holds_mem h (List.mem_map.mpr ⟨r, hl r hr, rfl⟩)

/-- An item has at least one tile. -/
theorem trips_pos (hpre : Pre P L mem0) : 1 ≤ trips L := by
  have := hpre.skDiv128
  have := hpre.skPos
  simp only [trips, Work.n, Work.sk, skOf_eq hpre]
  omega

/-! The tile indices of the sites around a row sum. -/

theorem tileIdx_statsW1 (i t : Nat) (s : Nat → Value) (m l : Value) :
    tileIdx L ⟨.statsW 1, i, t, s, m, l⟩ = trips L * i := by
  simp [tileIdx, Site.tile0]

theorem tileIdx_statsW2 (i t : Nat) (s : Nat → Value) (m l : Value) :
    tileIdx L ⟨.statsW 2, i, t, s, m, l⟩ = trips L * i + (t + 1) := by
  simp [tileIdx, Site.tile0]

theorem tileIdx_sW (i t : Nat) (s : Nat → Value) (m l : Value) :
    tileIdx L ⟨.sW true, i, t, s, m, l⟩ = trips L * i + (t + 1) := by
  simp [tileIdx, Site.tile0]

theorem tileIdx_lSt (i t : Nat) (s : Nat → Value) (m l : Value) :
    tileIdx L ⟨.lSt, i, t, s, m, l⟩ = trips L * i + (t + 1) := by
  simp [tileIdx, Site.tile0]

/-- Entering a loop trip: the scale, the stage's selection, to the score poll. -/
theorem loop_entry (hpre : Pre P L mem0) (hw : warpOf L g < 8) (i tt : Nat) (s : Nat → Value)
    (m l : Value) :
    Seg kernel asms L g (1 + (1 + 14)) 2709 (factsAt L g 2709 ⟨.sW true, i, tt, s, m, l⟩) 2725
      (factsAt L g 2725 ⟨.sW true, i, tt, s, m, l⟩) := by
  have h1 : Seg kernel asms L g 1 2709 (factsAt L g 2709 ⟨.sW true, i, tt, s, m, l⟩) 2710
      (factsAt L g 2710 ⟨.sW true, i, tt, s, m, l⟩) :=
    fun _ h => ld_scale hpre Flow.code_2709 h
      (by simp only [valueOf, ctrlValues, PTX.Flow.lookupLit, Option.getD_some])
      (by table_decide) (by decide +kernel) (by seg_free_pc)
  refine Seg.comp h1 (Seg.cases (decide (3 < warpOf L g) = true) (fun hb => ?_) (fun hb => ?_))
  · have h2 : Seg kernel asms L g 1 2710 (factsAt L g 2710 ⟨.sW true, i, tt, s, m, l⟩) 2711
        (factsX L g 2711 ⟨.sW true, i, tt, s, m, l⟩ [(280, .pred true)]) := by
      intro t h
      simp only [decide_eq_true_eq] at hb
      sm_seg h hpre
    have h3 : Seg kernel asms L g 14 2711
        (factsX L g 2711 ⟨.sW true, i, tt, s, m, l⟩ [(280, .pred true)]) 2725
        (factsAt L g 2725 ⟨.sW true, i, tt, s, m, l⟩) := by
      intro t h
      simp only [decide_eq_true_eq] at hb
      sm_segs h hpre [tidOf, hpre.block]
    exact Seg.comp h2 h3
  · have h2 : Seg kernel asms L g 1 2710 (factsAt L g 2710 ⟨.sW true, i, tt, s, m, l⟩) 2711
        (factsX L g 2711 ⟨.sW true, i, tt, s, m, l⟩ [(280, .pred false)]) := by
      intro t h
      simp only [decide_eq_true_eq] at hb
      sm_seg h hpre
    have h3 : Seg kernel asms L g 14 2711
        (factsX L g 2711 ⟨.sW true, i, tt, s, m, l⟩ [(280, .pred false)]) 2725
        (factsAt L g 2725 ⟨.sW true, i, tt, s, m, l⟩) := by
      intro t h
      simp only [decide_eq_true_eq] at hb
      sm_segs h hpre [tidOf, hpre.block]
    exact Seg.comp h2 h3

/-- Leaving the loop: the statistics word's address, to the store of `l`. -/
theorem lSt_entry (hpre : Pre P L mem0) (hw : warpOf L g < 8) (i tt : Nat) (s : Nat → Value)
    (m l : Value) :
    Seg kernel asms L g (1 + 6) 3729 (factsAt L g 3729 ⟨.lSt, i, tt, s, m, l⟩) 3736
      (factsAt L g 3736 ⟨.lSt, i, tt, s, m, l⟩) := by
  refine Seg.cases (decide (3 < warpOf L g) = true) (fun hb => ?_) (fun hb => ?_)
  · have h2 : Seg kernel asms L g 1 3729 (factsAt L g 3729 ⟨.lSt, i, tt, s, m, l⟩) 3730
        (factsX L g 3730 ⟨.lSt, i, tt, s, m, l⟩ [(287, .pred true)]) := by
      intro t h
      simp only [decide_eq_true_eq] at hb
      sm_seg h hpre
    have h3 : Seg kernel asms L g 6 3730
        (factsX L g 3730 ⟨.lSt, i, tt, s, m, l⟩ [(287, .pred true)]) 3736
        (factsAt L g 3736 ⟨.lSt, i, tt, s, m, l⟩) := by
      intro t h
      simp only [decide_eq_true_eq] at hb
      have hb' : 3 < g % 512 / 32 := by
        simpa only [warpOf, hpre.block] using hb
      have hw' : g % 512 / 32 < 8 := by simpa only [warpOf, hpre.block] using hw
      sm_segs h hpre [tidOf, warpOf, hpre.block, row_word, Nat.zero_or]
    exact Seg.comp h2 h3
  · have h2 : Seg kernel asms L g 1 3729 (factsAt L g 3729 ⟨.lSt, i, tt, s, m, l⟩) 3730
        (factsX L g 3730 ⟨.lSt, i, tt, s, m, l⟩ [(287, .pred false)]) := by
      intro t h
      simp only [decide_eq_true_eq] at hb
      sm_seg h hpre
    have h3 : Seg kernel asms L g 6 3730
        (factsX L g 3730 ⟨.lSt, i, tt, s, m, l⟩ [(287, .pred false)]) 3736
        (factsAt L g 3736 ⟨.lSt, i, tt, s, m, l⟩) := by
      intro t h
      simp only [decide_eq_true_eq] at hb
      have hb' : ¬ 3 < g % 512 / 32 := by
        simpa only [warpOf, hpre.block] using hb
      have hw' : g % 512 / 32 < 8 := by simpa only [warpOf, hpre.block] using hw
      sm_segs h hpre [tidOf, warpOf, hpre.block, row_word, Nat.zero_or]
    exact Seg.comp h2 h3

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Softmax
