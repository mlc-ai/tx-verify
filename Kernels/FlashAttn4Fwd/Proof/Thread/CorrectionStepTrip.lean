-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.CorrectionStepBase

@[expose] public section

/-! # The entry to the trips of an item

After stage 1's first barrier generation `@%p298 bra` skips the loop when the item has one
trip (`%p298 = (n - 1 < 1)`, a fact of the table): the thread reaches the credit after the loop
(`mov.b32 %r2918, 1` between); otherwise the loop counter is set (`%r3603 = -n`) and the first
trip's barrier is reached. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Correction
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- Stage 1's first barrier generation, then the loop or the credit after it. -/
theorem step_sync1First {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {d : D} {t u : TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0)
    (hs : d.site = .sync 1 .first) (hi : Inv L g d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bar_5)
  obtain rfl := fires_async_next (show AsyncAdvancesOp (.barSyncN _ _ _) from trivial) hf
  have hit : i < items L g := hi.item rfl
  obtain ⟨t2, hr2, ht2⟩ := run_bra (K := kernel) (A := asms) (L := L) (g := g)
    (show kernel.code[Flow.bra_3850]? = _ from Flow.code_3850) (decide (trips L ≤ 1))
    (At.next h) (holds_mem h.2.2.2.2 (List.mem_map.mpr ⟨298, by table_decide, by
      simp only [valueOf, values, chunkValues, loadValues, PTX.Flow.lookupLit,
        Option.getD_some]⟩))
    asms_localRule_none
  by_cases hn : trips L ≤ 1
  · simp only [hn, decide_true, ↓reduceIte] at ht2
    obtain ⟨t3, hr3, ht3⟩ : ∃ t3, run kernel asms L g 1 t2 = some t3 ∧
        At t3 (Site.credit 3).pc (facts L g ⟨.credit 3, i, tt, aw, a, o⟩) := by
      corr_seg ht2 hpre
    exact step_of_run (d' := ⟨.credit 3, i, tt, aw, a, o⟩) (by simp [next, hn])
      (inv_same (d := ⟨.sync 1 .first, i, tt, aw, a, o⟩) _ hi (by simp [Site.inItem])
        (.inl (by simp [Site.inItem])) (by simp [Site.inTrip]) (by simp [Site.rescale])
        (by simp)) rfl ⟨_, t3, run_comp hr2 hr3, ht3⟩
  · simp only [hn, decide_false, Bool.false_eq_true, ↓reduceIte] at ht2
    obtain ⟨t3, hr3, ht3⟩ : ∃ t3, run kernel asms L g 1 t2 = some t3 ∧
        At t3 (Site.sync 0 .loop).pc (facts L g ⟨.sync 0 .loop, i, 0, aw, a, o⟩) := by
      corr_seg ht2 hpre
    refine step_of_run (d' := ⟨.sync 0 .loop, i, 0, aw, a, o⟩) (by simp [next, hn])
      ⟨fun _ => hit, fun h' => by simp [Site.inItem] at h', fun h' => by simp at h',
        fun _ => by simp only; omega, fun h' => by simp [Site.rescale] at h'⟩ rfl
      ⟨_, t3, run_comp hr2 hr3, ht3⟩

/-- The trip count is below `2 ^ 31`. -/
theorem trips_lt {P : Params} {L : Launch} {mem0 : Mem0} (hpre : Pre P L mem0) :
    trips L < 2 ^ 31 := by
  have h1 := skOf_eq hpre
  have h2 := hpre.skRange
  unfold trips
  omega

/-- The loop test after trip `t` (`%r3603 + 1 ≠ -1`): another trip follows. -/
theorem trip_cmp (n t : Nat) (hn : n < 2 ^ 31) (ht : t + 1 < n) :
    PTX.compare .ne .b 32 (truncBits 32 (truncBits 32 (truncBits 32
      (BitVec.ofNat 64 ((neg32 n + t) % 2 ^ 32)) + truncBits 32 (BitVec.ofInt 64 1))))
      (truncBits 32 (BitVec.ofInt 64 (-1))) = decide (t + 2 < n) := by
  nf_simp [PTX.compare, neg32]
  simp only [decide_eq_decide]
  omega

/-- Stage 0's credit at the end of a trip, then the next trip (`add.s32 %r3603, 1`,
`setp.ne … -1`, `@%p303 bra`) or the credit after the loop. -/
theorem step_credit2 {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {d : D} {t u : TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0)
    (hs : d.site = .credit 2) (hi : Inv L g d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i, tt, aw, a, o⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_20)
  obtain ⟨rfl, -⟩ := fires_arrive_state hf
  have h1 := At.clear_state h
    (not_mem_factsFrom (show 5065 ∉ Flow.live Flow.mbarArrive_20 ++ [] by table_decide))
  have hit : i < items L g := hi.item rfl
  have htr : tt + 1 < trips L := hi.trip rfl
  have hn := trips_lt hpre
  obtain ⟨t2, hr2, ht2⟩ : ∃ t2,
      run kernel asms L g 2 (PTX.next (mbarStateDest t (some 5065))) = some t2 ∧
      At t2 Flow.bra_4292 (factsX L g Flow.bra_4292 ⟨.sync 0 .loop, i, tt + 1, aw, a, o⟩
        [(303, .pred (decide (tt + 2 < trips L)))]) := by
    seg_fp h1 using
      try simp only [valueX, valueOf, values, chunkValues, loadValues, PTX.Flow.lookupLit,
        Option.getD_some, Option.getD_none, List.lookup_cons, List.lookup_nil, Nat.reduceBEq]
      all_goals first
        | seg_close [neg32]
        | rw [trip_cmp _ _ hn htr]
  obtain ⟨t3, hr3, ht3⟩ := run_bra (K := kernel) (A := asms) (L := L) (g := g)
    (show kernel.code[Flow.bra_4292]? = _ from Flow.code_4292) (decide (tt + 2 < trips L)) ht2
    (holds_mem ht2.2.2.2.2 (List.mem_map.mpr ⟨303, by table_decide, by simp [valueX]⟩))
    asms_localRule_none
  by_cases hl : tt + 2 < trips L
  · simp only [hl, decide_true, ↓reduceIte] at ht3
    obtain ⟨t4, hr4, ht4⟩ : ∃ t4, run kernel asms L g 0 t3 = some t4 ∧
        At t4 (Site.sync 0 .loop).pc (facts L g ⟨.sync 0 .loop, i, tt + 1, aw, a, o⟩) := by
      corr_seg ht3 hpre
    refine step_of_run (d' := ⟨.sync 0 .loop, i, tt + 1, aw, a, o⟩)
      (by simp [next, afterTrip, hl])
      ⟨fun _ => hit, fun h' => by simp [Site.inItem] at h', fun h' => by simp at h',
        fun _ => by simp only; omega, fun h' => by simp [Site.rescale] at h'⟩ rfl
      ⟨_, t4, run_comp (run_comp hr2 hr3) hr4, ht4⟩
  · simp only [hl, decide_false, Bool.false_eq_true, ↓reduceIte] at ht3
    obtain ⟨t4, hr4, ht4⟩ : ∃ t4, run kernel asms L g 1 t3 = some t4 ∧
        At t4 (Site.credit 3).pc (facts L g ⟨.credit 3, i, tt, aw, a, o⟩) := by
      corr_seg ht3 hpre
    exact step_of_run (d' := ⟨.credit 3, i, tt, aw, a, o⟩) (by simp [next, afterTrip, hl])
      (inv_same (d := ⟨.credit 2, i, tt, aw, a, o⟩) _ hi (by simp [Site.inItem])
        (.inl (by simp [Site.inItem])) (by simp [Site.inTrip]) (by simp [Site.rescale])
        (by simp)) rfl ⟨_, t4, run_comp (run_comp hr2 hr3) hr4, ht4⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Correction
