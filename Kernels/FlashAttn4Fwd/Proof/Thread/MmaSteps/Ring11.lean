-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.MmaSteps.Ring

@[expose] public section

/-! The end of an item (after commit 11): the next item's first KV use and parities, the item
counter, then the next item's Q poll or the end. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

theorem seg_c11a (hpre : Pre P L mem0) (hg : g < L.threads) (i tr : Nat) (base : Value)
    (pro : Nat → Value) :
    Seg kernel asms L g 2 (Flow.tcCommit_11 + 1)
      (factsAt L g (Flow.tcCommit_11 + 1) ⟨.commit 11, i, tr, base, pro⟩) (Flow.tcCommit_11 + 3)
      (Flow.factsFrom (Flow.live (Flow.tcCommit_11 + 3))
        (valueSel L g ⟨.commit 11, i, tr, base, pro⟩ 135
          (decide (kvSlot L i (1 + 2 * tr) + 1 = 6)))) := by
  intro t h
  mma_seg_s h hpre hg [valueSel]

theorem seg_c11b (hpre : Pre P L mem0) (hg : g < L.threads) (i tr : Nat) (base : Value)
    (pro : Nat → Value) (ht : tr + 1 = trips L) (hw : work L g i < totOf L) (b : Bool)
    (hb : decide (kvSlot L i (1 + 2 * tr) + 1 = 6) = b) :
    Seg kernel asms L g 7 (Flow.tcCommit_11 + 3)
      (Flow.factsFrom (Flow.live (Flow.tcCommit_11 + 3))
        (valueSel L g ⟨.commit 11, i, tr, base, pro⟩ 135 b))
      Flow.bra_1115 (factsAt L g Flow.bra_1115 ⟨.qWait 0, i + 1, 0, base, pro⟩) := by
  intro t h
  have hw2 : (kvBase L i + (1 + 2 * tr)) % 6 = 5 ↔ b = true := by
    rw [← hb]; simp [kvSlot, kvUse]
  have hi2 : i % 2 < 2 := Nat.mod_lt _ (by decide)
  cases b
  · have hw' : (kvBase L i + (1 + 2 * tr)) % 6 ≠ 5 := fun h => absurd (hw2.mp h) (by decide)
    mma_seg_s h hpre hg [valueSel, kvUse, kvBase_succ, pPar_next ht, work_succ,
      xor_bit_zero (kvPar_lt L i (1 + 2 * tr)), xor_one_lt2 (pPar_lt L i tr), xor_one_lt2 hi2]
  · have hw' : (kvBase L i + (1 + 2 * tr)) % 6 = 5 := hw2.mpr rfl
    mma_seg_s h hpre hg [valueSel, kvUse, kvBase_succ, pPar_next ht, work_succ,
      xor_bit_one (kvPar_lt L i (1 + 2 * tr)), xor_one_lt2 (pPar_lt L i tr), xor_one_lt2 hi2]

/-- Back to the test for the odd CTA (the leader does not branch). -/
theorem seg_c11loop (hpre : Pre P L mem0) (hg : g < L.threads) (i : Nat) (base : Value)
    (pro : Nat → Value) :
    Seg kernel asms L g 1 (Flow.bra_594 - 1)
      (factsAt L g Flow.bra_1115 ⟨.qWait 0, i, 0, base, pro⟩)
      Flow.bra_594 (factsAt L g Flow.bra_594 ⟨.qWait 0, i, 0, base, pro⟩) := by
  intro t h
  mma_seg_s h hpre hg

/-- After the item's last commit: the next item's Q poll, or the end. -/
theorem seg_c11tail (hpre : Pre P L mem0) (hg : g < L.threads) (i tr : Nat) (base : Value)
    (pro : Nat → Value) (ht : tr + 1 = trips L) (hw : work L g i < totOf L)
    (hr0 : rank L g = 0) :
    Seg kernel asms L g (if work L g (i + 1) < totOf L then 12 else 10) (Flow.tcCommit_11 + 1)
      (factsAt L g (Flow.tcCommit_11 + 1) ⟨.commit 11, i, tr, base, pro⟩)
      (afterCommit L g ⟨.commit 11, i, tr, base, pro⟩ 11).site.pc
      (facts L g (afterCommit L g ⟨.commit 11, i, tr, base, pro⟩ 11)) := by
  intro t h
  have hab := Seg.comp (seg_c11a hpre hg i tr base pro)
    (seg_c11b hpre hg i tr base pro ht hw _ rfl)
  have hp : (136, Value.pred (decide (work L g (i + 1) < totOf L))) ∈
      factsAt L g Flow.bra_1115 ⟨.qWait 0, i + 1, 0, base, pro⟩ :=
    (show valueOf L g ⟨.qWait 0, i + 1, 0, base, pro⟩ 136 =
      .pred (decide (work L g (i + 1) < totOf L)) by mma_values) ▸
      Flow.mem_factsFrom (by table_decide)
  by_cases hn : work L g (i + 1) < totOf L
  · have hp' : (136, Value.pred true) ∈
        factsAt L g Flow.bra_1115 ⟨.qWait 0, i + 1, 0, base, pro⟩ := by
      simpa [hn] using hp
    have h105 : (105, Value.pred false) ∈
        factsAt L g Flow.bra_594 ⟨.qWait 0, i + 1, 0, base, pro⟩ :=
      (show valueOf L g ⟨.qWait 0, i + 1, 0, base, pro⟩ 105 = .pred false by
        mma_values; simp [hr0]) ▸ Flow.mem_factsFrom (by table_decide)
    obtain ⟨t', hr, ht'⟩ := (Seg.comp (Seg.comp (Seg.comp hab (seg_bra Flow.code_1115 hp'))
      (seg_c11loop hpre hg (i + 1) base pro)) (seg_bra Flow.code_594 h105)) t h
    refine ⟨t', by simpa [hn] using hr, ?_⟩
    simp only [afterCommit, hn, ↓reduceIte]
    exact At.mono ht' (Flow.holds_factsFrom_mono ht'.2.2.2.2 (by table_decide))
  · have hp' : (136, Value.pred false) ∈
        factsAt L g Flow.bra_1115 ⟨.qWait 0, i + 1, 0, base, pro⟩ := by
      simpa [hn] using hp
    have hv : valueOf L g ⟨.relinquish, i + 1, 0, base, pro⟩ =
        valueOf L g ⟨.qWait 0, i + 1, 0, base, pro⟩ := rfl
    obtain ⟨t', hr, ht'⟩ := (Seg.comp hab (seg_bra Flow.code_1115 hp')) t h
    refine ⟨t', by simpa [hn] using hr, ?_⟩
    simp only [afterCommit, hn, ↓reduceIte]
    refine At.mono ht' ?_
    show Holds _ (Flow.factsFrom (Flow.live Flow.tmemRelinquish_0) _)
    rw [hv]
    exact Flow.holds_factsFrom_mono ht'.2.2.2.2 (by table_decide)

theorem afterCommit11_inv {L : Launch} {g : Nat} {d : D} (hr0 : rank L g = 0) :
    Inv L g (afterCommit L g d 11) := by
  simp only [afterCommit]
  split_ifs with h
  · exact ⟨.inl rfl, fun _ => ⟨h, hr0⟩, rfl⟩
  · exact ⟨.inl rfl, nofun, trivial⟩

theorem afterCommit11_sub {L : Launch} {g : Nat} {d : D} :
    (afterCommit L g d 11).site.sub = 0 := by
  simp only [afterCommit]
  split_ifs <;> rfl

theorem stepOk_commit11 (hpre : Pre P L mem0) (hg : g < L.threads) {pro : Nat → Value}
    (i tr : Nat) (base : Value) (pr : Nat → Value) :
    (code asms L g pro).StepOk ⟨.commit 11, i, tr, base, pr⟩ :=
  Code.step_issue Flow.code_tcCommit_11 (fun hf => fires_tcCommit hf) (fun _ => rfl) rfl rfl
    ⟨fun hi => by
        exact ⟨_, Seg.weaken_start (seg_c11tail hpre hg i tr base pr hi.1.trip (hi.1.i trivial).1
          (hi.1.i trivial).2)
          fun _ hR => Flow.holds_factsFrom_mono hR (by table_decide)⟩,
      afterCommit11_sub, rfl,
      fun hi => ⟨afterCommit11_inv (hi.1.i trivial).2, baseOk_afterCommit 11⟩⟩

theorem stepOk_elC11 (hpre : Pre P L mem0) (hg : g < L.threads) {pro : Nat → Value}
    (i tr : Nat) (base : Value) (pr : Nat → Value) :
    (code asms L g pro).StepOk ⟨.elC 11, i, tr, base, pr⟩ :=
  Code.step_elect (dl := ⟨.commit 11, i, tr, base, pr⟩)
    (ds := afterCommit L g ⟨.commit 11, i, tr, base, pr⟩ 11) Flow.code_elect_51 (by fact_free)
    (by rintro r ⟨⟩; exact ⟨by fact_free, by decide⟩) (fun _ _ _ h => by next_simp [next, h])
    (fun _ _ _ h => by next_simp [next, afterCommit, h]) rfl rfl
    (fun _ => ⟨fun _ => by
        site_norm; dsimp only [Code.electFacts]; seg_auto using mma_close hpre hg,
      rfl, rfl, by mma_inv⟩)
    (fun _ => ⟨fun hi => by
        dsimp only [Code.electFacts]
        exact ⟨_, Seg.comp (m := 2) (by mma_close hpre hg)
          (seg_c11tail hpre hg i tr base pr hi.1.trip (hi.1.i trivial).1
          (hi.1.i trivial).2)⟩,
      afterCommit11_sub, rfl,
      fun hi => ⟨afterCommit11_inv (hi.1.i trivial).2, baseOk_afterCommit 11⟩⟩)

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Mma
