-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.MmaSteps.Ring

@[expose] public section

/-! The end of a loop trip (after commit 6): the next V use (slot increment with its wrap), the
P parity flip, the trip counter, then the next trip's V poll or the Q releases. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

theorem seg_c6a (hpre : Pre P L mem0) (hg : g < L.threads) (i tr : Nat) (base : Value)
    (pro : Nat → Value) :
    Seg kernel asms L g 2 (Flow.tcCommit_6 + 1)
      (factsAt L g (Flow.tcCommit_6 + 1) ⟨.commit 6, i, tr, base, pro⟩) (Flow.tcCommit_6 + 3)
      (Flow.factsFrom (Flow.live (Flow.tcCommit_6 + 3))
        (valueSel L g ⟨.commit 6, i, tr, base, pro⟩ 123
          (decide (kvSlot L i (2 + 2 * tr) + 1 = 6)))) := by
  intro t h
  mma_seg_s h hpre hg [valueSel]

theorem seg_c6b (hpre : Pre P L mem0) (hg : g < L.threads) (i tr : Nat) (base : Value)
    (pro : Nat → Value) (ht : tr + 1 < trips L) (b : Bool)
    (hb : decide (kvSlot L i (2 + 2 * tr) + 1 = 6) = b) :
    Seg kernel asms L g 7 (Flow.tcCommit_6 + 3)
      (Flow.factsFrom (Flow.live (Flow.tcCommit_6 + 3))
        (valueSel L g ⟨.commit 6, i, tr, base, pro⟩ 123 b))
      Flow.bra_991 (factsAt L g Flow.bra_991 ⟨.kvWait 1, i, tr + 1, base, pro⟩) := by
  intro t h
  have hw : b = true ↔ (kvBase L i + (2 + 2 * tr)) % 6 = 5 := by
    rw [← hb]; simp [kvSlot, kvUse]
  cases b
  · have hw' : (kvBase L i + (2 + 2 * tr)) % 6 ≠ 5 := fun h => absurd (hw.mpr h) (by decide)
    mma_seg_s h hpre hg [valueSel, kvUse, pPar_succ, Nat.add_one_ne_zero,
      xor_bit_zero (kvPar_lt L i (2 + 2 * tr)), xor_one_lt2 (pPar_lt L i tr)]
  · have hw' : (kvBase L i + (2 + 2 * tr)) % 6 = 5 := hw.mp rfl
    mma_seg_s h hpre hg [valueSel, kvUse, pPar_succ, Nat.add_one_ne_zero,
      xor_bit_one (kvPar_lt L i (2 + 2 * tr)), xor_one_lt2 (pPar_lt L i tr)]

/-- Back to the next trip's V poll. -/
theorem seg_c6loop (hpre : Pre P L mem0) (hg : g < L.threads) (i tr : Nat) (base : Value)
    (pro : Nat → Value) :
    Seg kernel asms L g 3 (Flow.bra_745 + 3)
      (factsAt L g Flow.bra_991 ⟨.kvWait 1, i, tr, base, pro⟩)
      (Site.kvWait 1).pc (facts L g ⟨.kvWait 1, i, tr, base, pro⟩) := by
  intro t h
  mma_seg_s h hpre hg [kvUse]

/-- After the last commit of a loop trip: the next trip's V poll, or the Q releases. -/
theorem seg_c6tail (hpre : Pre P L mem0) (hg : g < L.threads) (i tr : Nat) (base : Value)
    (pro : Nat → Value) (ht : tr + 1 < trips L) :
    Seg kernel asms L g (if tr + 1 < trips L - 1 then 13 else 10) (Flow.tcCommit_6 + 1)
      (factsAt L g (Flow.tcCommit_6 + 1) ⟨.commit 6, i, tr, base, pro⟩)
      (afterCommit L g ⟨.commit 6, i, tr, base, pro⟩ 6).site.pc
      (facts L g (afterCommit L g ⟨.commit 6, i, tr, base, pro⟩ 6)) := by
  intro t h
  have hab := Seg.comp (seg_c6a hpre hg i tr base pro)
    (seg_c6b hpre hg i tr base pro ht _ rfl)
  have hp : (124, Value.pred (decide (tr + 1 ≠ trips L - 1))) ∈
      factsAt L g Flow.bra_991 ⟨.kvWait 1, i, tr + 1, base, pro⟩ :=
    (show valueOf L g ⟨.kvWait 1, i, tr + 1, base, pro⟩ 124 =
      .pred (decide (tr + 1 ≠ trips L - 1)) by mma_values) ▸ Flow.mem_factsFrom (by table_decide)
  have hv : valueOf L g ⟨.elC 7, i, tr + 1, base, pro⟩ =
      valueOf L g ⟨.kvWait 1, i, tr + 1, base, pro⟩ := rfl
  by_cases hn : tr + 1 < trips L - 1
  · have hp' : (124, Value.pred true) ∈
        factsAt L g Flow.bra_991 ⟨.kvWait 1, i, tr + 1, base, pro⟩ := by
      have : tr + 1 ≠ trips L - 1 := by omega
      simpa [this] using hp
    obtain ⟨t', hr, ht'⟩ := (Seg.comp (Seg.comp hab (seg_bra Flow.code_991 hp'))
      (seg_c6loop hpre hg i (tr + 1) base pro)) t h
    refine ⟨t', by simpa [hn] using hr, ?_⟩
    simp only [afterCommit, hn, ↓reduceIte]
    exact ht'
  · have hp' : (124, Value.pred false) ∈
        factsAt L g Flow.bra_991 ⟨.kvWait 1, i, tr + 1, base, pro⟩ := by
      have : tr + 1 = trips L - 1 := by omega
      simpa [this] using hp
    obtain ⟨t', hr, ht'⟩ := (Seg.comp hab (seg_bra Flow.code_991 hp')) t h
    refine ⟨t', by simpa [hn] using hr, ?_⟩
    simp only [afterCommit, hn, ↓reduceIte]
    refine At.mono ht' ?_
    show Holds _ (Flow.factsFrom (Flow.live Flow.elect_45) _)
    rw [hv]
    exact Flow.holds_factsFrom_mono ht'.2.2.2.2 (by table_decide)

theorem afterCommit6_inv {L : Launch} {g : Nat} {d : D} (hi : Inv L g d)
    (hs : ItemSite d.site) (ht : d.t + 1 < trips L) : Inv L g (afterCommit L g d 6) := by
  simp only [afterCommit]
  split_ifs with h
  · exact ⟨.inr (by omega), fun _ => hi.i hs, show d.t + 1 + 1 < trips L by omega⟩
  · exact ⟨.inr (by omega), fun _ => hi.i hs, show d.t + 1 + 1 = trips L by omega⟩

theorem afterCommit6_sub {L : Launch} {g : Nat} {d : D} :
    (afterCommit L g d 6).site.sub = 0 := by
  simp only [afterCommit]
  split_ifs <;> rfl

theorem stepOk_commit6 (hpre : Pre P L mem0) (hg : g < L.threads) {pro : Nat → Value}
    (i tr : Nat) (base : Value) (pr : Nat → Value) :
    (code asms L g pro).StepOk ⟨.commit 6, i, tr, base, pr⟩ :=
  Code.step_issue Flow.code_tcCommit_6 (fun hf => fires_tcCommit hf) (fun _ => rfl) rfl rfl
    ⟨fun hi => by
        exact ⟨_, Seg.weaken_start (seg_c6tail hpre hg i tr base pr hi.1.trip)
          fun _ hR => Flow.holds_factsFrom_mono hR (by table_decide)⟩,
      afterCommit6_sub, rfl,
      fun hi => ⟨afterCommit6_inv hi.1 trivial hi.1.trip, baseOk_afterCommit 6⟩⟩

theorem stepOk_elC6 (hpre : Pre P L mem0) (hg : g < L.threads) {pro : Nat → Value}
    (i tr : Nat) (base : Value) (pr : Nat → Value) :
    (code asms L g pro).StepOk ⟨.elC 6, i, tr, base, pr⟩ :=
  Code.step_elect (dl := ⟨.commit 6, i, tr, base, pr⟩)
    (ds := afterCommit L g ⟨.commit 6, i, tr, base, pr⟩ 6) Flow.code_elect_44 (by fact_free)
    (by rintro r ⟨⟩; exact ⟨by fact_free, by decide⟩) (fun _ _ _ h => by next_simp [next, h])
    (fun _ _ _ h => by next_simp [next, afterCommit, h]) rfl rfl
    (fun _ => ⟨fun _ => by
        site_norm; dsimp only [Code.electFacts]; seg_auto using mma_close hpre hg,
      rfl, rfl, by mma_inv⟩)
    (fun _ => ⟨fun hi => by
        dsimp only [Code.electFacts]
        exact ⟨_, Seg.comp (m := 2) (by mma_close hpre hg)
          (seg_c6tail hpre hg i tr base pr hi.1.trip)⟩,
      afterCommit6_sub, rfl, fun hi => ⟨afterCommit6_inv (d := ⟨.commit 6, i, tr, base, pr⟩)
        ⟨hi.1.t, fun _ => hi.1.i trivial, hi.1.trip⟩ trivial hi.1.trip, baseOk_afterCommit 6⟩⟩)

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Mma
