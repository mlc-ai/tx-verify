-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.MmaSteps.Base

@[expose] public section

/-! The ring advances of the MMA warp's local code: after the release of the item's first K
(commit 2) the next V use, the test for a loop trip. The slot increment selects on whether the
slot wraps (`selp` on `slot + 1 = 6`), which the evaluation cannot decide: the segment is cut
there and the selection's predicate is a case. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- From the release of the first K to the wrap test of the next slot. -/
theorem seg_c2a (hpre : Pre P L mem0) (hg : g < L.threads) (i tr : Nat) (base : Value)
    (pro : Nat → Value) :
    Seg kernel asms L g 4 (Flow.tcCommit_2 + 1)
      (factsAt L g (Flow.tcCommit_2 + 1) ⟨.commit 2, i, tr, base, pro⟩) (Flow.tcCommit_2 + 5)
      (Flow.factsFrom (Flow.live (Flow.tcCommit_2 + 5))
        (valueSel L g ⟨.commit 2, i, tr, base, pro⟩ 113 (decide (kvSlot L i 0 + 1 = 6)))) := by
  intro t h
  mma_seg_s h hpre hg [valueSel]

/-- From the wrap test to the test for a loop trip. -/
theorem seg_c2b (hpre : Pre P L mem0) (hg : g < L.threads) (i : Nat) (base : Value)
    (pro : Nat → Value) (b : Bool) (hb : decide (kvSlot L i 0 + 1 = 6) = b) :
    Seg kernel asms L g 4 (Flow.tcCommit_2 + 5)
      (Flow.factsFrom (Flow.live (Flow.tcCommit_2 + 5))
        (valueSel L g ⟨.commit 2, i, 0, base, pro⟩ 113 b))
      Flow.bra_745 (factsAt L g Flow.bra_745 ⟨.kvWait 1, i, 0, base, pro⟩) := by
  intro t h
  have hw : b = true ↔ kvBase L i % 6 = 5 := by
    rw [← hb]; simp [kvSlot, kvUse]
  cases b
  · have hw' : kvBase L i % 6 ≠ 5 := fun h => absurd (hw.mpr h) (by decide)
    mma_seg_s h hpre hg [valueSel, kvUse, xor_bit_zero (kvPar_lt L i 0)]
  · have hw' : kvBase L i % 6 = 5 := hw.mp rfl
    mma_seg_s h hpre hg [valueSel, kvUse, xor_bit_one (kvPar_lt L i 0)]

/-- A loop trip follows: to the first V poll. -/
theorem seg_c2loop (hpre : Pre P L mem0) (hg : g < L.threads) (i : Nat) (base : Value)
    (pro : Nat → Value) :
    Seg kernel asms L g 5 (Flow.bra_745 + 1) (factsAt L g Flow.bra_745 ⟨.kvWait 1, i, 0, base, pro⟩)
      (Site.kvWait 1).pc (facts L g ⟨.kvWait 1, i, 0, base, pro⟩) := by
  intro t h
  mma_seg_s h hpre hg [kvUse]

/-- After the release of the item's first K: the first loop trip's V poll, or (one trip) the
Q releases. -/
theorem seg_c2tail (hpre : Pre P L mem0) (hg : g < L.threads) (i : Nat) (base : Value)
    (pro : Nat → Value) :
    Seg kernel asms L g (if trips L - 1 < 1 then 9 else 14) (Flow.tcCommit_2 + 1)
      (factsAt L g (Flow.tcCommit_2 + 1) ⟨.commit 2, i, 0, base, pro⟩)
      (afterCommit L g ⟨.commit 2, i, 0, base, pro⟩ 2).site.pc
      (facts L g (afterCommit L g ⟨.commit 2, i, 0, base, pro⟩ 2)) := by
  intro t h
  have hab := Seg.comp (seg_c2a hpre hg i 0 base pro)
    (seg_c2b hpre hg i base pro _ rfl)
  have hp : (112, Value.pred (decide (trips L - 1 < 1))) ∈
      factsAt L g Flow.bra_745 ⟨.kvWait 1, i, 0, base, pro⟩ :=
    (show valueOf L g ⟨.kvWait 1, i, 0, base, pro⟩ 112 = .pred (decide (trips L - 1 < 1))
      by mma_values) ▸
      Flow.mem_factsFrom (by table_decide)
  have hv : valueOf L g ⟨.elC 7, i, 0, base, pro⟩ = valueOf L g ⟨.kvWait 1, i, 0, base, pro⟩ :=
    rfl
  by_cases hn : trips L - 1 < 1
  · have hp' : (112, Value.pred true) ∈ factsAt L g Flow.bra_745 ⟨.kvWait 1, i, 0, base, pro⟩ := by
      simpa [hn] using hp
    obtain ⟨t', hr, ht'⟩ := (Seg.comp hab (seg_bra Flow.code_745 hp')) t h
    refine ⟨t', by simpa [hn] using hr, ?_⟩
    simp only [afterCommit, hn, ↓reduceIte]
    refine At.mono ht' ?_
    show Holds _ (Flow.factsFrom (Flow.live Flow.elect_45) _)
    rw [hv]
    exact Flow.holds_factsFrom_mono ht'.2.2.2.2 (by table_decide)
  · have hp' : (112, Value.pred false) ∈ factsAt L g Flow.bra_745 ⟨.kvWait 1, i, 0, base, pro⟩ :=
      by simpa [hn] using hp
    obtain ⟨t', hr, ht'⟩ :=
      (Seg.comp (Seg.comp hab (seg_bra Flow.code_745 hp')) (seg_c2loop hpre hg i base pro)) t h
    refine ⟨t', by simpa [hn] using hr, ?_⟩
    simp only [afterCommit, hn, ↓reduceIte]
    exact ht'

theorem afterCommit2_inv {L : Launch} {g : Nat} {d : D} (hi : Inv L g d)
    (hs : ItemSite d.site) (hd : d.t = 0) (htr : 0 < trips L) :
    Inv L g (afterCommit L g d 2) := by
  simp only [afterCommit]
  split_ifs with h
  · exact ⟨hi.t, fun _ => hi.i hs, show d.t + 1 = trips L by omega⟩
  · exact ⟨hi.t, fun _ => hi.i hs, show d.t + 1 < trips L by omega⟩

theorem afterCommit2_sub {L : Launch} {g : Nat} {d : D} :
    (afterCommit L g d 2).site.sub = 0 := by
  simp only [afterCommit]
  split_ifs <;> rfl

theorem stepOk_commit2 (hpre : Pre P L mem0) (hg : g < L.threads) {pro : Nat → Value}
    (i tr : Nat) (base : Value) (pr : Nat → Value) :
    (code asms L g pro).StepOk ⟨.commit 2, i, tr, base, pr⟩ :=
  Code.step_issue Flow.code_tcCommit_2 (fun hf => fires_tcCommit hf) (fun _ => rfl) rfl rfl
    ⟨fun hi => by
        obtain rfl : tr = 0 := hi.1.trip
        exact ⟨_, Seg.weaken_start (seg_c2tail hpre hg i base pr)
          fun _ hR => Flow.holds_factsFrom_mono hR (by table_decide)⟩,
      afterCommit2_sub, rfl, fun hi => ⟨afterCommit2_inv hi.1 trivial hi.1.trip (trips_pos hpre),
        baseOk_afterCommit 2⟩⟩

theorem stepOk_elC2 (hpre : Pre P L mem0) (hg : g < L.threads) {pro : Nat → Value}
    (i tr : Nat) (base : Value) (pr : Nat → Value) :
    (code asms L g pro).StepOk ⟨.elC 2, i, tr, base, pr⟩ :=
  Code.step_elect (dl := ⟨.commit 2, i, tr, base, pr⟩)
    (ds := afterCommit L g ⟨.commit 2, i, tr, base, pr⟩ 2) Flow.code_elect_36 (by fact_free)
    (by rintro r ⟨⟩; exact ⟨by fact_free, by decide⟩) (fun _ _ _ h => by next_simp [next, h])
    (fun _ _ _ h => by next_simp [next, afterCommit, h]) rfl rfl
    (fun _ => ⟨fun _ => by
        site_norm; dsimp only [Code.electFacts]; seg_auto using mma_close hpre hg,
      rfl, rfl, by mma_inv⟩)
    (fun _ => ⟨fun hi => by
        obtain rfl : tr = 0 := hi.1.trip
        dsimp only [Code.electFacts]
        exact ⟨_, Seg.comp (m := 2) (by mma_close hpre hg)
          (seg_c2tail hpre hg i base pr)⟩,
      afterCommit2_sub, rfl, fun hi => ⟨afterCommit2_inv (d := ⟨.commit 2, i, tr, base, pr⟩)
        ⟨hi.1.t, fun _ => hi.1.i trivial, hi.1.trip⟩ trivial hi.1.trip (trips_pos hpre),
        baseOk_afterCommit 2⟩⟩)

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Mma
