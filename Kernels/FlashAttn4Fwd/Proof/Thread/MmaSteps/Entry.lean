-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.MmaSteps.Head

@[expose] public section

/-! The step of the Q descriptor's broadcast: lane 0's value, then the first item's Q poll on
the leader CTA, or the end, through the odd CTA's item loop (`Seg.loop`) when there are items. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Mma
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem fact_mem {L : Launch} {g pc r : Nat} {d : D} {v : Value} (hr : r ∈ Flow.live pc)
    (hv : valueOf L g d r = v) : (r, v) ∈ factsAt L g pc d :=
  hv ▸ Flow.mem_factsFrom hr

/-- The cluster's items end: some item is past the item count. -/
theorem exists_end {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0) :
    ∃ j, totOf L ≤ work L g j := by
  have hc := hpre.clustersPos
  refine ⟨totOf L, ?_⟩
  simp only [work, pre_clusters hpre]
  nlinarith

/-- The odd CTA's item loop, from its first test of item 1 to the end. -/
theorem odd_loop {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) (base : Value) (pro : Nat → Value) (hrank : rank L g ≠ 0)
    (hw0 : work L g 0 < totOf L) :
    ∃ N, Seg kernel asms L g (N * 5 + 1) Flow.bra_1115 (oddFacts L g base pro 0)
      Site.relinquish.pc (facts L g ⟨.relinquish, 0, 0, base, pro⟩) := by
  classical
  let T := Nat.find (exists_end hpre (g := g))
  have hT : totOf L ≤ work L g T := Nat.find_spec (exists_end hpre (g := g))
  have hlt : ∀ j < T, work L g j < totOf L := fun j hj =>
    Nat.lt_of_not_le (Nat.find_min (exists_end hpre (g := g)) hj)
  have hT0 : 0 < T := by
    rcases Nat.eq_zero_or_pos T with h0 | h0
    · rw [h0] at hT; omega
    · exact h0
  refine ⟨T - 1, Seg.loop (F := oddFacts L g base pro) (fun k hk => ?_) ?_⟩
  · -- one pass: the test passes, the odd CTA's test branches, the counter steps
    have hw : work L g (k + 1) < totOf L := hlt _ (by omega)
    have hp136 : (136, Value.pred true) ∈ oddFacts L g base pro k := by
      have hv : valueOdd L g base pro (k + 1) 136 = .pred true := by
        simp [valueOdd, hw, PTX.Flow.lookupLit]
      exact hv ▸ Flow.mem_factsFrom (by table_decide)
    have hp105 : (105, Value.pred true) ∈
        Flow.factsFrom (Flow.live Flow.bra_594) (valueOdd L g base pro (k + 1)) := by
      have hv : valueOdd L g base pro (k + 1) 105 = .pred true := by
        simp only [valueOdd]
        mma_values
        simp [hrank]
      exact hv ▸ Flow.mem_factsFrom (by table_decide)
    exact Seg.of_len (Seg.comp (Seg.comp (Seg.comp (seg_bra Flow.code_1115 hp136)
      (seg_oddA hpre hg base pro k)) (seg_bra Flow.code_594 hp105))
      (seg_oddB hpre hg base pro k hw)) rfl
  · -- the last test fails
    have hp136 : (136, Value.pred false) ∈ oddFacts L g base pro (T - 1) := by
      have hv : valueOdd L g base pro (T - 1 + 1) 136 = .pred false := by
        simp [valueOdd, Nat.sub_add_cancel hT0, Nat.not_lt.mpr hT, PTX.Flow.lookupLit]
      exact hv ▸ Flow.mem_factsFrom (by table_decide)
    exact Seg.of_len (Seg.comp (seg_bra Flow.code_1115 hp136) (seg_oddExit hpre hg base pro _)) rfl

/-- The broadcast of the Q descriptor. -/
theorem step_shflQ {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hg : g < L.threads) (hs : d.site = .shflQ)
    (hi : Inv L g d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) :
    mma_cont L g d e u := by
  obtain ⟨site, i, tr, base, pro⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_5)
  obtain ⟨av, bv, cv, recv, ok, rfl, rfl⟩ := fires_shfl (p := none) hf
  by_cases hv : recv = b32 (qLo L false)
  swap
  · exact .inl (by simp [next, hv])
  subst hv
  right
  have h1 := At.set (r := 860) (v := b32 (qLo L false)) h
    (facts_ne (show 860 ∉ Flow.live Site.shflQ.pc by table_decide))
  simp only [Option.elim]
  have hsh := shape_bounds hpre hg
  have hvq : valueOf L g (d0 base pro) = valueOf L g ⟨.relinquish, 0, 0, base, pro⟩ := rfl
  have hp101 : (101, Value.pred (decide (totOf L ≤ clusterOf L g))) ∈
      factsAt L g Flow.bra_569 (d0 base pro) := fact_mem (by table_decide) (by mma_values)
  have hstart := seg_noItem hpre hg base pro i tr
  by_cases hnone : totOf L ≤ clusterOf L g
  · -- no item
    have hp : (101, Value.pred true) ∈ factsAt L g Flow.bra_569 (d0 base pro) := by
      simpa [hnone] using hp101
    obtain ⟨t', hr, ht'⟩ := (Seg.comp hstart (seg_bra Flow.code_569 hp)) _ h1
    have hn : ¬ (rank L g = 0 ∧ work L g 0 < totOf L) := by
      rw [work_zero]; omega
    refine ⟨⟨.relinquish, 0, 0, base, pro⟩, t', by simp [next, start, hn], run_rtg hr,
      atS_of_at rfl (At.mono ht' ?_), ⟨.inl rfl, nofun, trivial⟩⟩
    show Holds t'.regs (Flow.factsFrom (Flow.live Flow.tmemRelinquish_0) _)
    rw [← hvq]
    exact Flow.holds_factsFrom_mono ht'.2.2.2.2 (by table_decide)
  · have hp : (101, Value.pred false) ∈ factsAt L g Flow.bra_569 (d0 base pro) := by
      simpa [hnone] using hp101
    have hw0 : work L g 0 < totOf L := by rw [work_zero]; omega
    have hp105 : (105, Value.pred (decide (rank L g ≠ 0))) ∈
        factsAt L g Flow.bra_594 (d0 base pro) := fact_mem (by table_decide) (by mma_values)
    have hmid := Seg.comp (Seg.comp (Seg.comp hstart (seg_bra Flow.code_569 hp))
      (seg_toCeil hpre hg base pro)) (seg_toTest hpre hg base pro)
    by_cases hr0 : rank L g = 0
    · -- the leader CTA: the first item
      have hp' : (105, Value.pred false) ∈ factsAt L g Flow.bra_594 (d0 base pro) := by
        simpa [hr0] using hp105
      obtain ⟨t', hr, ht'⟩ := (Seg.comp hmid (seg_bra Flow.code_594 hp')) _ h1
      refine ⟨d0 base pro, t', by simp [next, start, hr0, hw0], run_rtg hr,
        atS_of_at rfl (At.mono ht' ?_), ⟨.inl rfl, fun _ => ⟨hw0, hr0⟩, rfl⟩⟩
      exact Flow.holds_factsFrom_mono ht'.2.2.2.2 (by table_decide)
    · -- the odd CTA: its item loop, then the end
      have hp' : (105, Value.pred true) ∈ factsAt L g Flow.bra_594 (d0 base pro) := by
        simpa [hr0] using hp105
      obtain ⟨N, hloop⟩ := odd_loop hpre hg base pro hr0 hw0
      obtain ⟨t', hr, ht'⟩ := (Seg.comp (Seg.comp (Seg.comp hmid (seg_bra Flow.code_594 hp'))
        (seg_oddEntry hpre hg base pro hw0)) hloop) _ h1
      have hn : ¬ (rank L g = 0 ∧ work L g 0 < totOf L) := fun h => hr0 h.1
      exact ⟨⟨.relinquish, 0, 0, base, pro⟩, t', by simp [next, start, hn], run_rtg hr,
        atS_of_at rfl ht', ⟨.inl rfl, nofun, trivial⟩⟩

theorem stepOk_shflQ {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} (hpre : Pre P L mem0)
    (hg : g < L.threads) {pro : Nat → Value} (i tr : Nat) (base : Value) (pr : Nat → Value) :
    (code asms L g pro).StepOk ⟨.shflQ, i, tr, base, pr⟩ :=
  stepOk_of (fun hn => by
      simp only [next, start] at hn
      split at hn <;> (try split_ifs at hn) <;> cases hn <;> exact nofun)
    fun hi h hc hf => .inl (step_shflQ hpre hg rfl hi (at_of_atS rfl h) hc hf)

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Mma
