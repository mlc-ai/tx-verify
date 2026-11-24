-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.StoreBase
public import Kernels.FlashAttn4Fwd.Proof.Thread.LoaderWorkPre

@[expose] public section

/-! # The store warp's item loop

The role's start (`setmaxnreg`, the coordinates of the cluster's first item, the branch past
the loop when the cluster has no item) and the end of an item (the arrival freeing stage 1,
the coordinates of the next item, the branch back into the loop or to the exit). Each segment
is cut at its branch: the code's comparison is a checkpoint fact (`factsX`), its value is
decided under `Pre` (`Work.start_branch`, `Work.loop_branch`), and the branch is taken with
`run_bra`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof.Store
open PTX PTX.Proof PTX.Flow Work

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- The checkpoint registers at the start's branch: the comparison and the first quotient and
its product with `nb`. -/
def exStart (L : Launch) (g : Nat) : List (Nat × Value) :=
  [(138, .pred (PTX.compare .ge .s 32 (rd (BitVec.ofNat 64 (cid L g))) (rd (totW L)))),
   (392, .bits 32 (qbW L g 0)), (393, .bits 32 (mulLoW (qbW L g 0) (BitVec.ofNat 64 (nb L))))]

/-- The checkpoint register at the item loop's branch: the comparison of the next item. -/
def exLoop (L : Launch) (g i : Nat) : List (Nat × Value) :=
  [(139, .pred (PTX.compare .lt .s 32 (rd (workW L g (i + 1))) (rd (totW L))))]

/-- `setmaxnreg`, the first item's coordinates, and the loop entry or the exit. -/
theorem step_start {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {d : D} {t u : TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0)
    (hg : g < L.threads) (hs : d.site = .setMaxReg) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i⟩ := d
  simp only at hs h hc hf ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_3)
  obtain rfl := fires_next (by exact trivial) hf
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  obtain ⟨t1, hr1, ht1⟩ : ∃ t1, run kernel asms L g 16 (PTX.next t) = some t1 ∧
      At t1 (Site.setMaxReg.pc + 17)
        (factsX L g (Site.setMaxReg.pc + 17) ⟨.wait 0, 0⟩ (exStart L g)) := by
    seg_fp (At.next h) using
      try simp only [valueX, exStart, valueOf, table, PTX.Flow.lookupLit, Option.getD_some,
        Option.getD_none]
      all_goals first
        | w_rfl_deep
        | (simp only [batchW, qbW, quotW, workW]
           rw [mulHiW_comm (BitVec.ofNat 64 (cid L g))]
           unfold_w
           rfl)
  have hp : (138, Value.pred (PTX.compare .ge .s 32 (rd (BitVec.ofNat 64 (cid L g)))
      (rd (totW L)))) ∈ factsX L g (Site.setMaxReg.pc + 17) ⟨.wait 0, 0⟩ (exStart L g) :=
    List.mem_map.mpr ⟨138, by table_decide, by simp [valueX, exStart]⟩
  obtain ⟨t2, hr2, ht2⟩ := run_bra (K := kernel) (A := asms) (L := L) (g := g)
    (show kernel.code[Site.setMaxReg.pc + 17]? = _ from Flow.code_1147) _ ht1
    (holds_mem ht1.2.2.2.2 hp)
    asms_localRule_none
  rw [start_branch hpre hg] at ht2
  right
  by_cases hT : 0 < T L g
  · simp only [hT, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte] at ht2
    obtain ⟨t3, hr3, ht3⟩ : ∃ t3, run kernel asms L g 15 t2 = some t3 ∧
        At t3 (Site.wait 0).pc (facts L g ⟨.wait 0, 0⟩) := by
      store_seg ht2 hpre
    exact ⟨⟨.wait 0, 0⟩, t3, by simp [next, hT], run_rtg (run_comp (run_comp hr1 hr2) hr3),
      ht3, fun _ => hT⟩
  · simp only [hT, not_false_eq_true, decide_true, ↓reduceIte] at ht2
    obtain ⟨t3, hr3, ht3⟩ : ∃ t3, run kernel asms L g 5 t2 = some t3 ∧
        At t3 Site.exit.pc (facts L g ⟨.exit, 0⟩) := by
      store_seg ht2 hpre
    exact ⟨⟨.exit, 0⟩, t3, by simp [next, hT], run_rtg (run_comp (run_comp hr1 hr2) hr3),
      ht3, fun h => absurd rfl h⟩

/-- The arrival freeing stage 1, the next item's coordinates, and the loop or the exit. -/
theorem step_free1 {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}
    {d : D} {t u : TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0)
    (hs : d.site = .free 1) (hi : Inv L g d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl asms L g t ins.op) e (some u)) : Step asms L g d e u := by
  obtain ⟨site, i⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  have hiT : i < T L g := hi (by simp)
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_mbarArrive_9)
  obtain ⟨rfl, m, tx, c, rel, sc, hk, -⟩ := fires_arrive_state hf
  have h1 := At.clear h (facts_ne (pc := Flow.mbarArrive_9) (r := 4102) (by table_decide))
  have hbase := hpre.sharedRange
  unfold sharedBytes at hbase
  obtain ⟨t1, hr1, ht1⟩ : ∃ t1, run kernel asms L g 17 _ = some t1 ∧
      At t1 ((Site.free 1).pc + 18)
        (factsX L g ((Site.free 1).pc + 18) ⟨.wait 0, i + 1⟩ (exLoop L g i)) := by
    seg_fp h1 using
      try simp only [valueX, exLoop, valueOf, table, PTX.Flow.lookupLit, Option.getD_some,
        Option.getD_none]
      all_goals w_rfl_deep
  have hp : (139, Value.pred (PTX.compare .lt .s 32 (rd (workW L g (i + 1))) (rd (totW L)))) ∈
      factsX L g ((Site.free 1).pc + 18) ⟨.wait 0, i + 1⟩ (exLoop L g i) :=
    List.mem_map.mpr ⟨139, by table_decide, by simp [valueX, exLoop]⟩
  obtain ⟨t2, hr2, ht2⟩ := run_bra (K := kernel) (A := asms) (L := L) (g := g)
    (show kernel.code[(Site.free 1).pc + 18]? = _ from Flow.code_1202) _ ht1
    (holds_mem ht1.2.2.2.2 hp)
    asms_localRule_none
  rw [loop_branch hpre hiT] at ht2
  right
  by_cases hT : i + 1 < T L g
  · simp only [hT, decide_true, ↓reduceIte] at ht2
    obtain ⟨t3, hr3, ht3⟩ : ∃ t3, run kernel asms L g 2 t2 = some t3 ∧
        At t3 (Site.wait 0).pc (facts L g ⟨.wait 0, i + 1⟩) := by
      store_seg ht2 hpre
    exact ⟨⟨.wait 0, i + 1⟩, t3, by simp [next, itemEnd, hT, hk],
      run_rtg (run_comp (run_comp hr1 hr2) hr3), ht3, fun _ => hT⟩
  · simp only [hT, decide_false, Bool.false_eq_true, ↓reduceIte] at ht2
    obtain ⟨t3, hr3, ht3⟩ : ∃ t3, run kernel asms L g 5 t2 = some t3 ∧
        At t3 Site.exit.pc (facts L g ⟨.exit, i⟩) := by
      store_seg ht2 hpre
    exact ⟨⟨.exit, i⟩, t3, by simp [next, itemEnd, hT, hk],
      run_rtg (run_comp (run_comp hr1 hr2) hr3), ht3, fun h => absurd rfl h⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof.Store
