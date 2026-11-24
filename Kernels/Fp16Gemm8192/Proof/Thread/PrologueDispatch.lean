-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.PrologueEvents
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! # The prologue's remaining events and the role dispatch

The barrier initializations, the Tensor Memory allocation and its write, the fences, the
cluster barrier, the dispatch on the warp index (warps 8 to 11 lower their register count;
warp 11 elects the loader) and the loader's entry: the tile its CTA starts with. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Prologue
open PTX PTX.Proof PTX.Flow

noncomputable section

set_option maxRecDepth 100000


theorem code_init (i : Fin 18) :
    ∃ ins, kernel.code[(Site.init i).pc]? = some ins ∧ AdvancesOp ins.op := by
  fin_cases i
  all_goals first
    | exact ⟨_, Flow.code_mbarInit_0, trivial⟩ | exact ⟨_, Flow.code_mbarInit_1, trivial⟩
    | exact ⟨_, Flow.code_mbarInit_2, trivial⟩ | exact ⟨_, Flow.code_mbarInit_3, trivial⟩
    | exact ⟨_, Flow.code_mbarInit_4, trivial⟩ | exact ⟨_, Flow.code_mbarInit_5, trivial⟩
    | exact ⟨_, Flow.code_mbarInit_6, trivial⟩ | exact ⟨_, Flow.code_mbarInit_7, trivial⟩
    | exact ⟨_, Flow.code_mbarInit_8, trivial⟩ | exact ⟨_, Flow.code_mbarInit_9, trivial⟩
    | exact ⟨_, Flow.code_mbarInit_10, trivial⟩ | exact ⟨_, Flow.code_mbarInit_11, trivial⟩
    | exact ⟨_, Flow.code_mbarInit_12, trivial⟩ | exact ⟨_, Flow.code_mbarInit_13, trivial⟩
    | exact ⟨_, Flow.code_mbarInit_14, trivial⟩ | exact ⟨_, Flow.code_mbarInit_15, trivial⟩
    | exact ⟨_, Flow.code_mbarInit_16, trivial⟩ | exact ⟨_, Flow.code_mbarInit_17, trivial⟩

set_option maxHeartbeats 10000000 in
/-- A barrier initialization continues to the next one, or after the last to the pointer
and the test for warp 0. -/
theorem step_init {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hg : g < L.threads) (i : Fin 18)
    (hs : d.site = .init i) (hi : Inv d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Step L g d u e := by
  obtain ⟨s, w⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain ⟨ins', hc', hadv⟩ := code_init i
  rw [hc] at hc'
  cases hc'
  obtain rfl := fires_next hadv hf
  have h1 := At.next h
  right
  by_cases hl : i.val + 1 < 18
  · obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g
        ((Site.init ⟨i.val + 1, hl⟩).pc - (Site.init i).pc - 1) (PTX.next t) = some t' ∧
        At t' (Site.init ⟨i.val + 1, hl⟩).pc (facts L g ⟨.init ⟨i.val + 1, hl⟩, w⟩) := by
      fin_cases i <;> first | (simp at hl; done) | pro_seg h1 hpre
    refine ⟨.inl ⟨.init ⟨i.val + 1, hl⟩, w⟩, t', ?_, run_rtg hr,
      good_of_at (by simp) ht' ⟨hi.w⟩⟩
    simp [next, hl]
  · have h17 : i = 17 := Fin.ext (by show i.val = 17; omega)
    subst h17
    have h1' : At (PTX.next t) ((Site.init 17).pc + 1)
        (factsAt L g ((Site.init 17).pc + 1) ⟨.init 17, w⟩) :=
      At.mono h1 (Flow.holds_factsFrom_mono (live := Flow.live (Site.init 17).pc) h1.2.2.2.2
        (by table_decide))
    obtain ⟨k, t', hr, ht'⟩ := from_pointer hpre hg hi h1'
    refine ⟨.inl ⟨afterInits w, w⟩, t', ?_, run_rtg hr,
      good_of_at (by unfold afterInits; split_ifs <;> simp) ht' ⟨hi.w⟩⟩
    simp [next]

/-- The allocation request: lane 0 goes on to its address store; the other lanes go to the
warp barrier. -/
theorem step_alloc {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .alloc) (hi : Inv d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Step L g d u e := by
  obtain ⟨s, w⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0)
  obtain ⟨dst, n, rfl, rfl⟩ := fires_tcAlloc h.2.1 hf
  right
  by_cases hl : laneOf L g = 0
  · refine ⟨.inl ⟨.allocWrite, w⟩, _, ?_, .refl, ?_⟩
    · simp [next, hl]
    · simp only [hl, ↓reduceIte, Good, sub]
      exact ⟨⟨h.1, by simp, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩, ⟨hi.w⟩⟩
  · refine ⟨.inl ⟨.warpBar, w⟩, _, ?_, .refl, ?_⟩
    · simp [next, hl]
    · simp only [hl, ↓reduceIte]
      exact good_of_at (by simp) (At.mono (At.next h)
        (Flow.holds_factsFrom_mono (live := Flow.live Site.alloc.pc)
          (live' := Flow.live Site.warpBar.pc) h.2.2.2.2 (by table_decide)))
        ⟨hi.w⟩

/-- Lane 0's address store, then the warp barrier. -/
theorem step_allocWrite {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .allocWrite) (hi : Inv d)
    (h : t.pc = d.site.pc ∧ t.sub = sub d ∧ t.acc = [] ∧ t.fault = none ∧
      Holds t.regs (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Step L g d u e := by
  obtain ⟨s, w⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  simp only [sub, ↓reduceIte] at h
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemAlloc_0)
  obtain ⟨a, bs, rfl, rfl⟩ := fires_tcAlloc_write h.2.1 hf
  right
  refine ⟨.inl ⟨.warpBar, w⟩, _, by simp [next], .refl, good_of_at (by simp) ?_ ⟨hi.w⟩⟩
  exact ⟨by simp [h.1]; rfl, rfl, h.2.2.1, h.2.2.2.1,
    Flow.holds_factsFrom_mono (live := Flow.live Site.allocWrite.pc)
      (live' := Flow.live Site.warpBar.pc) h.2.2.2.2 (by table_decide)⟩

/-- An advancing event whose successor site is the next instruction. -/
theorem step_adv {L : Launch} {g : Nat} {s s' : Site} {w : Nat} {t u : TState} {e : Event}
    {ins : Instr} (hadv : AdvancesOp ins.op) (hpc : s'.pc = s.pc + 1) (hs' : s' ≠ .allocWrite)
    (hsub : ∀ r ∈ Flow.live s'.pc, r ∈ Flow.live s.pc)
    (hn : next L g ⟨s, w⟩ e = some (some (.inl ⟨s', w⟩))) (hi : Inv ⟨s, w⟩)
    (h : At t s.pc (facts L g ⟨s, w⟩))
    (hf : Fires s.pc (eventTmpl Prod L g t ins.op) e (some u)) : Step L g ⟨s, w⟩ u e := by
  obtain rfl := fires_next hadv hf
  right
  refine ⟨.inl ⟨s', w⟩, _, hn, .refl, good_of_at hs' ?_ ⟨hi.w⟩⟩
  exact At.mono (by rw [hpc]; exact At.next h) (Flow.holds_factsFrom_mono h.2.2.2.2 hsub)

theorem step_warpBar {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .warpBar) (hi : Inv d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Step L g d u e := by
  obtain ⟨s, w⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_warpBar_0)
  exact step_adv (s' := .fence) (by exact trivial) rfl (by simp) (by table_decide) (by simp [next])
    hi h hf

theorem step_fence {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .fence) (hi : Inv d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Step L g d u e := by
  obtain ⟨s, w⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceProxy_0)
  exact step_adv (s' := .fenceInit) (by exact trivial) rfl (by simp) (by table_decide)
    (by simp [next]) hi h hf

theorem step_fenceInit {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .fenceInit) (hi : Inv d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Step L g d u e := by
  obtain ⟨s, w⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_fenceMbarInit_0)
  exact step_adv (s' := .arrive) (by exact trivial) rfl (by simp) (by table_decide) (by simp [next])
    hi h hf

theorem step_arrive {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .arrive) (hi : Inv d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Step L g d u e := by
  obtain ⟨s, w⟩ := d
  simp only at hs
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterArrive_0)
  exact step_adv (s' := .wait) (by exact trivial) rfl (by simp) (by table_decide) (by simp [next])
    hi h hf

set_option maxHeartbeats 10000000 in
/-- The cluster wait, then the dispatch: warps 8 to 11 lower their register count, warps 0
to 7 become consumers. -/
theorem step_wait {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .wait) (hi : Inv d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Step L g d u e := by
  obtain ⟨s, w⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterWait_0)
  obtain rfl := fires_next (show AdvancesOp (.cluster _) from trivial) hf
  by_cases hw : w / 4 = 2
  · right
    -- the values do not depend on the column; dropping it keeps the facts closed below
    have h1 : At (PTX.next t) (Site.wait.pc + 1) (facts L g ⟨.wait, w⟩) := At.next h
    have hw' : w = 8 ∨ w = 9 ∨ w = 10 ∨ w = 11 := by omega
    -- the warp-group test is evaluated into its fact, then the branch is taken apart
    obtain ⟨t1, hr1, ht1⟩ : ∃ t1, run kernel Prod L g 2 (PTX.next t) = some t1 ∧
        At t1 Flow.bra_88 (factsAt L g Flow.bra_88 ⟨.wait, w⟩) := by
      rcases hw' with rfl | rfl | rfl | rfl <;> pro_seg h1 hpre
    obtain ⟨t2, hr2, ht2⟩ := run_bra (K := kernel) (A := Prod) (L := L) (g := g) Flow.code_88
      false ht1 (reg_val ht1 (r := 6) (by table_decide) (by pro_values; simp [hw]))
      (prod_localRule_bra L g _ _ _)
    simp only [Bool.false_eq_true, ↓reduceIte] at ht2
    have ht' : At t2 Site.setMaxReg.pc (facts L g ⟨.setMaxReg, w⟩) :=
      At.mono ht2 (Flow.holds_factsFrom_mono (live := Flow.live Flow.bra_88)
        (live' := Flow.live Site.setMaxReg.pc) ht2.2.2.2.2 (by table_decide))
    exact ⟨.inl ⟨.setMaxReg, w⟩, t2, by simp [next, hw], run_rtg (run_comp hr1 hr2),
      good_of_at (by simp) ht' ⟨hi.w⟩⟩
  · by_cases hc : w < 8 ∧ w = Consumer.tidOf L g / 32
    · right
      obtain ⟨hw8, hwt⟩ := hc
      have h1 : At (PTX.next t) (Site.wait.pc + 1) (facts L g ⟨.wait, w⟩) := At.next h
      have hw' : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 5 ∨ w = 6 ∨ w = 7 := by omega
      -- the warp-group test sends warps 0 to 7 to the consumers' entry
      obtain ⟨t1, hr1, ht1⟩ : ∃ t1, run kernel Prod L g 2 (PTX.next t) = some t1 ∧
          At t1 Flow.bra_88 (factsAt L g Flow.bra_88 ⟨.wait, w⟩) := by
        rcases hw' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> pro_seg h1 hpre
      obtain ⟨t2, hr2, ht2⟩ := run_bra (K := kernel) (A := Prod) (L := L) (g := g) Flow.code_88
        true ht1 (reg_val ht1 (r := 6) (by table_decide) (by pro_values; simp [hw]))
        (prod_localRule_bra L g _ _ _)
      simp only [↓reduceIte] at ht2
      -- the test for warps beyond the consumers fails
      obtain ⟨t3, hr3, ht3⟩ : ∃ t3, run kernel Prod L g 1 t2 = some t3 ∧
          At t3 Flow.bra_618 ((7, .pred false) :: factsAt L g Flow.bra_88 ⟨.wait, w⟩) := by
        rcases hw' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> pro_seg ht2 hpre
      obtain ⟨t4, hr4, ht4⟩ := run_bra (K := kernel) (A := Prod) (L := L) (g := g)
        Flow.code_618 false ht3 (holds_mem ht3.2.2.2.2 (List.mem_cons_self ..))
        (prod_localRule_bra L g _ _ _)
      simp only [Bool.false_eq_true, ↓reduceIte] at ht4
      have hlive : Flow.live Consumer.Site.setMaxReg.pc = [47, 48, 894] := by
        table_decide
      have ht' : At t4 Consumer.Site.setMaxReg.pc (Consumer.facts L g consStart) := by
        refine ⟨ht4.1, ht4.2.1, ht4.2.2.1, ht4.2.2.2.1, ?_⟩
        show Holds t4.regs (Flow.factsFrom (Flow.live Consumer.Site.setMaxReg.pc)
          (Consumer.valueOf L g consStart))
        apply Flow.holds_of_pointwise
        intro r hr
        rw [hlive] at hr
        have hold := fun r (hl : r ∈ Flow.live Flow.bra_88) =>
          holds_mem ht4.2.2.2.2 (List.mem_cons_of_mem _ (Flow.mem_factsFrom (val :=
            valueOf L g ⟨.wait, w⟩) hl))
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [hold 47 (by table_decide)]
          simp only [valueOf, Consumer.valueOf, PTX.Flow.lookupLit, Option.getD_some]
        · rw [hold 48 (by table_decide)]
          simp only [valueOf, Consumer.valueOf, PTX.Flow.lookupLit, Option.getD_some]
          rw [hwt]
        · rw [hold 894 (by table_decide)]
          simp only [valueOf, Consumer.valueOf, PTX.Flow.lookupLit, Option.getD_some]
      have hlt : Consumer.tidOf L g < 256 := by
        have := Nat.mod_lt g (show 0 < L.block by rw [hpre.block]; decide)
        unfold Consumer.tidOf at hwt ⊢
        omega
      exact ⟨.inr (.cons consStart), t4, by subst hwt; simp [next, hw, hw8],
        run_rtg (run_comp hr1 (run_comp hr2 (run_comp hr3 hr4))),
        ⟨⟨ht'.1, ht'.2.1, ht'.2.2.1, ht'.2.2.2.1, ht'.2.2.2.2⟩,
          ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩, hlt⟩⟩
    · left
      simp [next, hw, hc]

set_option maxHeartbeats 10000000 in
/-- Lowering the register count, then the dispatch within warps 8 to 11: warp 11 goes to
the loader's election, warp 10 to the scheduler, warps 8 and 9 to the MMA warps. -/
theorem step_setMaxReg {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .setMaxReg) (hi : Inv d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Step L g d u e := by
  obtain ⟨s, w⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_setMaxReg_0)
  obtain rfl := fires_next (show AdvancesOp (.setMaxReg false 56) from trivial) hf
  by_cases hw : w = 11
  · subst hw
    right
    have h1 : At (PTX.next t) (Site.setMaxReg.pc + 1) (facts L g ⟨.setMaxReg, 11⟩) := At.next h
    obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g 6 (PTX.next t) = some t' ∧
        At t' Site.roleElect.pc (facts L g ⟨.roleElect, 11⟩) := by
      pro_seg h1 hpre
    exact ⟨.inl ⟨.roleElect, 11⟩, t', by simp [next], run_rtg hr,
      good_of_at (by simp) ht' ⟨hi.w⟩⟩
  by_cases h10 : w = 10
  · -- the scheduler's election
    subst h10
    right
    have h1 : At (PTX.next t) (Site.setMaxReg.pc + 1) (facts L g ⟨.setMaxReg, 10⟩) := At.next h
    obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g 4 (PTX.next t) = some t' ∧
        At t' schedStart.site.pc (Scheduler.facts L g schedStart) := by
      sched_seg h1 hpre [schedStart, valueOf, values, List.lookup_cons, Nat.reduceBEq,
        Option.getD_some]
    exact ⟨.inr (.sched schedStart), t', by simp [next], run_rtg hr, ht',
      ⟨by decide, by decide, by decide⟩⟩
  by_cases h89 : w = 8 ∨ w = 9
  · -- the MMA warps: the cluster's leader CTA elects, the other CTA leaves
    right
    have h1 : At (PTX.next t) (Site.setMaxReg.pc + 1) (facts L g ⟨.setMaxReg, w⟩) := At.next h
    obtain ⟨t1, hr1, ht1⟩ : ∃ t1, run kernel Prod L g 6 (PTX.next t) = some t1 ∧
        At t1 Flow.bra_456 (factsAt L g Flow.bra_456 ⟨.setMaxReg, w⟩) := by
      rcases h89 with rfl | rfl <;> pro_seg h1 hpre
    obtain ⟨t2, hr2, ht2⟩ := run_bra (K := kernel) (A := Prod) (L := L) (g := g) Flow.code_456
      (decide ((g / L.block) % 2 ≠ 0)) ht1
      (reg_val ht1 (r := 38) (by table_decide) (by pro_values))
      (prod_localRule_bra L g _ _ _)
    have hi' : Mma.Inv (mmaStart L g w) := ⟨h89, by show (0 : Nat) < 128; omega,
      by show (0 : Nat) % 4 = 0; rfl, by show (0 : Nat) < 2; omega, by show (0 : Nat) < 2; omega,
      by show (0 : Nat) < 2; omega, by show (0 : Nat) < 2 ^ 32; omega⟩
    by_cases hl : (g / L.block) % 2 = 0
    · rw [show decide ((g / L.block) % 2 ≠ 0) = false by simp [hl]] at ht2
      simp only [Bool.false_eq_true, ↓reduceIte] at ht2
      have hs : mmaStart L g w = ⟨.elect, w, 0, 0, 0, 0, b32 0, 0⟩ := by
        simp [mmaStart, Loader.leader, hl]
      obtain ⟨t3, hr3, ht3⟩ : ∃ t3, run kernel Prod L g 2 t2 = some t3 ∧
          At t3 (mmaStart L g w).site.pc (Mma.facts L g (mmaStart L g w)) := by
        rw [hs]
        rcases h89 with rfl | rfl <;> mma_seg ht2 hpre [valueOf, values, List.lookup_cons,
          Nat.reduceBEq, Option.getD_some]
      exact ⟨.inr (.mma (mmaStart L g w)), t3, by simp [next, hw, h10, h89],
        run_rtg (run_comp hr1 (run_comp hr2 hr3)), ht3, hi', by rw [hs]; simp,
        by rw [hs]; exact .inr (.inr (.inr hl))⟩
    · rw [show decide ((g / L.block) % 2 ≠ 0) = true by simp [hl]] at ht2
      simp only [↓reduceIte] at ht2
      have hs : mmaStart L g w = ⟨.exitArrive, w, 0, 0, 0, 0, b32 0, 0⟩ := by
        simp [mmaStart, Loader.leader, hl]
      obtain ⟨t3, hr3, ht3⟩ : ∃ t3, run kernel Prod L g 1 t2 = some t3 ∧
          At t3 (mmaStart L g w).site.pc (Mma.facts L g (mmaStart L g w)) := by
        rw [hs]
        rcases h89 with rfl | rfl <;> mma_seg ht2 hpre [valueOf, values, List.lookup_cons,
          Nat.reduceBEq, Option.getD_some]
      exact ⟨.inr (.mma (mmaStart L g w)), t3, by simp [next, hw, h10, h89],
        run_rtg (run_comp hr1 (run_comp hr2 hr3)), ht3, hi', by rw [hs]; simp,
        by rw [hs]; exact .inl rfl⟩
  · left
    simp [next, hw, h10, h89]

end
end PTX.Kernels.Fp16Gemm8192.Proof.Prologue
