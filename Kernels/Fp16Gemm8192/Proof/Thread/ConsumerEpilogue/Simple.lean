-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerEpilogue.Base
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerEpilogue.Subs
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerEpilogue.step_commit_7

@[expose] public section

/-! The epilogue steps whose local segments are short: the barrier, drain, commit, exit, final
drain,
load base and store sites. Each is one lemma of its site; the heavier sites keep their own
modules. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Consumer
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem step_barA {L : Launch} {g : Nat} {d : D} {k : Fin 8} {t u : TState} {e : Event}
    {ins : Instr} (hs : d.site = .barA k) (hi : Inv d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    epi_cont L g d e u := by
  obtain ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain ⟨ins', hc', hadv⟩ := epi_barA_code k
  rw [hc] at hc'
  cases hc'
  obtain rfl := fires_async_next hadv hf
  have h1 := At.next h
  rw [epi_pc_barA_store k] at h1
  right
  refine ⟨⟨.store k 0 0, m, n, m', n', cp, ap, resp, x, acc, base⟩, PTX.next t, by simp [next],
    .refl, ?_, ⟨hi.m, hi.n, hi.m', hi.n', hi.cp, hi.ap, hi.x⟩⟩
  exact At.mono h1 (epi_holds_facts_of h1.2.2.2.2 (epi_barA_store_sub k) fun _ _ => rfl)

theorem step_commit_lt {L : Launch} {g : Nat} {d : D} {k : Fin 8} {t u : TState} {e : Event}
    {ins : Instr} (hk : k.val + 1 < 8) (hs : d.site = .commit k) (hi : Inv d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    epi_cont L g d e u := by
  obtain ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain ⟨ins', hc', hadv⟩ := epi_commit_code k
  rw [hc] at hc'
  cases hc'
  obtain rfl := fires_async_next hadv hf
  have h1 := At.next h
  have h2 : At (PTX.next t) (Site.drain ⟨k.val + 1, hk⟩).pc
      (factsAt L g (Site.drain ⟨k.val + 1, hk⟩).pc
        ⟨.drain ⟨k.val + 1, hk⟩, m, n, m', n', cp, ap, resp, x, acc, base⟩) := by
    rw [← epi_pc_commit_drain k hk]
    exact At.mono h1 (epi_holds_facts_of h1.2.2.2.2 (epi_commit_drain_sub k hk) fun _ _ => rfl)
  right
  exact ⟨⟨.drain ⟨k.val + 1, hk⟩, m, n, m', n', cp, ap, resp, x, acc, base⟩, PTX.next t,
    by simp [next, hk], .refl, h2, ⟨hi.m, hi.n, hi.m', hi.n', hi.cp, hi.ap, hi.x⟩⟩

theorem step_commit {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {k : Fin 8}
    {t u : TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .commit k)
    (hi : Inv d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    epi_cont L g d e u := by
  by_cases hk : k.val + 1 < 8
  · exact step_commit_lt hk hs hi h hc hf
  · have hk7 : k = 7 := Fin.ext (by show k.val = 7; have := k.isLt; omega)
    subst hk7
    exact step_commit_7 hpre hs hi h hc hf

theorem step_dealloc {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .dealloc) (hi : Inv d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    epi_cont L g d e u := by
  obtain ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemDealloc_0)
  obtain rfl := fires_async_next (show AsyncAdvancesOp (.tcDealloc _ _ _) from trivial) hf
  right
  refine ⟨⟨.exit, m, n, m', n', cp, ap, resp, x, acc, base⟩, PTX.next t, by simp [next],
    .refl, ?_, ⟨hi.m, hi.n, hi.m', hi.n', hi.cp, hi.ap, hi.x⟩⟩
  exact At.mono (At.next h) (epi_holds_facts_of (At.next h).2.2.2.2 epi_exit_sub fun _ _ => rfl)

theorem step_drain {L : Launch} {g : Nat} {d : D} {k : Fin 8} {t u : TState} {e : Event}
    {ins : Instr} (hs : d.site = .drain k) (hi : Inv d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    epi_cont L g d e u := by
  obtain ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain ⟨ins', hc', hadv⟩ := epi_drain_code k
  rw [hc] at hc'
  cases hc'
  obtain rfl := fires_async_next hadv hf
  have h1 := At.next h
  rw [epi_pc_drain_barA k] at h1
  right
  refine ⟨⟨.barA k, m, n, m', n', cp, ap, resp, x, acc, base⟩, PTX.next t, by simp [next],
    .refl, ?_, ⟨hi.m, hi.n, hi.m', hi.n', hi.cp, hi.ap, hi.x⟩⟩
  exact At.mono h1 (epi_holds_facts_of h1.2.2.2.2 (epi_drain_barA_sub k) fun _ _ => rfl)

theorem step_exitArrive {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .exitArrive) (hi : Inv d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    epi_cont L g d e u := by
  obtain ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterArrive_1)
  obtain rfl := fires_next (show AdvancesOp (.cluster _) from trivial) hf
  right
  refine ⟨⟨.exitWait, m, n, m', n', cp, ap, resp, x, acc, base⟩, PTX.next t, by simp [next],
    .refl, ?_, ⟨hi.m, hi.n, hi.m', hi.n', hi.cp, hi.ap, hi.x⟩⟩
  exact At.mono (At.next h) (epi_holds_facts_of (At.next h).2.2.2.2 epi_exitWait_sub fun _ _ => rfl)

theorem step_exitWait {L : Launch} {g : Nat} {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .exitWait) (hi : Inv d) (h : At t d.site.pc (facts L g d))
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    epi_cont L g d e u := by
  obtain ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_clusterWait_1)
  obtain rfl := fires_next (show AdvancesOp (.cluster _) from trivial) hf
  have h1 := At.next h
  have hp : (42, Value.pred (decide (tidOf L g / 32 ≠ 0))) ∈
      factsAt L g Site.exitWait.pc ⟨.exitWait, m, n, m', n', cp, ap, resp, x, acc, base⟩ := by
    have hv : valueOf L g ⟨.exitWait, m, n, m', n', cp, ap, resp, x, acc, base⟩ 42 =
        Value.pred (decide (tidOf L g / 32 ≠ 0)) := by
      cons_values
    rw [← hv]
    exact Flow.mem_factsFrom (by table_decide)
  obtain ⟨t2, hr2, ht2⟩ := run_bra (K := kernel) (A := Prod) (L := L) (g := g) Flow.code_1090
    (decide (tidOf L g / 32 ≠ 0)) h1 (holds_mem h1.2.2.2.2 hp)
    (prod_localRule_bra L g _ _ _)
  right
  by_cases hw : tidOf L g / 32 = 0
  · rw [show decide (tidOf L g / 32 ≠ 0) = false by simp [hw]] at ht2
    simp only [Bool.false_eq_true, ↓reduceIte] at ht2
    refine ⟨⟨.relinquish, m, n, m', n', cp, ap, resp, x, acc, base⟩, t2, by simp [next, hw],
      run_rtg hr2, At.mono ht2 (epi_holds_facts_of ht2.2.2.2.2 epi_relinquish_sub fun _ _ => rfl),
      ⟨hi.m, hi.n, hi.m', hi.n', hi.cp, hi.ap, hi.x⟩⟩
  · rw [show decide (tidOf L g / 32 ≠ 0) = true by simp [hw]] at ht2
    simp only [↓reduceIte] at ht2
    refine ⟨⟨.exit, m, n, m', n', cp, ap, resp, x, acc, base⟩, t2, by simp [next, hw],
      run_rtg hr2, At.mono ht2 (epi_holds_facts_of ht2.2.2.2.2 epi_exit_wait_sub fun _ _ => rfl),
      ⟨hi.m, hi.n, hi.m', hi.n', hi.cp, hi.ap, hi.x⟩⟩

theorem step_relinquish {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .relinquish) (hi : Inv d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    epi_cont L g d e u := by
  obtain ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_tmemRelinquish_0)
  obtain rfl := fires_async_next (show AsyncAdvancesOp (.tcRelinquish _) from trivial) hf
  obtain ⟨t1, hr1, ht1⟩ : ∃ t1, run kernel Prod L g 1 (PTX.next t) = some t1 ∧
      At t1 Site.ldBase.pc (facts L g ⟨.ldBase, m, n, m', n', cp, ap, resp, x, acc, base⟩) := by
    cons_seg (At.next h) hpre
  right
  refine ⟨⟨.ldBase, m, n, m', n', cp, ap, resp, x, acc, base⟩, t1, by simp [next],
    run_rtg hr1, ht1, ⟨hi.m, hi.n, hi.m', hi.n', hi.cp, hi.ap, hi.x⟩⟩

theorem step_finalDrain {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hw : tidOf L g < 256)
    (hs : d.site = .finalDrain) (hi : Inv d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    epi_cont L g d e u := by
  obtain ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bulkWait_8)
  obtain rfl := fires_async_next (show AsyncAdvancesOp (.bulkWait _ _) from trivial) hf
  obtain ⟨t1, hr1, ht1⟩ : ∃ t1, run kernel Prod L g 1 (PTX.next t) = some t1 ∧
      At t1 Site.exitArrive.pc (facts L g ⟨.exitArrive, m, n, m', n', cp, ap, resp, x, acc,
        base⟩) := by
    cons_seg (At.next h) hpre [epi_setp_bounded (tidOf L g / 32) (by omega)]
  right
  refine ⟨⟨.exitArrive, m, n, m', n', cp, ap, resp, x, acc, base⟩, t1, by simp [next],
    run_rtg hr1, ht1, ⟨hi.m, hi.n, hi.m', hi.n', hi.cp, hi.ap, hi.x⟩⟩

theorem step_ldBase {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .ldBase) (hi : Inv d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    (next L g d e = some none ∨
      ∃ d' t', next L g d e = some (some d') ∧
        Relation.ReflTransGen (Tau kernel Prod L g) u t' ∧ At t' d'.site.pc (facts L g d') ∧
          Inv d') ∨
    (next L g d e = none ∧ Machine.Dead (K := kernel) (A := Prod) (L := L) (g := g) u) := by
  obtain ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_load_0)
  obtain ⟨a, bs, rfl, hu⟩ := fires_load rfl rfl hf
  change u = afterLoad t [874] bs at hu
  subst hu
  cases hv : rebuild 3 bs with
  | error f =>
    exact .inr ⟨by simp [next, hv], Machine.dead_of_fault (f := f) (by simp [afterLoad, hv])⟩
  | ok v =>
    refine .inl (.inr ?_)
    have hv3 := hv
    have h1 : At { setReg t 874 v with pc := t.pc + 1, sub := 0, acc := [] }
        (Site.ldBase.pc + 1) [(874, v)] :=
      ⟨by rw [h.1], rfl, rfl, h.2.2.2.1, by simp [setReg]⟩
    rw [afterLoad_ok h.2.1 h.2.2.1 hv3]
    obtain ⟨t', hr, ht'⟩ : ∃ t', run kernel Prod L g 1
        { setReg t 874 v with pc := t.pc + 1, sub := 0, acc := [] } = some t' ∧
        At t' Site.dealloc.pc (facts L g ⟨.dealloc, m, n, m', n', cp, ap, resp, x, acc, v⟩) := by
      cons_seg h1 hpre
    refine ⟨⟨.dealloc, m, n, m', n', cp, ap, resp, x, acc, v⟩, t', by simp [next, hv],
      run_rtg hr, ht', ⟨hi.m, hi.n, hi.m', hi.n', hi.cp, hi.ap, hi.x⟩⟩

/-- A store element: the next element of the same store, the next store, or the barrier
after the slice's stores. -/
theorem step_store {L : Launch} {g : Nat} {d : D} {k : Fin 8} {i el : Fin 4}
    {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .store k i el) (hi : Inv d) (h : AtS L g t d)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    next L g d e = some none ∨ ∃ d' t', next L g d e = some (some d') ∧
      Relation.ReflTransGen (Tau kernel Prod L g) u t' ∧ AtS L g t' d' ∧ Inv d' := by
  obtain ⟨hpc, hsub, hacc, hfault, hreg⟩ := h
  obtain ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only [Site.sub] at hs hpc hsub hreg hc hf hi
  subst hs
  have hsub' : t.sub = el.val := hsub
  clear hsub
  have hel4 := el.isLt
  obtain ⟨ins', hc', base', off, a0, a1, a2, a3, hop⟩ := epi_store_code k i el
  rw [hc] at hc'
  cases hc'
  rw [hop] at hf
  have hu := epi_fires_store hf
  subst hu
  by_cases hlt : el.val + 1 < 4
  · have hlen : t.sub + 1 < 4 := by omega
    have hA : afterStore t [a0, a1, a2, a3] = { t with sub := t.sub + 1 } := by
      simp [afterStore, hlen]
    rw [hA]
    right
    refine ⟨⟨.store k i ⟨el.val + 1, hlt⟩, m, n, m', n', cp, ap, resp, x, acc, base⟩,
      { t with sub := t.sub + 1 }, by simp [next, hlt], Relation.ReflTransGen.refl,
      ⟨hpc, ?_, hacc, hfault, ?_⟩, ⟨hi.m, hi.n, hi.m', hi.n', hi.cp, hi.ap, hi.x⟩⟩
    · show t.sub + 1 = el.val + 1
      omega
    · exact epi_holds_facts_of hreg (fun r hr => hr) (fun _ _ => rfl)
  · have hel : el.val = 3 := by omega
    have hlen : ¬ (t.sub + 1 < 4) := by omega
    have hA : afterStore t [a0, a1, a2, a3] = { t with pc := t.pc + 1, sub := 0 } := by
      simp [afterStore, hlen]
    rw [hA]
    by_cases hi3 : i.val + 1 < 4
    · right
      refine ⟨⟨.store k ⟨i.val + 1, hi3⟩ 0, m, n, m', n', cp, ap, resp, x, acc, base⟩,
        { t with pc := t.pc + 1, sub := 0 }, by simp [next, hlt, hi3], Relation.ReflTransGen.refl,
        ⟨?_, rfl, hacc, hfault, ?_⟩, ⟨hi.m, hi.n, hi.m', hi.n', hi.cp, hi.ap, hi.x⟩⟩
      · show t.pc + 1 = Site.pc (.store k ⟨i.val + 1, hi3⟩ 0)
        rw [hpc]
        exact epi_pc_store_succ k i hi3
      · exact epi_holds_facts_of hreg (epi_store_succ_sub k i hi3) (fun _ _ => rfl)
    · right
      refine ⟨⟨.barB k, m, n, m', n', cp, ap, resp, x, acc, base⟩,
        { t with pc := t.pc + 1, sub := 0 }, by simp [next, hlt, hi3], Relation.ReflTransGen.refl,
        ⟨?_, rfl, hacc, hfault, ?_⟩, ⟨hi.m, hi.n, hi.m', hi.n', hi.cp, hi.ap, hi.x⟩⟩
      · show t.pc + 1 = Site.pc (.barB k)
        rw [hpc]
        exact epi_pc_store_barB k i hi3
      · exact epi_holds_facts_of hreg (epi_barB_store_sub k i hi3) (fun _ _ => rfl)

end
end PTX.Kernels.Fp16Gemm8192.Proof.Consumer
