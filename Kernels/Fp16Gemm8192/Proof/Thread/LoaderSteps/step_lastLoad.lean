-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderSteps.Base
public import Kernels.Fp16Gemm8192.Proof.Thread.LoaderSteps.trip_end

@[expose] public section

/-! One step of `LoaderSteps`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Loader
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- After block `b`'s last load the leader arrives; the other CTA goes to the next block,
or past the last block to the end of the trip. -/
theorem step_lastLoad {P : Params} {L : Launch} {mem0 : Mem0} {g m n q cp x : Nat} {r : Value}
    {t u : TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0) (b : Fin 8)
    (hi : Inv ⟨.load b 2, m, n, q, cp, r, x⟩)
    (h : At t (Site.load b 2).pc (facts L g ⟨.load b 2, m, n, q, cp, r, x⟩))
    (hc : kernel.code[(Site.load b 2).pc]? = some ins)
    (hf : Fires (Site.load b 2).pc (eventTmpl Prod L g t ins.op) e (some u)) :
    ∃ d' t', next L g ⟨.load b 2, m, n, q, cp, r, x⟩ e = some (some d') ∧
      Relation.ReflTransGen (Tau kernel Prod L g) u t' ∧ At t' d'.site.pc (facts L g d') ∧
        Inv d' := by
  have hm : m < 16 := hi.m
  have hn : n < 32 := hi.n
  have hq : q < 128 := hi.q
  have hq8 : q % 8 = 0 := hi.q8
  obtain ⟨ins', hc', -, hadv, -⟩ := code_advances ⟨.load b 2, b, 2, .inl rfl⟩
  rw [hc] at hc'
  cases hc'
  obtain rfl := fires_next hadv hf
  have h1 := At.next h
  -- the two instructions before the rank branch
  obtain ⟨t1, hr1, ht1⟩ : ∃ t1, run kernel Prod L g 2 (PTX.next t) = some t1 ∧
      At t1 ((Site.load b 2).pc + 3) (factsAt L g ((Site.load b 2).pc + 3) ⟨.load b 2, m, n, q, cp,
        r, x⟩) := by
    fin_cases b <;> loader_seg h1 hpre
  have hp : (rankPred b, Value.pred (decide ((g / L.block) % 2 ≠ 0))) ∈
      factsAt L g ((Site.load b 2).pc + 3) ⟨.load b 2, m, n, q, cp, r, x⟩ := by
    have hlive : ∀ b : Fin 8, rankPred b ∈ Flow.live ((Site.load b 2).pc + 3) := by table_decide
    refine List.mem_map.mpr ⟨rankPred b, hlive b, ?_⟩
    fin_cases b <;> simp only [Fin.isValue, rankPred] <;> loader_values
  obtain ⟨t2, hr2, ht2⟩ := run_bra (K := kernel) (A := Prod) (L := L) (g := g) (code_rank b)
    (decide ((g / L.block) % 2 ≠ 0)) ht1 (holds_mem ht1.2.2.2.2 hp)
    (prod_localRule_bra L g _ _ _)
  by_cases hl : (g / L.block) % 2 = 0
  · -- leader: one instruction to the arrival
    have hd : decide ((g / L.block) % 2 ≠ 0) = false := by simp [hl]
    rw [hd] at ht2
    simp only [Bool.false_eq_true, ↓reduceIte] at ht2
    obtain ⟨t3, hr3, ht3⟩ : ∃ t3, run kernel Prod L g 1 t2 = some t3 ∧
        At t3 (Site.arrive b).pc (facts L g ⟨.arrive b, m, n, q, cp, r, x⟩) := by
      fin_cases b <;> loader_seg ht2 hpre
    refine ⟨⟨.arrive b, m, n, q, cp, r, x⟩, t3, ?_, run_rtg (run_comp (run_comp hr1 hr2) hr3),
      ht3, ⟨hi.1, hi.2, hi.3, hi.4, hi.5, hi.6⟩⟩
    simp [next, leader, hl]
  · have hd : decide ((g / L.block) % 2 ≠ 0) = true := by simp [hl]
    rw [hd] at ht2
    simp only [↓reduceIte] at ht2
    by_cases hb : b.val + 1 < 8
    · obtain ⟨t3, hr3, ht3⟩ : ∃ t3, run kernel Prod L g 4 t2 = some t3 ∧
          At t3 (Site.wait ⟨b.val + 1, hb⟩).pc
            (facts L g ⟨.wait ⟨b.val + 1, hb⟩, m, n, q, cp, r, x⟩) := by
        fin_cases b <;> first | (simp at hb; done) | loader_seg ht2 hpre
      refine ⟨⟨.wait ⟨b.val + 1, hb⟩, m, n, q, cp, r, x⟩, t3, ?_,
        run_rtg (run_comp (run_comp hr1 hr2) hr3), ht3, ⟨hi.1, hi.2, hi.3, hi.4, hi.5, hi.6⟩⟩
      simp [next, leader, hl, hb]
    · have hb7 : b = 7 := Fin.ext (by show b.val = 7; omega)
      subst hb7
      have ht2' : At t2 ((Site.arrive 7).pc + 1)
          (factsAt L g ((Site.arrive 7).pc + 1) ⟨.load 7 2, m, n, q, cp, r, x⟩) :=
        At.mono ht2 (factsAt_mono ht2.2.2.2.2 (by table_decide))
      obtain ⟨k, t', hr', ht', hi'⟩ := trip_end hpre hi ht2'
      refine ⟨endOfTrip ⟨.load 7 2, m, n, q, cp, r, x⟩, t', ?_,
        run_rtg (run_comp (run_comp hr1 hr2) hr'), ht', hi'⟩
      simp [next, leader, hl]

end
end PTX.Kernels.Fp16Gemm8192.Proof.Loader
