-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerEpilogue.Base
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerEpilogue.Subs

@[expose] public section

/-! One step of `ConsumerEpilogue`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Consumer
open PTX PTX.Proof PTX.Flow
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem step_barB {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {k : Fin 8}
    {t u : TState} {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .barB k)
    (hi : Inv d) (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    epi_cont L g d e u := by
  obtain ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  have hx : x < 2 ^ 32 := hi.x
  obtain ⟨ins', hc', hadv⟩ := epi_barB_code k
  rw [hc] at hc'
  cases hc'
  obtain rfl := fires_async_next hadv hf
  have h1 := At.next h
  have hp : (epi_barPred k, Value.pred (decide ((tidOf L g / 32 % 4) ||| (tidOf L g % 32) ≠ 0))) ∈
      factsAt L g (Site.barB k).pc ⟨.barB k, m, n, m', n', cp, ap, resp, x, acc, base⟩ := by
    rw [← epi_barPred_val L g _ k]
    exact Flow.mem_factsFrom (epi_barPred_live k)
  obtain ⟨u1, hr1, ht1⟩ := run_bra (K := kernel) (A := Prod) (L := L) (g := g) (epi_barB_branch k)
    (decide ((tidOf L g / 32 % 4) ||| (tidOf L g % 32) ≠ 0)) h1
    (holds_mem h1.2.2.2.2 hp) (prod_localRule_bra L g _ _ _)
  by_cases hf1 : first L g = true
  · have hz : (tidOf L g / 32 % 4) ||| (tidOf L g % 32) = 0 := by simpa [first] using hf1
    rw [show decide ((tidOf L g / 32 % 4) ||| (tidOf L g % 32) ≠ 0) = false by simp [hz]] at ht1
    simp only [Bool.false_eq_true, ↓reduceIte] at ht1
    rw [epi_pc_barB_fence k] at ht1
    right
    refine ⟨⟨.fence k, m, n, m', n', cp, ap, resp, x, acc, base⟩, u1, by simp [next, hf1],
      run_rtg hr1, At.mono ht1 (epi_holds_facts_of ht1.2.2.2.2 (epi_fence_barB_sub k) fun _ _ =>
        rfl),
      ⟨hi.m, hi.n, hi.m', hi.n', hi.cp, hi.ap, hi.x⟩⟩
  · have hnz : (tidOf L g / 32 % 4) ||| (tidOf L g % 32) ≠ 0 := by simpa [first] using hf1
    rw [show decide ((tidOf L g / 32 % 4) ||| (tidOf L g % 32) ≠ 0) = true by simp [hnz]] at ht1
    simp only [↓reduceIte] at ht1
    obtain ⟨u2, hr2, ht2⟩ : ∃ u2, run kernel Prod L g 1 u1 = some u2 ∧
        At u2 (Site.commit k).pc (facts L g ⟨.commit k, m, n, m', n', cp, ap, resp, x, acc,
          base⟩) := by
      fin_cases k <;> cons_seg ht1 hpre
        [epi_setp_bounded (tidOf L g / 32 % 4 ||| tidOf L g % 32) (epi_lead_lt L g),
          epi_setp_none x hx]
    right
    refine ⟨⟨.commit k, m, n, m', n', cp, ap, resp, x, acc, base⟩, u2, by simp [next, hf1],
      run_rtg (run_comp hr1 hr2), ht2, ⟨hi.m, hi.n, hi.m', hi.n', hi.cp, hi.ap, hi.x⟩⟩

end
end PTX.Kernels.Fp16Gemm8192.Proof.Consumer
