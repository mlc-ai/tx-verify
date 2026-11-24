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

theorem step_commit_7 {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat} {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hpre : Pre P L mem0) (hs : d.site = .commit 7) (hi : Inv d)
    (h : At t d.site.pc (facts L g d)) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) :
    epi_cont L g d e u := by
  obtain ⟨s, m, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs h hc hf hi ⊢
  subst hs
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_bulkCommit_7)
  obtain rfl := fires_async_next (show AsyncAdvancesOp .bulkCommit from trivial) hf
  have hcp : cp < 2 := hi.cp
  have hap : ap < 2 := hi.ap
  have h1 := At.next h
  obtain ⟨t1, hr1, ht1⟩ : ∃ t1, run kernel Prod L g 4 (PTX.next t) = some t1 ∧
      At t1 Flow.bra_1085 (factsAt L g Flow.bra_1085
        ⟨.commit 7, m', n', m', n', 1 - cp, 1 - ap, resp, x, acc, base⟩) := by
    cons_seg h1 hpre [epi_flip_bits cp hcp, epi_flip_bits ap hap]
  have hp : (19, Value.pred (decide (x ≠ Loader.none32))) ∈ factsAt L g Flow.bra_1085
      ⟨.commit 7, m', n', m', n', 1 - cp, 1 - ap, resp, x, acc, base⟩ := by
    have hv : valueOf L g ⟨.commit 7, m', n', m', n', 1 - cp, 1 - ap, resp, x, acc, base⟩ 19 =
        Value.pred (decide (x ≠ Loader.none32)) := by
      cons_values
    rw [← hv]
    exact Flow.mem_factsFrom (by table_decide)
  obtain ⟨t2, hr2, ht2⟩ := run_bra (K := kernel) (A := Prod) (L := L) (g := g) Flow.code_1085
    (decide (x ≠ Loader.none32)) ht1 (holds_mem ht1.2.2.2.2 hp)
    (prod_localRule_bra L g _ _ _)
  right
  by_cases hx : x = Loader.none32
  · rw [show decide (x ≠ Loader.none32) = false by simp [hx]] at ht2
    simp only [Bool.false_eq_true, ↓reduceIte] at ht2
    refine ⟨⟨.finalDrain, m, n, m', n', cp, ap, resp, x, acc, base⟩, t2, by simp [next, hx],
      run_rtg (run_comp hr1 hr2), At.mono ht2 (epi_holds_facts_of ht2.2.2.2.2 epi_finalDrain_sub
        (epi_finalDrain_val L g _ _)), ⟨hi.m, hi.n, hi.m', hi.n', hi.cp, hi.ap, hi.x⟩⟩
  · rw [show decide (x ≠ Loader.none32) = true by simp [hx]] at ht2
    simp only [↓reduceIte] at ht2
    obtain ⟨t3, hr3, ht3⟩ : ∃ t3, run kernel Prod L g 4 t2 = some t3 ∧
        At t3 Site.clcWait.pc (facts L g ⟨.clcWait, m', n', m', n', 1 - cp, 1 - ap, resp, x, acc,
          base⟩) := by
      cons_seg ht2 hpre [epi_setp_bounded (tidOf L g / 32 % 4 ||| tidOf L g % 32) (epi_lead_lt L g)]
    refine ⟨⟨.clcWait, m', n', m', n', 1 - cp, 1 - ap, resp, x, acc, base⟩, t3,
      by simp [next, hx], run_rtg (run_comp (run_comp hr1 hr2) hr3), ht3,
      ⟨hi.m', hi.n', hi.m', hi.n', (show 1 - cp < 2 by omega), (show 1 - ap < 2 by omega), hi.x⟩⟩

end
end PTX.Kernels.Fp16Gemm8192.Proof.Consumer
