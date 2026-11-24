-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.Thread.Cont

@[expose] public section

/-! # The step of the warp-index shuffle

After the shuffle, whose result the code never reads, the thread reads its CTA index: a CTA
without a row exits, any other enters its first row. -/

namespace PTX.Kernels.RmsNorm.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

local notation "Prod" => [Assumptions.idealArith, Assumptions.exactApprox]

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

theorem step_shfl0 (hpre : Pre P L mem0) (hg : g < L.threads) {d : D} {t u : TState}
    {e : Event} {ins : Instr} (hs : d.site = .shfl0) (hi : Inv P g d) (h : (code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Cont P L g d e u := by
  have hd0 : d.sub = 0 ∧ d.acc = [] :=
    ⟨hi.sub.2 (by simp [hs, Site.vec]), List.eq_nil_of_length_eq_zero
      (by simpa [hs, Site.vload] using hi.acc)⟩
  have hat : At t Site.shfl0.pc (factsAt P g Site.shfl0.pc d) := by
    have : At t d.site.pc (factsAt P g d.site.pc d) := at_of_atD (L := L) hd0.1 hd0.2 h
    rwa [hs] at this
  rw [hs] at hc hf
  obtain rfl := Option.some.inj (hc.symm.trans Flow.code_shfl_0)
  rw [tmpl_shfl0 hpre (reg_of hat.2.2.2.2 (by table_decide))] at hf
  obtain ⟨recv, ok, rfl, hu⟩ := hf
  cases hu
  have hB := hpre.hyp.block
  rms_hyps hpre
  have hgrid : g / 256 < 152 := by
    have := hg; simp only [Launch.threads, hpre.hyp.grid, hB] at this; omega
  have hcta := Launch.oneDim_ctaidOf hpre.hyp.oneDimLaunch.1 (g / L.block)
  have h7 : At (PTX.next (setReg (setReg t 46 recv) 1 (.pred ok))) (Flow.shfl_0 + 1)
      (factsAt P g (Flow.shfl_0 + 1) d) := by
    refine ⟨by simp only [PTX.next, setReg, hat.1]; rfl, hat.2.1, hat.2.2.1,
                 by simpa [PTX.next, setReg] using hat.2.2.2.1, ?_⟩
    have hframe : ∀ r, r ∉ [46, 1] →
        (PTX.next (setReg (setReg t 46 recv) 1 (.pred ok))).regs r = t.regs r := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [PTX.next, setReg, Function.update_of_ne hr.1, Function.update_of_ne hr.2]
    frame_fp hat.2.2.2.2, hframe
    trivial
  obtain ⟨t9, hr9, h9⟩ : ∃ t', run kernel Prod L g 2 (PTX.next
    (setReg (setReg t 46 recv) 1 (.pred ok))) = some t' ∧
      At t' Flow.bra_9 (factsAt P g Flow.bra_9 { d with site := .ldxa, i := 0 }) := by
    -- `%ctaid` is the launch's `ctaidOf`, so the geometry fact `hcta` (with the block size) is
    -- what reduces it to the row's CTA number.
    seg_fp h7 using
      rms_values
      all_goals
        rw [hcta, hB]
        first
          | (show Value.bits _ _ = _; norm_bits [row, Dim3.get])
          | (show Value.pred _ = _; norm_cmp [Dim3.get])
  have hl0 : Relation.ReflTransGen (Tau kernel Prod L g)
    (PTX.next (setReg (setReg t 46 recv) 1 (.pred ok))) t9 :=
    run_rtg hr9
  obtain ⟨u1, hr1, hu1⟩ := run_bra (K := kernel) (A := Prod) (L := L) (g := g) Flow.code_9
    (decide (P.Bt ≤ g / 256)) h9 (reg_of h9.2.2.2.2 (by table_decide))
    (localRule_bra L g _ _ _)
  by_cases hrow : g / 256 < P.Bt
  · have hd : decide (P.Bt ≤ g / 256) = false := by simp; omega
    rw [hd] at hu1
    simp only [Bool.false_eq_true, ↓reduceIte] at hu1
    have h10 : At u1 (Flow.bra_9 + 1) (factsAt P g (Flow.bra_9 + 1)
      { d with site := .ldxa, i := 0 }) :=
      At.mono hu1 (Flow.holds_factsFrom_mono hu1.2.2.2.2 (by table_decide))
    obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 19 u1 = some t' ∧
        At t' Site.ldxa.pc (facts P g { d with site := .ldxa, i := 0 }) := by
      seg_fp h10 using
        rms_values
        all_goals first
          | seg_close [sregValue, hB, row, off, hpre.hyp.shared]
          | (nf_simp [sregValue, hB, row, off, hpre.hyp.shared]; rw [lor_4096] <;> omega)
    refine .inl ⟨{ d with site := .ldxa, i := 0 }, t', by simp [next, hs, hrow],
      hl0.trans (run_rtg (run_comp hr1 hr')), atD_of hd0.1 hd0.2 ht', ?_⟩
    have := hd0.1; have := hd0.2
    inv_tac
  · have hd : decide (P.Bt ≤ g / 256) = true := by simp; omega
    rw [hd] at hu1
    simp only [↓reduceIte] at hu1
    refine .inl ⟨{ d with site := .exit }, u1, by simp [next, hs, hrow],
      hl0.trans (run_rtg hr1), ⟨hu1.1, hu1.2.1.trans hd0.1.symm, hu1.2.2.1.trans hd0.2.symm,
        hu1.2.2.2.1, holds_exit rfl⟩, ?_⟩
    have := hd0.1; have := hd0.2
    inv_tac

end
end PTX.Kernels.RmsNorm.Proof
