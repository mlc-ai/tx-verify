-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.Thread.StepBf

@[expose] public section

/-! # The barriers and warp 0's load of a warp sum

After the first barrier, warps 1..7 continue at the second barrier; in warp 0, lanes 0..7 load
the sum of their warp, lanes 8..31 enter the second butterfly with the integer `0`. A loaded
warp sum that is no four-byte value makes the shuffle undefined. After the second barrier every
thread loads the total. After the third barrier the row index advances by the grid size: the
thread enters the next row or exits. -/

namespace PTX.Kernels.RmsNorm.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

local notation "Prod" => [Assumptions.idealArith, Assumptions.exactApprox]

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- `setp.ne (and.b32 tid, 24), 0` for a thread of warp 0: true from thread 8 on. -/
theorem setp_and24 {a : Nat} (h : a < 32) :
    compare .ne .b 32
      (truncBits 32 (truncBits 32 (BitVec.ofNat 64 a) &&& truncBits 32 (BitVec.ofInt 64 24)))
      (truncBits 32 (BitVec.ofInt 64 0)) = decide (8 ≤ a) := by
  interval_cases a <;> rfl

theorem step_bar0 (hpre : Pre P L mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .bar0) (hi : Inv P g d) (h : (code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Cont P L g d e u := by
  have hat := at_site hs hi h rfl
  rms_hyps hpre
  have hsub : d.sub = 0 := hi.sub.2 (by simp [hs, Site.vec])
  have hacc : d.acc = [] := List.eq_nil_of_length_eq_zero (by simpa [hs, Site.vload] using hi.acc)
  have hrow := hi.row (by simp [hs, Site.inRow])
  rw [tmpl_site hpre hi h hc] at hf
  simp only [siteTmpl, hs] at hf
  obtain ⟨rfl, hu⟩ := hf
  cases hu
  have h1 : At (PTX.next t) (Flow.bar_0 + 1) (factsAt P g (Flow.bar_0 + 1) d) :=
    At.mono (At.next hat) (Flow.holds_factsFrom_mono hat.2.2.2.2 (by table_decide))
  obtain ⟨u1, hr1, hu1⟩ := run_bra (K := kernel) (A := Prod) (L := L) (g := g) Flow.code_115
    (decide (31 < g % 256)) h1 (reg_of h1.2.2.2.2 (by table_decide))
    (localRule_bra L g _ _ _)
  by_cases h31 : 31 < g % 256
  · have hd : decide (31 < g % 256) = true := by simp [h31]
    rw [hd] at hu1
    simp only [↓reduceIte] at hu1
    obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 2 u1 = some t' ∧
        At t' Site.bar1.pc (facts P g { d with site := .bar1 }) := by
      seg_fp hu1 using
        rms_values
        all_goals seg_close
    refine .inl ⟨{ d with site := .bar1 }, t', by simp [next, hs, h31],
      run_rtg (run_comp hr1 hr'), atD_of hsub hacc ht', ?_⟩
    inv_tac
  · have hd : decide (31 < g % 256) = false := by simp [h31]
    rw [hd] at hu1
    simp only [Bool.false_eq_true, ↓reduceIte] at hu1
    have ht : g % 256 < 32 := by omega
    obtain ⟨u2, hr2, hu2⟩ : ∃ t', run kernel Prod L g 3 u1 = some t' ∧
        At t' Flow.bra_119 (factsAt P g Flow.bra_119 { d with u := b32 0 }) := by
      seg_fp hu1 using
        rms_values
        all_goals seg_close [setp_and24 ht]
    obtain ⟨u3, hr3, hu3⟩ := run_bra (K := kernel) (A := Prod) (L := L) (g := g) Flow.code_119
      (decide (8 ≤ g % 256)) hu2 (reg_of hu2.2.2.2.2 (by table_decide))
      (localRule_bra L g _ _ _)
    have hl : Relation.ReflTransGen (Tau kernel Prod L g) (PTX.next t) u3 :=
      run_rtg (run_comp (run_comp hr1 hr2) hr3)
    by_cases h8 : 8 ≤ g % 256
    · have hd8 : decide (8 ≤ g % 256) = true := by simp [h8]
      rw [hd8] at hu3
      simp only [↓reduceIte] at hu3
      obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 4 u3 = some t' ∧
          At t' (Site.bfb 0).pc (facts P g { d with site := .bfb 0, u := b32 0 }) := by
        seg_fp hu3 using
          rms_values
          all_goals seg_close
      refine .inl ⟨{ d with site := .bfb 0, u := b32 0 }, t',
        by simp [next, hs, h31, show ¬ g % 256 < 8 by omega],
        hl.trans (run_rtg hr'), atD_of hsub hacc ht', ?_⟩
      inv_tac
    · have hd8 : decide (8 ≤ g % 256) = false := by simp [h8]
      rw [hd8] at hu3
      simp only [Bool.false_eq_true, ↓reduceIte] at hu3
      obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 4 u3 = some t' ∧
          At t' Site.ldws.pc (facts P g { d with site := .ldws }) := by
        seg_fp hu3 using
          rms_values
          all_goals seg_close [hpre.hyp.shared]
      refine .inl ⟨{ d with site := .ldws }, t', by simp [next, hs, h31, show g % 256 < 8 by omega],
        hl.trans (run_rtg hr'), atD_of hsub hacc ht', ?_⟩
      inv_tac

theorem step_bar1 (hpre : Pre P L mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .bar1) (hi : Inv P g d) (h : (code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Cont P L g d e u := by
  have hat := at_site hs hi h rfl
  rms_hyps hpre
  have hsub : d.sub = 0 := hi.sub.2 (by simp [hs, Site.vec])
  have hacc : d.acc = [] := List.eq_nil_of_length_eq_zero (by simpa [hs, Site.vload] using hi.acc)
  have hrow := hi.row (by simp [hs, Site.inRow])
  rw [tmpl_site hpre hi h hc] at hf
  simp only [siteTmpl, hs] at hf
  obtain ⟨rfl, hu⟩ := hf
  cases hu
  have h1 : At (PTX.next t) (Flow.bar_1 + 1) (factsAt P g (Flow.bar_1 + 1) d) :=
    At.mono (At.next hat) (Flow.holds_factsFrom_mono hat.2.2.2.2 (by table_decide))
  obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 2 (PTX.next t) = some t' ∧
      At t' Site.ldts.pc (facts P g { d with site := .ldts }) := by
    seg_fp h1 using
      rms_values
      all_goals seg_close [hpre.hyp.shared]
  refine .inl ⟨{ d with site := .ldts }, t', by simp [next, hs], run_rtg hr',
    atD_of hsub hacc ht', ?_⟩
  inv_tac

theorem step_bar2 (hpre : Pre P L mem0) {d : D} {t u : TState} {e : Event} {ins : Instr}
    (hs : d.site = .bar2) (hi : Inv P g d) (h : (code P L g).AtD d t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e (some u)) : Cont P L g d e u := by
  have hat := at_site hs hi h rfl
  rms_hyps hpre
  have hsub : d.sub = 0 := hi.sub.2 (by simp [hs, Site.vec])
  have hacc : d.acc = [] := List.eq_nil_of_length_eq_zero (by simpa [hs, Site.vload] using hi.acc)
  have hrow := hi.row (by simp [hs, Site.inRow])
  rw [tmpl_site hpre hi h hc] at hf
  simp only [siteTmpl, hs] at hf
  obtain ⟨rfl, hu⟩ := hf
  cases hu
  have hrow' : g / 256 + 152 * d.i < P.Bt := hrow
  have h1 : At (PTX.next t) (Flow.bar_2 + 1) (factsAt P g (Flow.bar_2 + 1) d) :=
    At.mono (At.next hat) (Flow.holds_factsFrom_mono hat.2.2.2.2 (by table_decide))
  obtain ⟨u1, hr1, hu1⟩ : ∃ t', run kernel Prod L g 3 (PTX.next t) = some t' ∧
      At t' Flow.bra_293 (factsAt P g Flow.bra_293 { d with i := d.i + 1 }) := by
    seg_fp h1 using
      rms_values
      all_goals seg_close [row]
  obtain ⟨u2, hr2, hu2⟩ := run_bra (K := kernel) (A := Prod) (L := L) (g := g) Flow.code_293
    (decide (row g (d.i + 1) < P.Bt)) hu1 (reg_of hu1.2.2.2.2 (by table_decide))
    (localRule_bra L g _ _ _)
  have hl : Relation.ReflTransGen (Tau kernel Prod L g) (PTX.next t) u2 :=
    run_rtg (run_comp hr1 hr2)
  by_cases hn : row g (d.i + 1) < P.Bt
  · have hn' : g / 256 + 152 * (d.i + 1) < P.Bt := hn
    have hd : decide (row g (d.i + 1) < P.Bt) = true := by simp [hn]
    rw [hd] at hu2
    simp only [↓reduceIte] at hu2
    obtain ⟨t', hr', ht'⟩ : ∃ t', run kernel Prod L g 3 u2 = some t' ∧
        At t' Site.ldxa.pc (facts P g { d with site := .ldxa, i := d.i + 1 }) := by
      seg_fp hu2 using
        rms_values
        all_goals seg_close [row, off]
    refine .inl ⟨{ d with site := .ldxa, i := d.i + 1 }, t', by simp [next, hs, hn],
      hl.trans (run_rtg hr'), atD_of hsub hacc ht', ?_⟩
    have := hn
    inv_tac
  · have hd : decide (row g (d.i + 1) < P.Bt) = false := by simp [hn]
    rw [hd] at hu2
    simp only [Bool.false_eq_true, ↓reduceIte] at hu2
    refine .inl ⟨{ d with site := .exit, i := d.i + 1 }, u2, by simp [next, hs, hn], hl,
      ⟨hu2.1, hu2.2.1.trans hsub.symm, hu2.2.2.1.trans hacc.symm, hu2.2.2.2.1, holds_exit rfl⟩, ?_⟩
    inv_tac

end
end PTX.Kernels.RmsNorm.Proof
