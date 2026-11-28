-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.InklingRelDecode.Proof.Prologue.Data.QueryCarry
public import Kernels.InklingRelDecode.Proof.Prologue.Steps.PreloadGate
public import Lemmas.Flow.DataAdvanceF

@[expose] public section

/-! # The barrier before the preload loop: the data step

After the barrier, a launch without blocks runs to the query part; otherwise the first preload
block follows. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Prologue.Data
open PTX PTX.Proof PTX.Flow PTX.Flow.Code Control

noncomputable section

/-- The scale fact is a fact of every state before the query part. -/
theorem scale_dF {Q L g} (d : D) (h : Tag.scale ∈ tags d.c.site) :
    (525, scaleVal L) ∈ dF Q L g d := List.mem_map.mpr ⟨.scale, h, rfl⟩

theorem bar2_step {Q L g w m} (hp : Pre Q L m) (d : D) (hs : d.c.site = .bar2) :
    DataStep (code Q L g w) (dF Q L g) d := by
  have hc : kernel.code[(code Q L g w).pc d]? =
      some ⟨none, .barSyncN (.imm 0) (.imm 128) true⟩ := by
    show kernel.code[d.c.site.pc]? = _
    rw [hs]; exact Flow.code_180
  apply DataStep.advanceF (C' := code Q L g w) hc fires_barSyncN_next
    (by show d.c.site.sub = 0; rw [hs]; rfl) rfl
  intro e d' hn
  obtain ⟨c, hnc, rfl⟩ := succ_split hn
  have hsc : (code Q L g w).facts d = Control.facts Q L g w d.c 180 ++ dF Q L g d := by
    show Control.facts Q L g w d.c d.c.site.pc ++ _ = _
    rw [hs]; rfl
  rw [show (code Q L g w).pc d = 180 by show d.c.site.pc = _; rw [hs]; rfl, hsc]
  have hq : qside d.c.site = true := by rw [hs]; rfl
  have hnq : isQ d.c.site = false := by rw [hs]; rfl
  have hb : ¬ Bare d.c.site := by rw [hs]; decide
  have hscale : (525, scaleVal L) ∈ dF Q L g d := scale_dF d (by rw [hs]; decide)
  simp only [Control.next, hs, Option.some.injEq] at hnc
  by_cases hn0 : preloadN Q L g d.c = 0
  · have hn0' : preload Q.splits ((L.ctaidOf (g / L.block)).get Dim.x) d.c = 0 := hn0
    refine entry_reach (w := w) hp d.c ⟨c, record d e⟩ (p := 181)
      (SegU.sub_start (gate_to_316 (d := d.c) hp hn0) fun x hx => List.mem_append_left _ hx)
      (by rw [← hnc]; simp only [hn0', ↓reduceIte]) (fun n => by rw [← hnc]; rfl)
      (List.mem_append_right _ hscale) (by omega) (by omega)
  · have hn0' : ¬ preload Q.splits ((L.ctaidOf (g / L.block)).get Dim.x) d.c = 0 := hn0
    have hsite : c.site = .pb 0 0 := by rw [← hnc]; simp only [hn0', ↓reduceIte]
    have hd' : isQ c.site = false := by rw [hsite]; rfl
    refine reach_carry (d := d) (d' := ⟨c, record d e⟩) (fun τ hτ => ?_) ?_
      (by rw [hs]; simp [Site.pc]) (by omega) (by omega)
    · exact qcarry _ hq hnq _ (by rw [hs]; show c.site ∈ _; rw [hsite]; simp [succs]) hd' τ hτ
    · exact fun x hx => List.mem_append_right _ (carry_sub_q hq hnq hb hn hd' x hx)

theorem ptc3_fetch (b : Fin 3) : ∃ gd op, kernel.code[(Site.ptc b 3).pc]? = some ⟨gd, op⟩ ∧
    AdvancesOp op := by
  fin_cases b
  · exact ⟨_, _, Flow.code_231, trivial⟩
  · exact ⟨_, _, Flow.code_273, trivial⟩
  · exact ⟨_, _, Flow.code_315, trivial⟩

/-- **The site after the last copy issue** is the next block or the query part. -/
theorem afterCopy3 (d : Control.D) (tid n : Nat) (b : Fin 3) :
    (∃ b', afterCopy d tid n b 3 = .pb b' 0 ∧ (Site.pb b' 0) ∈ succs (.ptc b 3)) ∨
    (afterCopy d tid n b 3 = querySite tid d 0 ∧ (b = 0 → n = 1) ∧ (b = 1 → n < 3)) := by
  fin_cases b <;> simp only [afterCopy, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    split_ifs <;> first
    | (exfalso; omega)
    | exact .inr ⟨rfl, by omega, by omega⟩
    | exact .inl ⟨_, rfl, by simp [succs, afterC]⟩

theorem ptc3_pc : ∀ b : Fin 3, 27 ≤ (Site.ptc b 3).pc + 1 ∧ (Site.ptc b 3).pc + 1 ≤ 316 := by
  decide +kernel

theorem ptc3_nb : ∀ b : Fin 3, ¬ Bare (.ptc b 3) ∧ Tag.scale ∈ tags (.ptc b 3) ∧
    qside (.ptc b 3) = true ∧ isQ (.ptc b 3) = false := by decide +kernel

theorem ptc3_step {Q L g w m} (hp : Pre Q L m) (d : D) (b : Fin 3) (hs : d.c.site = .ptc b 3) :
    DataStep (code Q L g w) (dF Q L g) d := by
  obtain ⟨gd, op, hcode, hadv⟩ := ptc3_fetch b
  have hc : kernel.code[(code Q L g w).pc d]? = some ⟨gd, op⟩ := by
    show kernel.code[d.c.site.pc]? = _
    rw [hs]; exact hcode
  apply DataStep.advanceF (C' := code Q L g w) hc (fun hf => fires_next hadv hf)
    (by show d.c.site.sub = 0; rw [hs]; rfl) rfl
  intro e d' hn
  obtain ⟨c, hnc, rfl⟩ := succ_split hn
  have hsc : (code Q L g w).facts d =
      Control.facts Q L g w d.c (Site.ptc b 3).pc ++ dF Q L g d := by
    show Control.facts Q L g w d.c d.c.site.pc ++ _ = _
    rw [hs]
  rw [show (code Q L g w).pc d = (Site.ptc b 3).pc by show d.c.site.pc = _; rw [hs], hsc]
  obtain ⟨hnb, hsc', hq, hnq⟩ := ptc3_nb b
  rw [← hs] at hnb hsc' hq hnq
  have hscale : (525, scaleVal L) ∈ dF Q L g d := scale_dF d hsc'
  simp only [Control.next, hs, Option.some.injEq] at hnc
  have hpp := ptc3_pc b
  rcases afterCopy3 d.c (g % L.block) (preloadN Q L g d.c) b with ⟨b', hb', hmem⟩ | ⟨hq', h0, h1⟩
  · have hsite : c.site = .pb b' 0 := by rw [← hnc]; exact hb'
    have hd' : isQ c.site = false := by rw [hsite]; rfl
    refine reach_carry (d := d) (d' := ⟨c, record d e⟩) (fun τ hτ => ?_) ?_
      (by rw [hs]; omega) (by omega) (by omega)
    · exact qcarry _ hq hnq _ (by rw [hs]; show c.site ∈ _; rw [hsite]; exact hmem) hd' τ hτ
    · exact fun x hx => List.mem_append_right _ (carry_sub_q hq hnq hnb hn hd' x hx)
  · refine entry_reach (w := w) hp d.c ⟨c, record d e⟩ (p := (Site.ptc b 3).pc + 1)
      (SegU.sub_start (copy_tail_316 (d := d.c) (w := w) b h0 h1) (by
        intro x hx; exact List.mem_append_left _ hx))
      (by rw [← hnc]; exact hq') (fun n => by rw [← hnc]; rfl)
      (List.mem_append_right _ hscale) hpp.1 hpp.2

end
end PTX.Kernels.InklingRelDecode.Proof.Prologue.Data
