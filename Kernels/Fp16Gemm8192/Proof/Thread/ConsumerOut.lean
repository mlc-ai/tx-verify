-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerExit
public import Kernels.Fp16Gemm8192.Proof.Thread.ConsumerOutDefs
public import Lemmas.Flow.Bar
public import Lemmas.Flow.BulkCount
public import Lemmas.Flow.OpPcsFast

@[expose] public section

/-! # The consumer's output barriers and bulk commits

Each slice of a consumer's epilogue passes its group's output barrier twice (before and after
the staging stores) and commits one bulk group. Along a consumer's run, its arrivals on the output
barrier (`Consumer.outBars`) count the slices it began, modulo the eight slices of a tile
(`D.outPhase`), and its commits trail them by the slice's position (`D.outLag`): `OutRel`. -/

namespace PTX.Kernels.Fp16Gemm8192.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-- The kernel's named barriers are at its barrier sites (decided on the code). -/
theorem kernel_bar_pcs : OpPcs kernel.code barOp Flow.bar.toList = true :=
  OpPcsFast.opPcs (by decide +kernel)

/-- The kernel's bulk commits are at its commit sites (decided on the code). -/
theorem kernel_commit_pcs : OpPcs kernel.code bulkCommitOp Flow.bulkCommit.toList = true :=
  OpPcsFast.opPcs (by decide +kernel)

namespace Consumer

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

theorem counts_snoc (es : List Event) (e : Event) :
    outBars L g (es ++ [e]) = outBars L g es + (if isOutBar L g e then 1 else 0) ∧
    commits (es ++ [e]) = commits es + (if isCommit e then 1 else 0) := by
  simp [outBars, commits, List.countP_append]

theorem OutRel.keep {d d' : D} {es : List Event} {e : Event} (h : OutRel L g d es)
    (hb : isOutBar L g e = false) (hc : isCommit e = false) (hp : d'.outPhase = d.outPhase)
    (hl : d'.outLag = d.outLag) : OutRel L g d' (es ++ [e]) := by
  obtain ⟨h1, h2⟩ := counts_snoc (L := L) (g := g) es e
  simp only [hb, hc, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at h1 h2
  unfold OutRel
  rw [h1, h2, hp, hl]
  exact h

/-- A named barrier of a consumer is at its group's CLC barrier or a slice's barrier. -/
theorem bar_site {d : D} {t : TState} {ins : Instr} {e : Event} {o : Option TState}
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) {id : Nat} {c : Option Nat}
    {m : BarMode} (hk : e.kind = .bar id c m) :
    d.site = .clcBar ∨ (∃ k, d.site = .barA k) ∨ ∃ k, d.site = .barB k := by
  have hpc := OpPcs.mem kernel_bar_pcs hc (fires_bar_op hf hk)
  clear hc hf hk
  site_of_pc d hpc

/-- A slice's barrier is an arrival on the group's output barrier, counting its 128 threads. -/
theorem out_bar_event (hpre : Pre P L mem0) {d : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hat : (code L g).AtD (.inr (.cons d)) t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) {k : Fin 8}
    (hs : d.site = .barA k ∨ d.site = .barB k) :
    e = ⟨d.site.pc, .bar (outId L g) (some 128)⟩ := by
  have hblock := hpre.block
  have htid : tidOf L g < 384 := by rw [← hblock]; exact Nat.mod_lt _ (by omega)
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs hc hf hat ⊢
  rcases hs with rfl | rfl <;> fin_cases k <;> code_at hc <;> subst hc <;>
    exact fires_barN (id := tidOf L g / 32 / 4 + 10) (n := 128)
      ((holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
        (congrArg some (by cons_values))) (by omega) (by decide) (by decide) (by decide)
      (by omega) hf

/-- The group's CLC barrier is an arrival on its CLC barrier, counting its 128 threads. -/
theorem clcBar_event (hpre : Pre P L mem0) {d : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hat : (code L g).AtD (.inr (.cons d)) t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) (hs : d.site = .clcBar) :
    e = ⟨d.site.pc, .bar (tidOf L g / 32 / 4 + 1) (some 128)⟩ := by
  have hblock := hpre.block
  have htid : tidOf L g < 384 := by rw [← hblock]; exact Nat.mod_lt _ (by omega)
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  simp only at hs hc hf hat ⊢
  subst hs
  code_at hc
  subst hc
  exact fires_barN (id := tidOf L g / 32 / 4 + 1) (n := 128)
    ((holds_mem hat.2.2.2.2 (Flow.mem_factsFrom (by lit_mem))).trans
      (congrArg some (by cons_values))) (by omega) (by decide) (by decide) (by decide)
    (by omega) hf

theorem out_step (hpre : Pre P L mem0) {d d' : D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} {pre : List Event} (hat : (code L g).AtD (.inr (.cons d)) t)
    (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) (hn : next L g d e = some (some d'))
    (hq : OutRel L g d pre) : OutRel L g d' (pre ++ [e]) := by
  have hNB : (∀ k, d.site ≠ .barA k) → (∀ k, d.site ≠ .barB k) → isOutBar L g e = false := by
    intro hA hB
    by_cases hbar : ∃ id c m, e.kind = .bar id c m
    · obtain ⟨id, c, m, hk⟩ := hbar
      rcases bar_site hc hf hk with hs | ⟨k, hs⟩ | ⟨k, hs⟩
      · rw [clcBar_event hpre hat hc hf hs]; simp [isOutBar]
      · exact absurd hs (hA k)
      · exact absurd hs (hB k)
    · unfold isOutBar
      split
      · rename_i id c m hk
        exact absurd ⟨id, c, m, hk⟩ hbar
      · rfl
  have hNC : (∀ k, d.site ≠ .commit k) → isCommit e = false := by
    intro hC
    by_cases hcm : e.kind = .bulkCommit
    · have hpc := OpPcs.mem kernel_commit_pcs hc (fires_bulkCommit_op hf hcm)
      obtain ⟨k, hs⟩ : ∃ k, d.site = .commit k := by
        clear hat hn hq hNB hC hc hf hcm
        site_of_pc d hpc
      exact absurd hs (hC k)
    · unfold isCommit
      split
      · rename_i hk
        exact absurd hk hcm
      · rfl
  obtain ⟨hb1, hc1⟩ := counts_snoc (L := L) (g := g) pre e
  obtain ⟨h1, h2⟩ := hq
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  cases site
  case barA k =>
    have he := out_bar_event hpre hat hc hf (k := k) (.inl rfl)
    subst he
    simp only [next, Option.some.injEq] at hn
    subst hn
    simp only [isOutBar, decide_true, ↓reduceIte, isCommit, Bool.false_eq_true,
      Nat.add_zero] at hb1 hc1
    simp only [D.outPhase, D.outLag] at h1 h2
    refine ⟨?_, ?_⟩ <;> simp only [D.outPhase, D.outLag, hb1, hc1] <;> omega
  case barB k =>
    have he := out_bar_event hpre hat hc hf (k := k) (.inr rfl)
    subst he
    simp only [isOutBar, decide_true, ↓reduceIte, isCommit, Bool.false_eq_true,
      Nat.add_zero] at hb1 hc1
    simp only [D.outPhase, D.outLag] at h1 h2
    simp only [next] at hn
    split_ifs at hn <;> simp only [Option.some.injEq] at hn <;> subst hn <;>
      refine ⟨?_, ?_⟩ <;> simp only [D.outPhase, D.outLag, hb1, hc1] <;> omega
  case commit k =>
    have he : e = ⟨(Site.commit k).pc, .bulkCommit⟩ := by
      obtain ⟨ins', hc', -⟩ := epi_commit_code k
      have := hc.symm.trans hc'
      fin_cases k <;> code_at hc <;> subst hc <;> exact fires_bulkCommit hf
    subst he
    simp only [isOutBar, Bool.false_eq_true, ↓reduceIte, isCommit, Nat.add_zero] at hb1 hc1
    simp only [D.outPhase, D.outLag] at h1 h2
    simp only [next] at hn
    split_ifs at hn <;> simp only [Option.some.injEq] at hn <;> subst hn <;>
      refine ⟨?_, ?_⟩ <;> simp only [D.outPhase, D.outLag, hb1, hc1] <;> omega
  all_goals have hb := hNB (fun _ h => by cases h) (fun _ h => by cases h)
  all_goals have hcm := hNC (fun _ h => by cases h)
  all_goals clear hNB hNC hat hc hf
  all_goals refine OutRel.keep ⟨h1, h2⟩ hb hcm ?_ ?_
  all_goals simp only [next] at hn
  clc_sweep hn
  all_goals simp [D.outPhase, D.outLag]

/-- The output barrier arrivals and the accumulator releases of a consumer: each release of an
accumulator (`accArrive`) starts an epilogue of sixteen barrier arrivals, so its arrivals, plus the
sixteen of the epilogue in progress, are sixteen per release plus the slice's position
(`D.outPhase`); and a state that has started an epilogue (`D.started`) has had a release. -/
def OutTile (L : Launch) (g : Nat) (d : D) (es : List Event) : Prop :=
  outBars L g es + 16 * d.inEpi = 16 * arrivals (accEmpty L g (accIdx L g)) es + d.outPhase ∧
    d.started ≤ arrivals (accEmpty L g (accIdx L g)) es

/-- A consumer arrives on its accumulator's empty barrier only at its accumulator release. -/
theorem arrives_acc_site (hpre : Pre P L mem0) (hg : g < L.threads) {d : D} {t : TState}
    {ins : Instr} {e : Event} {o : Option TState}
    (hat : (code L g).AtD (.inr (.cons d)) t) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) :
    arrivesOn (accEmpty L g (accIdx L g)) e = true → d.site = .accArrive := by
  have hw := group_lt (g := g) hpre
  intro har
  obtain ⟨tx, n, rel, sc, hk⟩ := arrivesOn_form har
  rcases arrive_site hpre hg hat.2.2.2.2 hc hf hk with ⟨h1, -⟩ | ⟨-, hl⟩
  · exact h1
  · simp only [Bar.loc, Bar.off, accIdx] at hl
    omega

set_option maxHeartbeats 8000000 in
theorem tile_step (hpre : Pre P L mem0) (hg : g < L.threads) {d d' : D} {t : TState}
    {ins : Instr} {e : Event} {o : Option TState} {pre : List Event}
    (hat : (code L g).AtD (.inr (.cons d)) t) (hc : kernel.code[d.site.pc]? = some ins)
    (hf : Fires d.site.pc (eventTmpl Prod L g t ins.op) e o) (hn : next L g d e = some (some d'))
    (hq : OutTile L g d pre) : OutTile L g d' (pre ++ [e]) := by
  have hR := arrives_acc_site hpre hg hat hc hf
  have hR0 : d.site ≠ .accArrive → arrivesOn (accEmpty L g (accIdx L g)) e = false :=
    fun hs => Bool.eq_false_iff.mpr fun h' => hs (hR h')
  have hNB : (∀ k, d.site ≠ .barA k) → (∀ k, d.site ≠ .barB k) → isOutBar L g e = false := by
    intro hA hB
    by_cases hbar : ∃ id c m, e.kind = .bar id c m
    · obtain ⟨id, c, m, hk⟩ := hbar
      rcases bar_site hc hf hk with hs | ⟨k, hs⟩ | ⟨k, hs⟩
      · rw [clcBar_event hpre hat hc hf hs]; simp [isOutBar]
      · exact absurd hs (hA k)
      · exact absurd hs (hB k)
    · unfold isOutBar
      split
      · rename_i id c m hk
        exact absurd ⟨id, c, m, hk⟩ hbar
      · rfl
  obtain ⟨hb1, -⟩ := counts_snoc (L := L) (g := g) pre e
  unfold OutTile at hq ⊢
  rw [hb1, arrivals_snoc]
  obtain ⟨site, mm, n, m', n', cp, ap, resp, x, acc, base⟩ := d
  cases site
  case barA k =>
    have he := out_bar_event hpre hat hc hf (k := k) (.inl rfl)
    subst he
    have ha := hR0 (by simp)
    simp only [next, Option.some.injEq] at hn
    subst hn
    simp only [isOutBar, decide_true, ↓reduceIte, ha, Bool.false_eq_true, Nat.add_zero] at hq ⊢
    simp only [D.outPhase, D.inEpi, D.started] at hq ⊢
    refine ⟨by omega, by omega⟩
  case barB k =>
    have he := out_bar_event hpre hat hc hf (k := k) (.inr rfl)
    subst he
    have ha := hR0 (by simp)
    simp only [isOutBar, decide_true, ↓reduceIte, ha, Bool.false_eq_true, Nat.add_zero] at hq ⊢
    simp only [D.outPhase, D.inEpi, D.started] at hq
    simp only [next] at hn
    split_ifs at hn <;> simp only [Option.some.injEq] at hn <;> subst hn <;>
      simp only [D.outPhase, D.inEpi, D.started] <;> refine ⟨by omega, by omega⟩
  case accArrive =>
    obtain ⟨rel, sc, rfl⟩ := accArrive_event hpre hg rfl hat.2.2.2.2 hc hf
    have hb := hNB (fun _ h => by cases h) (fun _ h => by cases h)
    simp only [next, Option.some.injEq] at hn
    subst hn
    simp only [hb, arrivesOn_arrive rfl, decide_true, ↓reduceIte, Bool.false_eq_true,
      Nat.add_zero] at hq ⊢
    simp only [D.outPhase, D.inEpi, D.started] at hq ⊢
    refine ⟨by omega, by omega⟩
  case commit k =>
    have hb := hNB (fun _ h => by cases h) (fun _ h => by cases h)
    have ha := hR0 (by simp)
    simp only [hb, ha, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hq ⊢
    simp only [D.outPhase, D.inEpi, D.started] at hq
    simp only [next] at hn
    split_ifs at hn <;> simp only [Option.some.injEq] at hn <;> subst hn <;>
      simp only [D.outPhase, D.inEpi, D.started] <;> refine ⟨by omega, by omega⟩
  all_goals have hb := hNB (fun _ h => by cases h) (fun _ h => by cases h)
  all_goals have ha := hR0 (by simp)
  all_goals clear hNB hR hR0 hat hc hf
  all_goals simp only [hb, ha, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hq ⊢
  all_goals simp only [next] at hn
  all_goals revert hq
  clc_sweep hn
  all_goals first
    | (simp [D.outPhase, D.inEpi, D.started]; done)
    | (simp [D.outPhase, D.inEpi, D.started]; intros; omega)

end Consumer

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- No prologue event is a barrier arrival or a bulk commit. -/
theorem prologue_no_bar {p : Prologue.D} {t : TState} {ins : Instr} {e : Event}
    {o : Option TState} (hc : kernel.code[p.site.pc]? = some ins)
    (hf : Fires p.site.pc (eventTmpl Prod L g t ins.op) e o) :
    Consumer.isOutBar L g e = false ∧ isCommit e = false := by
  obtain ⟨site, w⟩ := p
  simp only at hc hf
  constructor
  · unfold Consumer.isOutBar; split
    · rename_i id c m hk
      have hpc := OpPcs.mem kernel_bar_pcs hc (fires_bar_op hf hk)
      clear hc hf hk; exfalso; revert hpc
      cases site <;> simp only [Prologue.Site.pc] <;> decide +revert
    · rfl
  · unfold isCommit; split
    · rename_i hk
      have hpc := OpPcs.mem kernel_commit_pcs hc (fires_bulkCommit_op hf hk)
      clear hc hf hk; exfalso; revert hpc
      cases site <;> simp only [Prologue.Site.pc] <;> decide +revert
    · rfl

end
end PTX.Kernels.Fp16Gemm8192.Proof
