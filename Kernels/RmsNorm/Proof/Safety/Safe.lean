-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.RmsNorm.Proof.NoStop
public import Kernels.RmsNorm.Proof.Arrivals
public import Lemmas.Kernel.PlainSafety
public import Lemmas.MBarrier.BarrierOrdinal
public import Kernels.RmsNorm.Proof.NoBarArrive

@[expose] public section

/-! # No consistent execution is unsafe

Without asynchronous instructions only the branches of `Unsafe` the threads' own events decide
remain (`Execution.NoTma.not_unsafe`). A thread's machine stops only at a value its next
transition rejects; every value a thread reads or receives is one it accepts (`next_ne_none`),
so no thread performs undefined behaviour (`no_ub`). Every access is allocated (`no_unalloc`),
and conflicting accesses are ordered (`conflicts_ordered`). The barriers are matched
(`no_barMismatch`) and no aligned barrier diverges or is left by an exit (`no_alignedMismatch`):
a thread's arrivals are, per row, barrier `0` twice and barrier `1` once, so lanes of a warp at
the same arrival number are at one site, and a thread exits only after the arrivals of all rows of
its CTA. -/

namespace PTX.Kernels.RmsNorm.Proof

open PTX PTX.Proof PTX.Flow CtaBarrier

noncomputable section

local notation "Prod" => [Assumptions.idealArith, Assumptions.exactApprox]

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts P L X)
include hpre hX ht

/-- The barrier sites are aligned. -/
theorem bar_aligned {g k id pc : Nat} {c : Option Nat} (he : X.IsBarrier (g, k) id c pc) :
    c = none ∧ kernel.alignedAt pc = true := by
  obtain ⟨d, -, hc, hpc, hs⟩ := bar_number hpre hX ht he
  refine ⟨hc, ?_⟩
  rcases hs with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [hpc, h1] <;> decide +kernel

theorem bars_aligned : ∀ g ev, ev ∈ X.tr g → ∀ id count, ev.kind = .bar id count →
    count = none ∧ kernel.alignedAt ev.pc = true := by
  intro g ev hm id count hk
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hm
  obtain ⟨pc, kd⟩ := ev
  simp only at hk
  subst hk
  exact bar_aligned hpre hX ht (show X.IsBarrier (g, j) id count pc from hj)

/-- **Barriers are matched.** -/
theorem no_barMismatch : ¬ BarMismatch L X := by
  rintro (⟨g, h, i, j, id, id', count, count', pc, pc', -, hb1, hb2, hn, hbad⟩ | hna)
  · obtain ⟨d1, -, rfl, rfl, hs1⟩ := bar_number hpre hX ht hb1
    obtain ⟨d2, -, rfl, rfl, hs2⟩ := bar_number hpre hX ht hb2
    rcases hs1 with ⟨h1, rfl, h1'⟩ | ⟨h1, rfl, h1'⟩ | ⟨h1, rfl, h1'⟩ <;>
      rcases hs2 with ⟨h2, rfl, h2'⟩ | ⟨h2, rfl, h2'⟩ | ⟨h2, rfl, h2'⟩ <;>
      rw [h1', h2'] at hn <;> first | omega | simp at hbad
  · exact hX.not_barArriveMismatch Fact.out hna

omit hpre ht in
/-- An event of the kernel is in no aligned class other than `barrier{.cta}`. -/
theorem member_false {c : AlignedClass} (hc : c ≠ .bar) {e : EvId} {ev : Event}
    (he : X.get e = some ev) : c.member ev = false := by
  obtain ⟨pc, k⟩ := ev
  have hk := noTma_of_consistent noTma hX _ _ _ he
  cases c
  case bar => exact absurd rfl hc
  all_goals cases k <;> simp_all [AlignedClass.member, Kind.isTma, isTcColl, isCluster,
    SetMaxNReg.isRequest, isMatrix]

/-- Lanes of a warp at the same barrier number are at the same barrier instruction. -/
theorem no_barDivergent : ¬ AlignedClass.bar.Divergent L kernel X := by
  intro hd
  obtain ⟨g, h, i, j, id, id', count, count', mode, mode', pc, pc', -, he, hf, hk, -, hne⟩ :=
    (AlignedClass.divergent_bar_iff L).mp hd
  cases mode
  case arrive => exact hX.noBarArrive Fact.out _ _ _ _ he
  cases mode'
  case arrive => exact hX.noBarArrive Fact.out _ _ _ _ hf
  obtain ⟨d1, -, -, rfl, hs1⟩ := bar_number hpre hX ht (show X.IsBarrier (g, i) id count pc from he)
  obtain ⟨d2, -, -, rfl, hs2⟩ :=
    bar_number hpre hX ht (show X.IsBarrier (h, j) id' count' pc' from hf)
  rcases hs1 with ⟨h1, -, h1'⟩ | ⟨h1, -, h1'⟩ | ⟨h1, -, h1'⟩ <;>
    rcases hs2 with ⟨h2, -, h2'⟩ | ⟨h2, -, h2'⟩ | ⟨h2, -, h2'⟩ <;>
    rw [h1', h2'] at hk <;> rw [h1, h2] at hne <;> omega

/-- No thread exits before an arrival of its CTA: a thread exits after the arrivals of all rows
of its CTA. -/
theorem no_barExited : ¬ AlignedClass.bar.Exited L kernel X := by
  intro hx
  obtain ⟨e, f, k, hc, ⟨ev, he, hev⟩, hk, hs⟩ := (AlignedClass.exited_bar_iff L).mp hx
  obtain ⟨pc, id, mode, rfl, -⟩ := Kernel.isAlignedCtaBar_iff hev
  cases mode
  case arrive => exact (hX.noBarArrive Fact.out _ _ _ _ he).elim
  obtain ⟨e1, e2⟩ := e
  obtain ⟨f1, f2⟩ := f
  obtain ⟨d1, hA1, -, -, hs1⟩ := bar_number hpre hX ht
    (show X.IsBarrier (e1, e2) id none pc from he)
  rw [Execution.countP_isAlignedCtaBar (fun ev hm =>
    bars_aligned hpre hX ht e1 ev (List.mem_of_mem_take hm))
    (fun ev hm => hX.noBarArrive_tr Fact.out e1 ev (List.mem_of_mem_take hm))] at hk
  obtain ⟨⟨pcx, hx⟩, hcnt⟩ := hs
  rw [Execution.countP_isAlignedCtaBar (bars_aligned hpre hX ht f1)
    (hX.noBarArrive_tr Fact.out f1)] at hcnt
  obtain ⟨-, dx, hAx⟩ := event_facts hpre hX ht hx (by intro _ _ h; cases h)
  have hxs := exit_site hAx.event
  have hnx := countP_isBar hpre hX ht hAx
  have hmono : ((X.tr f1).take f2).countP Execution.isBar ≤ (X.tr f1).countP Execution.isBar :=
    (List.take_sublist _ _).countP_le
  have hex := hAx.inv.exit hxs
  have hr1 := hA1.inv.row (by
    rcases hs1 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h, Site.inRow])
  have hcta : e1 / 256 = f1 / 256 := by
    have := hc.2.2
    rw [hpre.hyp.block] at this
    exact this
  simp only [D.bc0, D.bc1, hxs, row] at hnx hr1
  have hlt : d1.i < dx.i := by omega
  have : 3 * d1.i + 3 ≤ 3 * dx.i := by omega
  simp only at hk hcnt
  rcases hs1 with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> omega

/-- **No aligned instruction diverges or is left by an exit.** -/
theorem no_alignedMismatch : ¬ AlignedMismatch L kernel X := by
  rintro ⟨c, hd | hx⟩
  · by_cases hc : c = .bar
    · subst hc
      exact no_barDivergent hpre hX ht hd
    · obtain ⟨e, f, pe, pf, ke, kf, -, he, -, hm, -⟩ := hd
      rw [member_false hX hc he] at hm
      cases hm
  · by_cases hc : c = .bar
    · subst hc
      exact no_barExited hpre hX ht hx
    · obtain ⟨e, f, ev, -, he, hm, -⟩ := hx
      have hex : c.exitMember kernel ev = c.member ev := by
        cases c <;> first | exact absurd rfl hc | rfl
      rw [hex, member_false hX hc he] at hm
      cases hm

/-- **No undefined behaviour.** -/
theorem no_ub : ¬ HasUb X := by
  rintro ⟨⟨g, k⟩, pc, f, he⟩
  have hg := Frame.lt_of_get hX he
  have hk := len_of_get he
  simp only at hk
  obtain ⟨j, d, e, hj, hσj, hej, hnext⟩ := ht.dead hg hk.le (ht.ub hg he)
  obtain ⟨h0, h1, h2⟩ := ht.counts hg hσj
  have hA : At P L X g j d e := ⟨hσj, ht.event hg hej hσj,
    ht.index hg (len_of_get hej).le hσj, ht.inv hg hσj, ht.data hg hσj, h0, h1, h2⟩
  by_cases hx : d.site = .exit
  · obtain ⟨pcx, rfl⟩ := exit_site_of hA.event hx
    have := Execution.exit_last hX hg hej
    omega
  · exact next_ne_none hpre hX ht hej hA hx hnext

/-- No thread performs a non-coherent read. -/
theorem no_nc {i : EvId} {a : Acc} {bs : List (Option Byte)} (h : X.NcReads i a bs) : False := by
  obtain ⟨pc, he⟩ := h
  obtain ⟨-, d, hA⟩ := event_facts hpre hX ht he (by intro _ _ h; cases h)
  obtain ⟨t, o, hf⟩ := hA.event
  rcases hs : d.site <;> simp only [siteTmpl, hs, Fires] at hf <;> ev_close hf

omit hpre hX ht in
/-- The site of an access is in a row. -/
theorem access_row {g : Nat} {d : D} {pc : Nat} {k : Kind} (h : SiteEvent P g d ⟨pc, k⟩)
    (hk : (∃ a bs, k = .rd a bs) ∨ ∃ a bs, k = .wr a bs) : d.site.inRow = true := by
  rcases hk with ⟨a, bs, rfl⟩ | ⟨a, bs, rfl⟩
  · rcases rd_site h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ |
      ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h1, Site.inRow]
  · rcases wr_site h with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ |
      ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h1, Site.inRow]

/-- **Every access is allocated.** -/
theorem no_unalloc : ¬ Unalloc mem0 X := by
  rintro (⟨e, a, l, htouch, hc, hn⟩ | ⟨e, m, l, hu, -, -⟩)
  swap
  · exact (noTma_of_consistent noTma hX).not_usesMbar hu
  obtain ⟨⟨g, k⟩, rfl, hacc⟩ :=
    Execution.NoTma.memTouches_thread (noTma_of_consistent noTma hX) htouch
  have hacc' : ∃ w, X.Access (g, k) a w := by
    rcases hacc with ⟨bs, hr⟩ | ⟨bs, hnc⟩ | ⟨bs, hw⟩ | ⟨o, n, pc, hm⟩
    · exact ⟨false, .inl ⟨bs, hr, rfl⟩⟩
    · exact (no_nc hpre hX ht hnc).elim
    · exact ⟨true, .inr (.inl ⟨bs, hw, rfl⟩)⟩
    · exact (no_rmw hpre hX ht hm).elim
  obtain ⟨w, hacc⟩ := hacc'
  obtain ⟨hg, d, ev, hev, hA, hsh, -⟩ := access_facts hpre hX ht hacc
  have hr : d.site.inRow = true := by
    rcases hacc with ⟨bs, ⟨pc, hr⟩, -⟩ | ⟨bs, ⟨pc, hw⟩, -⟩ | ⟨o, n, pc, hm⟩
    · rw [hr] at hev; cases Option.some.inj hev
      exact access_row hA.event (.inl ⟨_, _, rfl⟩)
    · rw [hw] at hev; cases Option.some.inj hev
      exact access_row hA.event (.inr ⟨_, _, rfl⟩)
    · exact (no_rmw hpre hX ht hm).elim
  have hrow := hA.inv.row hr
  simp only [row] at hrow
  have hc152 := cta_of_lt hpre hg
  obtain ⟨sp, c, addr⟩ := l
  obtain ⟨h1, h2, h3, h4⟩ := hc
  rw [hsh.size] at h4
  have h4' := hsh.align
  have hI := hpre.hyp.inAlign
  have hW := hpre.hyp.wAlign
  have hO := hpre.hyp.outAlign
  have hS := hpre.hyp.sharedAlign
  simp only at h1 h2 h3 h4
  rcases hsh.space with hgl | hsp
  · obtain ⟨hc0, hwr, hrd⟩ := hsh.global hgl
    rw [hgl] at h1
    rw [hc0] at h2
    subst h1 h2
    cases w
    · rcases hrd rfl with ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩
      · have := hpre.input (addr - P.I) (by omega)
        rw [show P.I + (addr - P.I) = addr by omega] at this
        rw [show (⟨.global, 0, addr⟩ : Loc) = gl addr from rfl, this] at hn
        cases hn
      · have := hpre.weight (addr - P.W) (by omega)
        rw [show P.W + (addr - P.W) = addr by omega] at this
        rw [show (⟨.global, 0, addr⟩ : Loc) = gl addr from rfl, this] at hn
        cases hn
    · obtain ⟨hlo, hhi, -⟩ := hwr rfl
      have := hpre.output (addr - P.O) (by omega)
      rw [show P.O + (addr - P.O) = addr by omega] at this
      exact this hn
  · obtain ⟨hc', hlo, hhi, -, -⟩ := hsh.shared hsp
    rw [hsp] at h1
    rw [hc'] at h2
    subst h1 h2
    have := hpre.shared (g / 256) hc152 (by omega) (addr - P.S) (by omega)
    rw [show P.S + (addr - P.S) = addr by omega] at this
    exact this hn

/-- The barriers of a CTA count their threads alike. -/
theorem no_ctaBarFault : ¬ CtaBarFault L X :=
  not_ctaBarFault hX fun ⟨_, _⟩ ⟨_, _⟩ _ _ _ _ _ _ h1 h2 =>
    (bar_aligned hpre hX ht h1).1.trans (bar_aligned hpre hX ht h2).1.symm

omit hpre hX ht in
theorem tcGroupUniform : kernel.TcGroupUniform := by
  unfold Kernel.TcGroupUniform; decide +kernel

/-- **No consistent execution is unsafe.** -/
theorem safe : ¬ Unsafe L kernel Prod mem0 X := by
  refine (noTma_of_consistent noTma hX).not_unsafe hX (no_ub hpre hX ht) (no_unalloc hpre hX ht)
    (conflicts_ordered hpre hX ht) (no_barMismatch hpre hX ht) (no_ctaBarFault hpre hX ht) ?_
    (no_alignedMismatch hpre hX ht) (not_warpDivergent (by decide +kernel)) ?_
  · rintro ⟨a, ha, hu⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> exact hu
  · intro e a w ha hs
    obtain ⟨-, d, ev, -, -, hsh, -⟩ := access_facts hpre hX ht ha
    rw [(hsh.shared hs).1, hpre.hyp.block]

end
end PTX.Kernels.RmsNorm.Proof
