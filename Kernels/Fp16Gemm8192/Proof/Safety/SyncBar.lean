-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.Fp16Gemm8192.Proof.Safety.SyncCluster
public import Lemmas.CtaBarrier.CtaBarrierIdentity
public import Kernels.Fp16Gemm8192.Proof.NoBarArrive
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
public import Lemmas.Protocol.NamedBarSources

@[expose] public section

/-! # `BarMismatch` and the barrier clauses of `AlignedMismatch`, from the thread facts

Only consumers arrive on named barriers, at three kinds of site: the group's CLC barrier
(`clcBar`) and the group's output barrier before and after a slice's stores (`barA`, `barB`).
Along a consumer's run its arrivals on the CLC barrier and on the output barrier count its tiles
(`ThreadFacts.cons_bar_phase`), so the ordinal of an arrival among all of a thread's barrier
arrivals, modulo seventeen, tells the site (`ordinal_of_site`). Two lanes of a warp at the same
ordinal are at the same site, hence at the same source line, barrier and count
(`warp_agrees`). Arrivals of different warps are not compared by site (EXT-BAR-PARTICIPANTS). -/

namespace PTX.Kernels.Fp16Gemm8192.Proof.Safety

open PTX

variable {L : Launch} {mem0 : Mem0} {X : Execution}

/-- A named barrier arrival is a consumer's, at one of its barrier sites. -/
theorem bar_info (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {g i pc id : Nat}
    {cnt : Option Nat} (he : X.IsBarrier (g, i) id cnt pc) :
    g < L.threads ∧ ∃ c : Consumer.D, Frame.stateAt (code L) X g i = some (some (.inr (.cons c))) ∧
      pc = c.site.pc ∧ cnt = some 128 ∧ Consumer.tidOf L g / 32 < 8 ∧
      ((c.site = .clcBar ∧ id = Consumer.tidOf L g / 32 / 4 + 1) ∨
        (∃ s, (c.site = .barA s ∨ c.site = .barB s) ∧ id = Consumer.outId L g)) := by
  have he' : X.get (g, i) = some ⟨pc, .bar id cnt⟩ := he
  have hg := Frame.lt_of_get hX he'
  obtain ⟨d, hσ⟩ := Frame.event_state ht.sound hX ht.tracked he' nofun
  obtain ⟨c, rfl⟩ := ht.bar_role hg he' hσ rfl
  have hrw := ht.role_warp hg (len_of_get he').le hσ
  simp only [roleWarp] at hrw
  have hpc : pc = c.site.pc := Frame.event_pc ht.sound hX he' hσ
  refine ⟨hg, c, hσ, hpc, ?_, by simp only [Consumer.tidOf]; omega, ?_⟩
  · rcases (ht.cons_out hg he' hσ).2.2.2.2.1 id cnt rfl with ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> exact h
  · rcases (ht.cons_out hg he' hσ).2.2.2.2.1 id cnt rfl with ⟨hs, hid, -⟩ | ⟨hs, hid, -⟩
    · exact .inl ⟨hs, hid⟩
    · exact .inr ⟨hs.choose, hs.choose_spec, hid⟩


/-- The barrier arrivals of a thread before its `i`-th event are those on its group's CLC barrier
and on its output barrier. -/
theorem bar_ordinal (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) {g i : Nat}
    (hi : i ≤ (X.tr g).length) :
    ((X.tr g).take i).countP Execution.isBar =
      ((X.tr g).take i).countP (Execution.isBarId (Consumer.tidOf L g / 32 / 4 + 1)) +
        Consumer.outBars L g ((X.tr g).take i) := by
  rw [Consumer.outBars_eq]
  apply NamedBar.countP_bar_split (by simp only [Consumer.outId]; omega)
  intro e he hbar
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp he
  have hjk : j < i := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    simp only [List.length_take] at this
    omega
  have hget : X.get (g, j) = some e := by
    rw [List.getElem?_take_of_lt hjk] at hj
    exact hj
  obtain ⟨pc, kind⟩ := e
  cases kind <;> simp only [Execution.isBar, Bool.false_eq_true] at hbar
  case bar id cnt mode =>
    cases mode
    case arrive => exact (hX.noBarArrive Fact.out _ _ _ _ hget).elim
    obtain ⟨-, c, -, -, -, -, hs⟩ := bar_info hX ht (show X.IsBarrier (g, j) id cnt pc from hget)
    rcases hs with ⟨-, hid⟩ | ⟨s, -, hid⟩
    · exact .inl (by simp [Execution.isBarId, hid])
    · exact .inr (by simp [Execution.isBarId, hid])


/-- **The site of a barrier arrival from its ordinal.** With `q` the thread's tiles, the arrival is
at the CLC barrier site when `17 q` barrier arrivals precede it, and at a slice's first or second
output barrier site when `17 q + 2 k - 16` or `17 q + 2 k - 15` do. -/
theorem ordinal_of_site (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    {g i pc id : Nat}
    {cnt : Option Nat} (he : X.IsBarrier (g, i) id cnt pc) :
    ∃ (q : Nat) (c : Consumer.D), Frame.stateAt (code L) X g i = some (some (.inr (.cons c))) ∧
      pc = c.site.pc ∧ cnt = some 128 ∧ Consumer.tidOf L g / 32 < 8 ∧
      ((c.site = .clcBar ∧ id = Consumer.tidOf L g / 32 / 4 + 1 ∧
          ((X.tr g).take i).countP Execution.isBar = 17 * q) ∨
        (∃ s : Fin 8, c.site = .barA s ∧ id = Consumer.outId L g ∧
          ((X.tr g).take i).countP Execution.isBar + 16 = 17 * q + 2 * s.val) ∨
        (∃ s : Fin 8, c.site = .barB s ∧ id = Consumer.outId L g ∧
          ((X.tr g).take i).countP Execution.isBar + 16 = 17 * q + 2 * s.val + 1)) := by
  obtain ⟨hg, c, hσ, hpc, hcnt, hw8, hs⟩ := bar_info hX ht he
  obtain ⟨q, h1, h2⟩ := ht.cons_bar_phase hg hσ
  have hn := bar_ordinal hX ht (g := g) (i := i) (len_of_get (show X.get (g, i) = _ from he)).le
  refine ⟨q, c, hσ, hpc, hcnt, hw8, ?_⟩
  rcases hs with ⟨hs, hid⟩ | ⟨s, hs | hs, hid⟩
  · simp only [Consumer.D.clcHold, Consumer.tileOpen, Consumer.D.inEpi, Consumer.D.outPhase,
      hs] at h1 h2
    exact .inl ⟨hs, hid, by omega⟩
  · simp only [Consumer.D.clcHold, Consumer.tileOpen, Consumer.D.inEpi, Consumer.D.outPhase,
      hs] at h1 h2
    exact .inr (.inl ⟨s, hs, hid, by omega⟩)
  · simp only [Consumer.D.clcHold, Consumer.tileOpen, Consumer.D.inEpi, Consumer.D.outPhase,
      hs] at h1 h2
    exact .inr (.inr ⟨s, hs, hid, by omega⟩)


/-- **Two lanes of a warp at equal barrier ordinals agree** on the barrier, the count and the source
line. -/
theorem warp_agrees (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X)
    {g h i j id id' pc pc' : Nat} {cnt cnt' : Option Nat} (hw : SameWarp L g h)
    (he : X.IsBarrier (g, i) id cnt pc) (hf : X.IsBarrier (h, j) id' cnt' pc')
    (hn : ((X.tr g).take i).countP Execution.isBar = ((X.tr h).take j).countP Execution.isBar) :
    id = id' ∧ cnt = cnt' ∧ pc = pc' := by
  obtain ⟨q, c, hσ, hpc, hcnt, hw8, hord⟩ := ordinal_of_site hX ht he
  obtain ⟨q', c', hσ', hpc', hcnt', hw8', hord'⟩ := ordinal_of_site hX ht hf
  have hwarp : g % L.block / 32 = h % L.block / 32 := hw.2
  refine ⟨?_, hcnt.trans hcnt'.symm, ?_⟩ <;>
  simp only [Consumer.tidOf, Consumer.outId] at hord hord' hw8 hw8' ⊢ <;>
  rcases hord with ⟨hs, hid, h1⟩ | ⟨s, hs, hid, h1⟩ | ⟨s, hs, hid, h1⟩ <;>
  rcases hord' with ⟨hs', hid', h1'⟩ | ⟨s', hs', hid', h1'⟩ | ⟨s', hs', hid', h1'⟩ <;>
  first
  | (exfalso; have := s.isLt; have := s'.isLt; omega)
  | (exfalso; have := s'.isLt; omega)
  | (exfalso; have := s.isLt; omega)
  | omega
  | (obtain rfl : s = s' := Fin.ext (by have := s.isLt; have := s'.isLt; omega)
     rw [hpc, hpc', hs, hs'])
  | (rw [hpc, hpc', hs, hs'])

/-- **No named barrier mismatch.** -/
theorem no_barMismatch (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts L X) : ¬ BarMismatch L X := by
  rintro (⟨g, h, i, j, id, id', count, count', pc, pc', hw, he, hf, hn, hbad⟩ | h)
  · obtain ⟨hid, hcount, -⟩ := warp_agrees hX ht hw he hf hn
    exact hbad.elim (fun h => h hid) (fun h => h hcount)
  · exact hX.not_barArriveMismatch Fact.out h

/-- **Two lanes of a warp at one barrier ordinal are at one source instruction.** -/
theorem no_barDivergent (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) :
    ¬ AlignedClass.bar.Divergent L kernel X := by
  rw [AlignedClass.divergent_bar_iff]
  rintro ⟨g, h, i, j, id, id', count, count', mode, mode', pc, pc', hw, he, hf, hn, -, hne⟩
  cases mode
  case arrive => exact hX.noBarArrive Fact.out _ _ _ _ he
  cases mode'
  case arrive => exact hX.noBarArrive Fact.out _ _ _ _ hf
  exact hne (warp_agrees hX ht hw (show X.IsBarrier (g, i) id count pc from he)
    (show X.IsBarrier (h, j) id' count' pc' from hf) hn).2.2

/-- **No thread exits before an aligned barrier of its CTA**: the kernel's barriers name a thread
count, so none is an aligned CTA-wide barrier. -/
theorem no_barExited (hX : Consistent L kernel Prod mem0 X) (ht : ThreadFacts L X) :
    ¬ AlignedClass.bar.Exited L kernel X := by
  rw [AlignedClass.exited_bar_iff]
  rintro ⟨e, f, k, -, ⟨ev, he, hev⟩, -, -⟩
  obtain ⟨pc, id, mode, rfl, -⟩ := Kernel.isAlignedCtaBar_iff hev
  cases mode
  case arrive => exact (hX.noBarArrive Fact.out _ _ _ _ he).elim
  obtain ⟨-, c, -, -, h, -⟩ := bar_info hX ht (show X.IsBarrier e id none pc from he)
  cases h

end PTX.Kernels.Fp16Gemm8192.Proof.Safety
