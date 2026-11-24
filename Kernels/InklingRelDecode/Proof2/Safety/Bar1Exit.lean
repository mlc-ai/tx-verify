-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Safety.Bar0
public import Kernels.InklingRelDecode.Proof2.Lib.BarExitRes
public import Lemmas.Protocol.NamedBarExitCycle
public import Lemmas.Step.ExitLast
public import Lemmas.Order.WaitOrderEnables
public import Kernels.InklingRelDecode.Proof2.Lib.BarHandoff

@[expose] public section

/-! # An exiting thread made every barrier-1 arrival its CTA passed

`bar1Exits`: let `f` be a passed `barrier.sync 1` of a thread `h` and `g` a thread of the same CTA
that exits. Then `g` has the barrier-1 arrival of `f`'s ordinal. This is what lets the hand-offs
of barrier 1 be used at every instance without knowing first which role each worker runs (the
`hexit` premise of `Handoff.of_bar_upTo` asks it of every exiting thread). The argument is the
first tree's `Interface/Bar1Exit.lean` on the role table's states:

1. if `g` has no arrival of that ordinal, its exit `E` is a witness of `f`'s return
   (`NamedBar.Sources.arrival_or_exit`);
2. `E` follows `g`'s last `bar.sync 0` `W` (`exit_final_bar`, from `post_inv`);
3. the generation of `W` counts every lane of the CTA, so `h` has a witness `Z` of `W`'s return:
   its exit or its own last `bar.sync 0` (`final_witness`, with barrier 0's phased sources
   `bar0_phSources`); `Z` is after `f` in `h`'s trace (`final_after_b1`, from `post_after`);
4. `E → f → Z → W → E` is a cycle of the dependency order (`Consistent.no_exit_cycle`). -/

namespace PTX.Kernels.InklingRelDecode.Proof2
open PTX PTX.Proof PTX.Flow PTX.Frame

noncomputable section
set_option maxRecDepth 100000

variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **An exit follows the thread's last `bar.sync 0`.** -/
theorem exit_final_bar (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {g j pc : Nat} (hE : X.get (g, j) = some ⟨pc, .exit⟩) :
    ∃ jW pcW, jW < j ∧ X.get (g, jW) = some ⟨pcW, .bar 0 none .sync⟩ ∧
      2 ≤ ((X.tr g).take jW).countP (Execution.isBarId 0) := by
  have hg := Frame.lt_of_get hX hE
  obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ := ev_state hp hX hE (fun f h => by cases h)
  have hlen : j < (X.tr g).length := (List.getElem?_eq_some_iff.mp hE).1
  have hpc := ret_pc' hc hf rfl
  have hpost : IsPost Q L g σ := by
    obtain ⟨x, n⟩ := σ
    rcases x with st | ⟨_ | r, d⟩
    · have hm := startup_special st.site (List.mem_append_right _ hpc)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h <;>
        rw [show (thread Q L g).pc _ = st.site.pc from rfl, h] at hpc <;>
        simp [retPcs, Startup.Site.pc] at hpc
    · rename_i i
      cases i with
      | dp tm bw =>
        rcases d with d | ⟨_ | _, τ⟩
        · exact absurd (List.mem_append_right _ hpc) (proA_special d.site)
        · cases τ with
          | sm d => simpa using sm_special d.site (List.mem_append_right _ hpc)
          | epi d =>
            have hm := epi_special d.site (List.mem_append_right _ hpc)
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
            exact .inr (hm.resolve_left (fun h => by
              rw [show (thread Q L g).pc _ = d.site.pc from rfl, h] at hpc
              simp [retPcs, Proof.Epi.Site.pc] at hpc))
        · exact hJ.elim
      | worker w =>
        obtain ⟨P, hP⟩ := worker_state_special d (List.mem_append_right _ hpc)
        subst hP
        rfl
    · exact hJ.elim
  obtain ⟨jW, hjW, pcW, hW, h2⟩ := post_inv hp hX hg j hlen σ hσ hpost
  exact ⟨jW, pcW, hjW, hW, h2⟩

/-- **Every barrier-1 event of a thread is before its last `bar.sync 0`.** -/
theorem final_after_b1 (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {h jZ jf pcZ pcf : Nat} {md mf : BarMode} {cnt : Option Nat}
    (hZ : X.get (h, jZ) = some ⟨pcZ, .bar 0 none md⟩)
    (h2 : 2 ≤ ((X.tr h).take jZ).countP (Execution.isBarId 0))
    (hf : X.get (h, jf) = some ⟨pcf, .bar 1 cnt mf⟩) : jf < jZ := by
  have hb : L.block = 256 := hp.block
  by_contra hle
  have hne : jf ≠ jZ := by
    rintro rfl
    rw [hZ] at hf
    simp at hf
  have hlen : jf < (X.tr h).length := (List.getElem?_eq_some_iff.mp hf).1
  obtain ⟨σ, t, ins, o, hσ, hJ, hat, hi, hc, hfi⟩ := ev_state hp hX hf (fun f h => by cases h)
  obtain ⟨d, rfl⟩ : ∃ d, jf = jZ + 1 + d := ⟨jf - (jZ + 1), by omega⟩
  have hpost := post_after hp hX hZ h2 d hlen σ hσ
  have hpc := bar1_pc hc hfi rfl (by omega)
  rcases post_pc hpost with h' | h' <;> rw [h'] at hpc <;> simp [bar1Pcs] at hpc

/-- **The generation of a passed last `bar.sync 0` counts every thread of the CTA.** -/
theorem final_witness (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {g jW pcW : Nat} (hW : X.get (g, jW) = some ⟨pcW, .bar 0 none .sync⟩)
    (hpass : jW + 1 < (X.tr g).length)
    (h2 : 2 ≤ ((X.tr g).take jW).countP (Execution.isBarId 0))
    {h : Nat} (hcta : h / L.block = g / L.block) :
    ∃ Z : EvId, Z.1 = h ∧ Witness L X (.thread Z) (g, jW) ∧
      ((∃ pcx, X.get Z = some ⟨pcx, .exit⟩) ∨
        ∃ pcZ m', X.get Z = some ⟨pcZ, .bar 0 none m'⟩ ∧
          2 ≤ ((X.tr Z.1).take Z.2).countP (Execution.isBarId 0)) := by
  have hb : L.block = 256 := hp.block
  have hWbar : X.IsBarrier (g, jW) 0 none pcW := hW
  obtain ⟨key, hk, hdone⟩ := ctaBarDone_of_returned hX hWbar hpass
  have hgth : g < L.threads := hk.1
  have hc : g / L.block < L.grid := NamedBar.cta_lt hgth
  have hkid : key % 16 = 0 := by
    obtain ⟨count', pc', he'⟩ := hk.2.1
    exact (Kind.bar.inj (Event.mk.inj (Option.some.inj (he'.symm.trans hW))).2).1
  have hgen : CtaBarrier.GenerationOf L.block (X.barriers (g / L.block)) (g, jW) 0 (key / 16) := by
    have := hk.2.2
    rwa [hkid] at this
  have hG2 : 2 ≤ key / 16 := le_trans h2 (NamedBar.ordinal_le_generation hX hc hgen)
  obtain ⟨ic, hic⟩ := hdone
  have hic0 : CtaBarrier.CompletesAt L.block (X.barriers (g / L.block)) ic 0 (key / 16) := by
    have := hic
    rwa [hkid] at this
  obtain ⟨-, -, last, hlast⟩ := hX.ctaBar.2 _ hc
  obtain ⟨jr, sW, warpW, cntW, lanesW, lW, hjr, hatW, hmW, hgW, tW, hpW⟩ := hgen
  have hcntW : cntW = none := by
    obtain ⟨-, -, pc'', mode, hbar''⟩ :=
      ((hX.ctaBar.2 _ hc).2.1 _ (List.mem_of_getElem? hjr)) (lW, (g, jW)) hmW
    have := hbar''.symm.trans hW
    simp only [Option.some.injEq, Event.mk.injEq, Kind.bar.injEq] at this
    exact this.2.2.1
  subst hcntW
  have hjric : jr ≤ ic := by
    by_contra hlt
    obtain ⟨r, s, t, hr, hs, htt, hg0, hg1⟩ := hic0
    have hat := NamedBar.at_succ hr hs htt
    have := NamedBar.at_gen_mono (id := 0) (show ic + 1 ≤ jr by omega) hat hatW
    omega
  have hl : h % L.block < L.block := Nat.mod_lt _ (by omega)
  have hthr : g / L.block * L.block + h % L.block = h := by
    rw [← hcta, Nat.mul_comm]
    exact Nat.div_add_mod h L.block
  rcases NamedBar.completes_counts hic0 hjr hatW hpW hgW (by simp [CtaBarrier.target]) hjric hl
    with ⟨i, y, hi, hy⟩ | ⟨i, cnt', lanes', Z, si, ti, hi, hri, hZm, hsi, hti, hgi, htg⟩
  · obtain ⟨-, hy1, pcx, hget⟩ := (hX.ctaBar.2 _ hc).2.1 _ (List.mem_of_getElem? hy)
    have hcnt : CtaBarCounted L X (g, jW) y :=
      ⟨key, ic, hk, hic, i, .exit (h % L.block) y, hy, by simp [CtaBarrier.Record.refs], hi,
        .inr ⟨h % L.block, rfl⟩⟩
    have hy' : y ∈ (X.barriers (g / L.block)).flatMap CtaBarrier.Record.refs :=
      List.mem_flatMap.mpr ⟨_, List.mem_of_getElem? hy, by simp [CtaBarrier.Record.refs]⟩
    exact ⟨y, hy1.trans hthr, Witness.of_need L (ctaBarCounted_witnessed L X (g, jW) y hW hy' hcnt)
      ⟨_, hget⟩ rfl, .inl ⟨pcx, hget⟩⟩
  · obtain ⟨-, hZ1, pcZ, mZ, hZbar⟩ :=
      ((hX.ctaBar.2 _ hc).2.1 _ (List.mem_of_getElem? hri)) (h % L.block, Z) hZm
    have hZh : Z.1 = h := hZ1.trans hthr
    have hcnt' : cnt' = none := by
      rcases (bar_event_static hX (by omega) hZbar).2 with ⟨h1, -⟩ | ⟨-, h1⟩
      · exact h1
      · subst h1
        simp [CtaBarrier.target, CtaBarrier.warps, hb] at htg
    subst hcnt'
    have hstart := NamedBar.start_le_ordinal (loopGroup_sub hp) loopGroup_card
      (loopGroup_ne hp) loopGroup_target ((bar0_phSources hp hX).protocol hX hc) hsi hti
      (by omega)
    obtain ⟨-, -, -, -, hord, -⟩ := NamedBar.record_ordinal hX hc hlast hri hsi hZm
    have hcnt : CtaBarCounted L X (g, jW) Z :=
      ⟨key, ic, hk, hic, i, .arrival 0 (h % L.block / 32) none lanes', hri,
        List.mem_map.mpr ⟨(h % L.block, Z), hZm, rfl⟩, hi,
        .inl ⟨h % L.block / 32, none, lanes', si, by rw [hkid], hsi, by rw [hkid]; exact hgi⟩⟩
    have hy' : Z ∈ (X.barriers (g / L.block)).flatMap CtaBarrier.Record.refs :=
      List.mem_flatMap.mpr ⟨_, List.mem_of_getElem? hri,
        List.mem_map.mpr ⟨(h % L.block, Z), hZm, rfl⟩⟩
    refine ⟨Z, hZh, Witness.of_need L (ctaBarCounted_witnessed L X (g, jW) Z hW hy' hcnt)
      ⟨_, hZbar⟩ rfl, .inr ⟨pcZ, mZ, hZbar, ?_⟩⟩
    simp only at hord
    omega

/-- **An exiting thread made every barrier-1 arrival its CTA passed.** -/
theorem bar1Exits (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X)
    {f : EvId} {pc g : Nat} (hf : X.IsBarrier f 1 none pc) (hpass : f.2 + 1 < (X.tr f.1).length)
    (hcta : g / L.block = f.1 / L.block) (_hex : ∃ j pcx, X.get (g, j) = some ⟨pcx, .exit⟩) :
    ∃ i pc', X.IsBarrier (g, i) 1 none pc' ∧
      ((X.tr g).take i).countP (Execution.isBarId 1) =
        ((X.tr f.1).take f.2).countP (Execution.isBarId 1) := by
  have hb : L.block = 256 := hp.block
  have hw1 : (g % L.block) / 32 ∈ Finset.range (CtaBarrier.warps L.block) := by
    have := Nat.mod_lt g (show L.block > 0 by omega)
    simp only [Finset.mem_range, CtaBarrier.warps, hb] at this ⊢
    omega
  rcases (bar1_sources hp hX).arrival_or_exit hX (bar1_shape hp) hf hpass hcta hw1 with
    ⟨i, pc', m', hgi, hord⟩ | ⟨E, pcx, hEg, hE, hEf⟩
  · obtain ⟨hm, -⟩ := bar_event_static hX (by omega) hgi
    subst hm
    exact ⟨i, pc', hgi, hord⟩
  exfalso
  obtain ⟨E1, E2⟩ := E
  simp only at hEg
  subst hEg
  obtain ⟨jW, pcW, hjW, hW, h2⟩ := exit_final_bar hp hX hE
  have hElen := len_of_get hE
  obtain ⟨Z, hZh, hZW, hZ⟩ := final_witness hp hX hW (by simp only at hElen; omega) h2
    (h := f.1) hcta.symm
  have hfZ : TraceBefore X f Z := by
    refine ⟨hZh.symm, ?_, ?_⟩
    · rcases hZ with ⟨pcx', hZx⟩ | ⟨pcZ, mZ, hZb, hZ2⟩
      · have hft : f.1 < L.threads := Frame.lt_of_get hX hf
        have hlast := Execution.exit_last hX (hZh ▸ hft)
          (show X.get (Z.1, Z.2) = some ⟨pcx', .exit⟩ from hZx)
        rw [hZh] at hlast
        have := len_of_get hf
        omega
      · obtain ⟨Z1, Z2⟩ := Z
        simp only at hZh hZ2
        subst hZh
        exact final_after_b1 hp hX hZb hZ2 hf
    · rcases hZ with ⟨pcx', hZx⟩ | ⟨pcZ, mZ, hZb, -⟩
      · exact len_of_get hZx
      · exact len_of_get hZb
  exact hX.no_exit_cycle hEf ⟨_, false, hf, rfl⟩ hfZ hZW ⟨_, false, hW, rfl⟩
    ⟨rfl, hjW, hElen⟩

/-- **Barrier 1 is a hand-off at every instance** among the threads of a CTA: an event of `g`
whose barrier-1 events up to it are fewer than those before an event of `h` happens before it. -/
theorem bar1_handoff (hp : Pre Q L m) (hX : Consistent L kernel Assumptions.all m X) :
    Handoff L X (fun g h => SameCta L g h ∧ (g % L.block) / 32 ∈
        Finset.range (CtaBarrier.warps L.block) ∧ True)
      (fun i => ((X.tr i.1).take (i.2 + 1)).countP (Execution.isBarId 1))
      (fun i => ((X.tr i.1).take i.2).countP (Execution.isBarId 1)) := by
  have hb : L.block = 256 := hp.block
  refine Handoff.of_bar_exits hX (bar1_sources hp hX) (bar1_shape hp)
    (fun h j pc cnt mode _ he => (bar_event_static hX (by omega) he).1)
    (fun f pc cnt g hf hpass hcta _ hex => ?_)
  have hf' : X.get f = some ⟨pc, .bar 1 cnt .sync⟩ := hf
  have hcn : cnt = none := by
    rcases (bar_event_static hX (by omega) hf').2 with ⟨h, -⟩ | ⟨h, -⟩
    · exact h
    · cases h
  subst hcn
  obtain ⟨i, pc', hi, hord⟩ := bar1Exits hp hX hf hpass hcta hex
  exact ⟨i, pc', .sync, hi, hord⟩

end
end PTX.Kernels.InklingRelDecode.Proof2
