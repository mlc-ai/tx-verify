-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Common.Export.BarZero
public import Lemmas.Protocol.NamedBarExitCycle
import Kernels.InklingRelDecode.Proof.Lib.BarOne
import Lemmas.Protocol.NamedBarGenExit
import Lemmas.Protocol.NamedBarEarly

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
open PTX
variable {Q : Params} {L : Launch} {m : Mem0} {X : Execution}

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
  have group : Finset.range 4 ⊆ Finset.range (CtaBarrier.warps L.block) := by
    intro w mem
    simp only [Finset.mem_range,CtaBarrier.warps,hb] at mem ⊢
    omega
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
    have hat := NamedBar.GenLedger.at_succ hr hs htt
    have := NamedBar.GenLedger.at_gen_mono (id := 0) (show ic + 1 ≤ jr by omega) hat hatW
    omega
  have hl : h % L.block < L.block := Nat.mod_lt _ (by omega)
  have hthr : g / L.block * L.block + h % L.block = h := by
    rw [← hcta, Nat.mul_comm]
    exact Nat.div_add_mod h L.block
  rcases NamedBar.GenLedger.completes_counts hic0 hjr hatW hpW hgW
      (by simp [CtaBarrier.target]) hjric hl
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
      obtain ⟨_,one|full|half⟩ := Lib.recorded_bar hX hb hZbar
      · cases one.1
      · exact full.2.1
      · rw [half.2.1] at htg
        simp [BarRow.recCnt,CtaBarrier.target,CtaBarrier.warps,hb] at htg
    subst hcnt'
    have hstart := NamedBar.GenLedger.start_le_ordinal group (Finset.card_range 4)
      (by simp [CtaBarrier.warps,hb]) (by simp [CtaBarrier.target])
      ((Export.barZeroSources hp hX).protocol hX hc) hsi hti
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

end PTX.Kernels.InklingRelDecode.Proof.Protocol.Shared
