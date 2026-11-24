-- SPDX-License-Identifier: Apache-2.0
module

import Lemmas.Kernel.FrameU

public import Kernels.TmlFa4Fwd.Proof.Correction.Export.Count
public import Kernels.TmlFa4Fwd.Proof.Correction.Export.MemRead
public import Kernels.TmlFa4Fwd.Proof.Lib.TmemRegion
import Kernels.TmlFa4Fwd.Proof.Correction.Export.TmemRoute
import Kernels.TmlFa4Fwd.Proof.Correction.Export.TmemSite
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Counts
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Pos
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.ReadAddr
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Open
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Correction.Export.MbarSite
import Kernels.TmlFa4Fwd.Proof.Startup.Export.Mem
import Kernels.TmlFa4Fwd.Proof.Correction.Export.Mem

@[expose] public section

/-! # The named-barrier ordinal of a statistics read

A statistics read of a correction lane, at the site its program counter names, loads its stage's
word after `A + 1 ≥ 2` events on its stage's named barrier (`corr_stat_site`); at the reads of the
final stage's maximum `A` is one more than the rescale rounds. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Correction (ptsOf passed before inRound tailR arrivePts)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {h k : Nat}

private theorem site_tab : ∀ s ∈ Correction.allSites, ∀ s' ∈ Correction.allSites,
    s.statRd.isSome = true → s'.pc = s.pc → s' = s := by decide +kernel

private theorem nb_tab : ∀ q : Fin 2,
    (∀ s ∈ Correction.allSites, ∀ n, s.statRd = some (n, q) →
      (ptsOf (.nb q)).countP (before s) = 2) ∧ (ptsOf (.nb q)).countP inRound = 1 := by
  decide +kernel

private theorem tail_tab : ∀ s ∈ Correction.allSites, ∀ q,
    s.statRd = some ((1 : Fin 2), q) → tailR s = true := by decide +kernel

private theorem ne_tab : ∀ s ∈ Correction.allSites, s.statRd.isSome = true →
    (inRound s.pc || tailR s) = true := by decide +kernel

private theorem full_tab : ∀ q : Fin 2,
    (arrivePts (96 + 8 * q.val)).countP (before (.rscale q)) = 1 ∧
      (arrivePts (96 + 8 * q.val)).countP inRound = 1 := by decide +kernel

/-- **A statistics read's address, ordinal and round**: the ordinal is the round of a scale read,
its P-full arrivals, and one more than the rescale rounds at the final stage's reads. -/
theorem corr_stat_ord (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : 8 ≤ Prologue.warpIndex L h) (hw1 : Prologue.warpIndex L h ≤ 11)
    {pc : Nat} {a : Acc} {bs : List (Option Byte)} (he : X.get (h, k) = some ⟨pc, .rd a bs⟩)
    {s : Correction.Site} {n st : Fin 2} (hs : s.statRd = some (n, st)) (hpc : pc = s.pc) :
    a.size = 4 ∧ a.loc = ⟨.shared, h / L.block, L.sharedBase + 368 + 1024 * n.val +
        4 * (128 * st.val + Correction.rowN L h)⟩ ∧
      ∃ A, 1 ≤ A ∧
        ((X.tr h).take k).countP (Execution.isBarId (Prologue.warpIndex L h - 5 + 4 * st.val)) =
          A + 1 ∧ (∃ R, CorrRounds p L h R ∧ (tailR s = true → A = R + 1) ∧
            (inRound s.pc = true → A ≤ R)) ∧ (s = .rscale st → Tm.pArr L X h st k = A) := by
  rcases CorrWarp.open_ev hp hX hFw hw hw1 he (fun f h => by cases h) with
    ⟨s', n', -, -, -, hi, hev⟩ | ⟨d, n', hσ, h0, hR, hi, hev1, hevR⟩
  · exact (start_mem hev hi.2 trivial).elim
  obtain ⟨t, ins, o, hat, hi', hc, hf⟩ :=
    Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ (by intro f h; cases h)
  have hpc' : pc = d.site.pc := Frame.event_pcU (fun g hg => thread_sound hp hg) hX he hσ
    (by intro f h; cases h)
  have hd : d.site = s := site_tab _ (Correction.mem_allSites _) _ (Correction.mem_allSites _)
    (by rw [hs]; rfl) (hpc'.symm.trans hpc)
  obtain ⟨⟨⟨r, ℓ, hQ⟩, -⟩, -⟩ := hR h0
  obtain ⟨hz, hl⟩ := Correction.stat_rd hp hat hi' hc hf (hd ▸ hs) rfl
  have hsd : d.scheduler.site = s := hd
  refine ⟨hz, hl, 1 + r, by omega, ?_, ?_, fun h => ?_⟩
  · obtain ⟨t1, t2⟩ := nb_tab st
    rw [corr_isBarId hw hw1, count hσ]
    have c1 : n' (.corr (.nb st)) = _ := hQ.cnt (.nb st) (by simp)
    dsimp only at c1
    rw [c1, passed, hsd, t1 _ (Correction.mem_allSites _) n hs, t2]
    omega
  · obtain ⟨h1, h2⟩ := CorrWarp.rt_site (s := d.scheduler.site)
      (by rw [hsd]; exact ne_tab _ (Correction.mem_allSites _) (by rw [hs]; rfl))
    have hR := Correction.corr_rounds hp hX hFw hw hw1 he (by intro f h; cases h) hσ h1 h2
    refine ⟨_, hR, fun ht => ?_, fun hl => ?_⟩
    · have := hQ.tail (by rw [hsd]; exact ht)
      simp only at this
      omega
    · have := hQ.loop (by rw [hsd]; exact hl)
      simp only at this
      omega
  · obtain ⟨t1, t2⟩ := full_tab st
    have c1 : n' (.corr (.arrive (96 + 8 * st.val))) = _ :=
      hQ.cnt (.arrive (96 + 8 * st.val)) (by simp)
    dsimp only at c1
    rw [Correction.pArr_at hσ, c1, passed, hsd, h]
    show (arrivePts (96 + 8 * st.val)).countP _ + r * (arrivePts (96 + 8 * st.val)).countP _ = _
    rw [t1, t2]
    omega

/-- **A statistics read's address and ordinal.** -/
theorem corr_stat_site (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : 8 ≤ Prologue.warpIndex L h) (hw1 : Prologue.warpIndex L h ≤ 11)
    {pc : Nat} {a : Acc} {bs : List (Option Byte)} (he : X.get (h, k) = some ⟨pc, .rd a bs⟩)
    {s : Correction.Site} {n st : Fin 2} (hs : s.statRd = some (n, st)) (hpc : pc = s.pc) :
    a.size = 4 ∧ a.loc = ⟨.shared, h / L.block, L.sharedBase + 368 + 1024 * n.val +
        4 * (128 * st.val + Correction.rowN L h)⟩ ∧
      ∃ A, 1 ≤ A ∧
        ((X.tr h).take k).countP (Execution.isBarId (Prologue.warpIndex L h - 5 + 4 * st.val)) =
          A + 1 ∧ (n = 1 → ∃ R, CorrRounds p L h R ∧ A = R + 1) := by
  obtain ⟨h1, h2, A, h3, h4, ⟨R, hR, h5, -⟩, -⟩ := corr_stat_ord hp hX hFw hw hw1 he hs hpc
  refine ⟨h1, h2, A, h3, h4, fun hn => ⟨R, hR, h5 ?_⟩⟩
  subst hn
  exact tail_tab _ (Correction.mem_allSites _) _ hs

end
end PTX.Kernels.TmlFa4Fwd.Proof
