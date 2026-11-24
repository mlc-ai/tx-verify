-- SPDX-License-Identifier: Apache-2.0
module

import Lemmas.Kernel.FrameU

public import Kernels.TmlFa4Fwd.Proof.Correction.Export.Count
public import Kernels.TmlFa4Fwd.Proof.Correction.Export.MemRead
import Kernels.TmlFa4Fwd.Proof.Common.Sound
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Counts
import Kernels.TmlFa4Fwd.Proof.Epilogue.Export.ReadAddr
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Open
import Kernels.TmlFa4Fwd.Proof.CorrWarp.Warp
import Kernels.TmlFa4Fwd.Proof.Correction.Export.MbarSite
import Kernels.TmlFa4Fwd.Proof.Startup.Export.Mem
import Kernels.TmlFa4Fwd.Proof.Correction.Export.Mem

@[expose] public section

/-! # The correction lanes' counts at their statistics loads

A load of a stage's word follows one more event on the stage's named barrier than the lane's
arrivals on the stage's credit barrier. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof.Correction (ptsOf passed before inRound)

noncomputable section
set_option maxRecDepth 100000

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution} {h k : Nat}

private theorem stat_tab : ∀ q : Fin 2,
    (∀ s ∈ Correction.allSites, ∀ n, s.statRd = some (n, q) →
      (ptsOf (.nb q)).countP (before s) =
        (ptsOf (.arrive (192 + 8 * q.val))).countP (before s) + 1) ∧
    (ptsOf (.nb q)).countP inRound = 1 ∧
    (ptsOf (.arrive (192 + 8 * q.val))).countP inRound = 1 := by
  decide +kernel

/-- **A statistics load's counts and address.** -/
theorem corr_stat_rd (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow p L X) (hw : 8 ≤ Prologue.warpIndex L h) (hw1 : Prologue.warpIndex L h ≤ 11)
    {pc : Nat} {a : Acc} {bs : List (Option Byte)} (he : X.get (h, k) = some ⟨pc, .rd a bs⟩)
    (hsh : a.loc.space = .shared) :
    ∃ n st : Fin 2, a.size = 4 ∧ a.loc = ⟨.shared, h / L.block, L.sharedBase + 368 + 1024 * n.val +
        4 * (128 * st.val + Correction.rowN L h)⟩ ∧
      ((X.tr h).take k).countP (Execution.isBarId (Prologue.warpIndex L h - 5 + 4 * st.val)) =
        arrivals (obj L h (192 + 8 * st.val)) ((X.tr h).take k) + 1 := by
  rcases CorrWarp.open_ev hp hX hFw hw hw1 he (fun f h => by cases h) with
    ⟨s, n, -, -, -, hi, hev⟩ | ⟨d, n, hσ, h0, hR, hi, hev1, hevR⟩
  · exact (start_mem hev hi.2 trivial).elim
  obtain ⟨t, ins, o, hat, hi', hc, hf⟩ :=
    Frame.fired_siteU (fun g hg => thread_sound hp hg) hX he hσ (by intro f h; cases h)
  obtain ⟨⟨⟨r, ℓ, hQ⟩, -⟩, hF⟩ := hR h0
  obtain ⟨rv, -, -, hFE, -⟩ : CorrWarp.CFits p L h d (n .shfl) (n .vote) := hF
  have hev1 := hev1.data_or_vote.resolve_right (by rintro ⟨_,_,hh⟩; cases hh)
  have hstat : ∃ q, d.scheduler.site.statRd = some q := by
    by_contra hcon
    have hin : InWord p a := by
      cases hs : d.scheduler.site <;> simp only [Correction.Ev, hs] at hev1
      case word | q0 | q1 =>
        simp only [CorrWarp.EvR, hs] at hevR
        exact Epilogue.sched_rd hp hFE hevR rfl
      case uk =>
        simp only [CorrWarp.EvR, hs] at hevR
        rcases hevR with ⟨bs, hk⟩ | ⟨f, h⟩
        · simp only [Epilogue.Fits, CorrWarp.toE, hs, CorrWarp.epi] at hFE
          obtain ⟨R, bal, hC, -, -⟩ := hFE
          exact Epilogue.usedK_rd rfl hk (Epilogue.usedK_addr hp hC)
        · cases h
      case rscale | fsum | fmax => exact (hcon ⟨_, by rw [hs]; rfl⟩).elim
      all_goals exfalso
      all_goals try simp only [Epilogue.Ev, Correction.Site.toE] at hev1
      all_goals simp_all
    obtain ⟨-, ⟨_, -, hl⟩ | ⟨_, -, hl⟩ | ⟨_, -, _, -, hl⟩⟩ := hin <;>
      (rw [hl] at hsh; cases hsh)
  obtain ⟨⟨n', st⟩, hs⟩ := hstat
  obtain ⟨hz, hl⟩ := Correction.stat_rd hp hat hi' hc hf hs rfl
  refine ⟨n', st, hz, hl, ?_⟩
  obtain ⟨t1, t2, t3⟩ := stat_tab st
  rw [corr_isBarId hw hw1, corr_arrivals, count hσ, count hσ]
  have c1 : n (.corr (.nb st)) = _ := hQ.cnt (.nb st) (by simp)
  have c2 : n (.corr (.arrive (192 + 8 * st.val))) = _ := hQ.cnt _ (by simp)
  dsimp only at c1 c2
  rw [c1, c2, passed, passed, t1 _ (Correction.mem_allSites _) n' hs, t2, t3]
  omega

end
end PTX.Kernels.TmlFa4Fwd.Proof
