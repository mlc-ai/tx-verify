-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Tma
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
public import Lemmas.Flow.Counted
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmaLen
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmaWords
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmaWon
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.TmaLane
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.ObjCnt
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.RefStep
import Kernels.FlashMlaSparseDecodeH64.Proof.Tma.Won

@[expose] public section

/-! # A TMA gather is of a use below the CTA's uses of its slot

A tensor load of the TMA lane to `rawReady b` follows `16 u + q` earlier loads to it, `q < 16`, of
a block `r < R` (the CTA's block count `blocksOf`, `Tma.LoopOk`, the lane's words `tma_words`), the
use `u` of the slot, so fewer than `16` times the CTA's uses of the slot. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- **The loads before a TMA gather are fewer than the sixteen loads of every use of its slot.** -/
theorem tma_gather_lt (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {g k a : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hat : TmaAt L g e.pc) {s : TensorCopy.Spec} (hk : e.kind = .tensorIssue a s) {b : Fin 2}
    (hm : s.mbar = mbarLoc L (g / L.block) (.rawReady b)) :
    ((X.tr g).take k).countP (issuesTo (mbarLoc L (g / L.block) (.rawReady b))) <
      16 * ringUses 2 b.val (blocksOf P L (g / L.block)) := by
  have hub : ∀ f, e.kind ≠ .ub f := by intro f h; rw [hk] at h; cases h
  obtain ⟨-, hr⟩ := hat
  obtain ⟨σ, hσ, hJ, hi, hev, hpc⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, hR, -, hE, hl, hw⟩ := tma_state hJ hi hev hpc hr
  obtain ⟨kk, hs⟩ := Tma.ev_gather hl hE hk
  have hpcR : 2165 < e.pc := by
    rw [hE.1, hs]
    exact (by decide : ∀ i : Fin 16, 2165 < (Tma.Site.gather i).pc) kk
  obtain ⟨j, hjk, inst, hj⟩ := tma_won hp hX hFw he hub ⟨hpcR, hr.2⟩
  have hu : ((X.tr g).take k).countP (cls .ub) = 0 :=
    (state_count hσ .ub).symm.trans (state_ub hX hσ he)
  obtain ⟨d', n', heq, -, hwd, hRc⟩ := tma_win_state hp hX hFw hj hjk hσ hu
  simp only [Prod.mk.injEq, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq] at heq
  obtain ⟨⟨-, -, -, rfl⟩, -⟩ := heq
  obtain ⟨⟨-, -, -, hrR, -, hbuf, -, -, -, -⟩, hn⟩ := (Tma.core_loop (by rw [hs]; rfl)).mp hRc
  have hrounds := tma_rounds_of (g := g) (d := d) (by simp [hs]) (by simp [hs]) hwd
  obtain ⟨-, hK⟩ := hE
  simp only [Tma.EvK, hs] at hK
  obtain ⟨a', s', hK, hmb⟩ | ⟨f, hK⟩ := hK
  · rw [hk] at hK
    simp only [Kind.tensorIssue.injEq] at hK
    obtain ⟨-, rfl⟩ := hK
    have hl' : MbarRow.loc L g (.rawReady b) =
        MbarRow.loc L g (.rawReady (slot2 d.cnt.toNat)) :=
      hm.symm.trans (hmb.trans ((Tma.raw_of hbuf).trans (Tma.raw_loc hp (slot2 d.cnt.toNat))))
    have hb : b = slot2 d.cnt.toNat := by
      have := Tma.loc_eq_iff.mp hl'
      cases this
      rfl
    have hI := lane5_issues hp hX hFw hw k (mbarLoc L (g / L.block) (.rawReady b))
    rw [hI, hn _ (by simp), Tma.tcnt_gather hp, hb]
    rw [hrounds] at hrR
    have hg := kk.isLt
    simp only [Tma.ind, Tma.Site.gN, hs, MbarRow.slot2, ringUses, ite_true, one_mul] at hrR ⊢
    omega
  · rw [hk] at hK
    cases hK

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
