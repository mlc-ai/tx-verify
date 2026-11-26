-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Slots
public import Lemmas.Flow.Counted
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.RoundsPos
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Wg0
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Lane
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Class
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Time
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.EarlyCore

@[expose] public section

/-! # Warpgroup 0's performed poll of `svDone`

A successful poll at pc 1184 of a lane of CTA `c` is on the slot of the CTA's last block, with that
block's parity, after the lane's `(R - 1) / 2 + 1` successful polls of `qkDone` of that slot
(`wg0_svPoll`; the trace form of `wg0_svWait`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {y : Nat}

/-- **A performed poll of `svDone j` of CTA `c` at pc 1184** is on the slot of the CTA's last block
with its parity, after that slot's uses of `qkDone`. -/
theorem wg0_svPoll (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {jw c p : Nat} {j : Fin 2} {acq : Bool} {sc : MbarScope}
    (he : X.get (y, jw) = some ⟨1184, .wait (mbarLoc L c (.svDone j)) p true acq sc⟩) :
    y / L.block = c ∧ j = slot2 (blocksOf P L c - 1) ∧
      p % 2 = (blocksOf P L c - 1) / 2 % 2 ∧
      okPolls (mbarLoc L c (.qkDone j)) ((X.tr y).take jw) = (blocksOf P L c - 1) / 2 + 1 ∧
      ∀ b : Fin 2, okPolls (mbarLoc L c (.qkDone b)) ((X.tr y).take jw) =
        ringUses 2 b.val (blocksOf P L c) := by
  have hub : ∀ f, Kind.wait (mbarLoc L c (.svDone j)) p true acq sc ≠ .ub f :=
    fun _ h => by cases h
  obtain ⟨σ, hσ, hJ, hi, hev, hpc'⟩ := ev_at hp hX hFw he hub
  obtain ⟨d, n, rfl, hR, ⟨hpc, hk⟩, hw⟩ := wg0_state hJ hi hev hpc' ⟨by simp, by simp⟩
  have hc : (fun c => n (.wg0 c)) = fun c => ((X.tr y).take jw).countP (Wg0.cls c) :=
    funext fun c => state_count hσ (.wg0 c)
  have hR' := hR (state_ub hX hσ he)
  rw [hc] at hR'
  obtain ⟨hc, hL, -⟩ := hR' (wg0_take_noUb hX he)
  have hP := wg0_okPolls hp hX hFw hw jw
  rcases Wg0.evK_wait_site hk rfl with hs | hs | hs <;> rw [hs] at hpc <;>
    simp only [Wg0.Site.pc] at hpc <;> (try omega)
  have hb := Wg0.rounds_blocks hL (by rw [hs]; decide)
  unfold Wg0.EvK at hk; unfold Wg0.RefCore Wg0.RefAt at hc; rw [hs] at hk hc
  simp only [Wg0.Site.reg, Wg0.Site.idx, Nat.reduceEqDiff, ↓reduceIte] at hc
  obtain ⟨⟨hsl, hps⟩, hn', -⟩ := hc
  rcases hk with ⟨ok', hk⟩ | ⟨f, hk⟩
  · simp only [Kind.wait.injEq] at hk; obtain ⟨hl, hq, -⟩ := hk
    obtain ⟨site, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
    simp only [Wg0.Control.D.words] at hsl hps hb; subst hsl hps
    obtain ⟨hcy, hf⟩ := by simpa only [loc, mbarLoc, Loc.mk.injEq, Nat.add_left_cancel_iff,
      true_and] using hl.trans (Wg0.sv_loc hp (slot2 (Wg0.rounds l0 l1 - 1)))
    have hj : j = slot2 (Wg0.rounds l0 l1 - 1) := MbarFam.svDone.inj (MbarFam.off_inj hf)
    subst hcy hj
    have h2 : ∀ b : Fin 2, okPolls (mbarLoc L (y / L.block) (.qkDone b)) ((X.tr y).take jw) =
        ringUses 2 b.val (Wg0.rounds l0 l1) := fun b => by
      have h3 := (hP (loc L y (.qkDone b))).trans (hn' _)
      rw [Wg0.acq_qk hp, Wg0.use_lt (i := 0) (k := 2) (by decide)] at h3
      simpa only [loc, Wg0.Control.D.words] using h3
    refine ⟨rfl, by rw [hb], ?_, ?_, fun b => by rw [← hb]; exact h2 b⟩
    · rw [hq, Wg0.parW_W (Nat.mod_lt _ (by decide)), hb]
      exact Nat.mod_mod _ _
    · rw [← hb, h2]
      simp only [slot2, ringUses]
      have := blocksOf_pos hp (y / L.block)
      omega
  · cases hk

end

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
