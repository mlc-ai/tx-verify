-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Wg0
public import Lemmas.Flow.Polls
public import Lemmas.Flow.Counted
public import Kernels.FlashMlaSparseDecodeH64.Proof.Lib.Rounds
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.View
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Lane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.FollowStep
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Objs
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Nc
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.Export.Block

@[expose] public section

/-! # A store of warpgroup 0 is of a block below the CTA's block count

The rescale arm's stores are in the loop, where the lane's block `r` is below `rounds`, the CTA's
block count (`blocksOf`, `Wg0.rounds_blocks`): `wg0_stBlock_lt` is `wg0_stBlock` with the bound. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- A site whose event is a Tensor Memory store is a rescale store. -/
private theorem st_site' {g : Nat} {w : BitVec 64} {d : Wg0.Control.D} {e : Event} {a : Nat}
    {vals : List Value} {sh : TcShape} (h : Wg0.EvK P L g w d e)
    (hk : e.kind = .tc (.st a vals sh)) : ∃ c, d.site = .rst c := by
  obtain ⟨site, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  cases site <;> simp [Wg0.EvK, Wg0.PollEv, Wg0.ArrEv, GWrAt, RdAt, WrAt, GenWrAt, Wg0.NcEv,
    Wg0.TcLdEv, Wg0.TcStEv, hk] at h ⊢

/-- **The block of a store of warpgroup 0 is below the block count.** -/
theorem wg0_stBlock_lt (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X)
    (hFw : Follow P L X) {h k pc a : Nat} {vals : List Value} {sh : TcShape}
    (he : X.get (h, k) = some ⟨pc, .tc (.st a vals sh)⟩) (hat : MbarRow.Wg0At L h pc) :
    ∃ r, r < blocksOf P L (h / L.block) ∧ ∀ j : Fin 2,
      okPolls (mbarLoc L (h / L.block) (.qkDone j)) ((X.tr h).take k) = ringUses 2 j (r + 1) ∧
      arrivals (mbarLoc L (h / L.block) (.soReady j)) ((X.tr h).take k) = ringUses 2 j r := by
  obtain ⟨hw, hlo, hhi⟩ := hat
  have hub : ∀ f, (⟨pc, .tc (.st a vals sh)⟩ : Event).kind ≠ .ub f := fun _ h => by cases h
  obtain ⟨d, hR, ⟨-, hk⟩, -⟩ := wg0_at hp hX hFw he hub ⟨hlo, hhi⟩
  obtain ⟨hc, hL, -⟩ := hR (wg0_take_noUb hX he)
  obtain ⟨c, hs⟩ := st_site' hk rfl
  simp only [Wg0.RefCore, hs, Wg0.Site.reg, Wg0.Site.idx, Wg0.RefAt] at hc
  obtain ⟨r, ⟨-, -, hrR, -⟩, hq, ha⟩ := hc
  dsimp only at hq ha
  have hlens : 2 ≤ d.site.lens := by rw [hs]; simp [Wg0.Site.lens]
  have hrb := Wg0.rounds_blocks hL hlens
  simp only [Wg0.Control.D.words] at hrR
  refine ⟨r, by rw [← hrb]; exact hrR, fun j => ⟨?_, ?_⟩⟩
  · rw [show mbarLoc L (h / L.block) (.qkDone j) = loc L h (.qkDone j) from rfl,
      wg0_okPolls hp hX hFw hw, hq, Wg0.acq_qk hp]
    have := j.isLt
    unfold Wg0.use Wg0.ind ringUses
    split_ifs <;> omega
  · rw [show mbarLoc L (h / L.block) (.soReady j) = loc L h (.soReady j) from rfl,
      wg0_arrivals hp hX hFw hw, ha, Wg0.arr_so hp]

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
