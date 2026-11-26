-- SPDX-License-Identifier: Apache-2.0
-- domain: consistent
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Follow
public import Kernels.FlashMlaSparseDecodeH64.Proof.Iface.MbarRows.Wg0
public import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Where
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0Lane
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0BarCnt
import Kernels.FlashMlaSparseDecodeH64.Proof.Common.Wg0BarLag
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.BarLoop
import Kernels.FlashMlaSparseDecodeH64.Proof.Wg0.BarSite

@[expose] public section

/-! # Where warpgroup 0's barrier 12 is

Barrier 12 (`barrier.sync 12`, pc 1835) is the role's barrier event of ordinal `3 R + 6`, `R` the
CTA's block count (`Wg0.idAt`), so a lane of warps 0–3 counts, by the barrier events of its trace:

* `wg0_ldstBar12`: a load or a store (a rescale site `sld`, `rld`, `old`, `rst`, of ordinal at most
  `3 R + 5`) has no barrier-12 event before it;
* `wg0_deallocBar12`: the deallocation (pc 1840, ordinal `3 R + 7`) has one before it;
* `wg0_exitBar12`: a lane that exits made one. -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution}

/-- The barrier events of ordinals up to `3 R + 6` hold no barrier 12 below `3 R + 6`. -/
private theorem idCnt_zero {R p B : Nat} (hp : p < 2) (h : B ≤ 3 * R + 6) :
    w0IdCnt R p 12 B = 0 := by
  unfold w0IdCnt
  refine List.length_eq_zero_iff.mpr (List.filter_eq_nil_iff.mpr fun o ho => ?_)
  have := List.mem_range.mp ho
  unfold Wg0.idAt
  simp only [decide_eq_true_eq]
  split_ifs <;> omega

/-- Barrier 12 is the event of ordinal `3 R + 6`: from ordinal `3 R + 7` one is counted. -/
private theorem idCnt_pos {R p B : Nat} (h : 3 * R + 7 ≤ B) : 1 ≤ w0IdCnt R p 12 B := by
  have h1 := w0IdCnt_mono (R := R) (p := p) (id := 12) (show 3 * R + 6 + 1 ≤ B by omega)
  have h2 := w0IdCnt_succ R p 12 (3 * R + 6)
  have h3 : Wg0.idAt R p (3 * R + 6) = 12 := by simp [Wg0.idAt]
  rw [h3] at h2
  simp only [ite_true] at h2
  omega

/-- A site whose event is a Tensor Memory load or store is a load or store site. -/
private theorem ldst_site {g : Nat} {w : BitVec 64} {d : Wg0.Control.D} {e : Event} {a : Nat}
    {vals : List Value} {sh : TcShape} (h : Wg0.EvK P L g w d e)
    (hk : e.kind = .tc (.ld a vals sh) ∨ e.kind = .tc (.st a vals sh)) :
    (∃ a0 k, d.site = .sld a0 k) ∨ (∃ c, d.site = .rld c) ∨ (∃ c, d.site = .old c) ∨
      ∃ c, d.site = .rst c := by
  obtain ⟨site, el, a0, l0, l1, cnt, bi, vs, pv, sl, ps, vt⟩ := d
  rcases hk with hk | hk <;>
  cases site <;> simp [Wg0.EvK, Wg0.PollEv, Wg0.ArrEv, GWrAt, RdAt, WrAt, GenWrAt, Wg0.NcEv,
    Wg0.TcLdEv, Wg0.TcStEv, hk] at h ⊢

section
variable (hp : Pre P L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow P L X)
include hp hX hFw

/-- The ordinal of a load or store site is at most `3 R + 5`. -/
private theorem ldst_ord {h k : Nat} {e : Event} {a : Nat} {vals : List Value} {sh : TcShape}
    (he : X.get (h, k) = some e) (hat : MbarRow.Wg0At L h e.pc)
    (hk : e.kind = .tc (.ld a vals sh) ∨ e.kind = .tc (.st a vals sh)) :
    w0BarCnt X h k ≤ 3 * blocksOf P L (h / L.block) + 5 := by
  have hub : ∀ f, e.kind ≠ .ub f := fun _ hf => by
    rcases hk with hk | hk <;> rw [hk] at hf <;> cases hf
  obtain ⟨d, hR, ⟨-, hE⟩, -⟩ := wg0_at hp hX hFw he hub ⟨hat.2.1, hat.2.2⟩
  obtain ⟨hC, hL, hB⟩ := hR (wg0_take_noUb hX he)
  have hbar : w0BarCnt X h k = Wg0.barOrd d := hB.2
  rw [hbar]
  have hlt := fun (hs : d.site.reg = .loop) (h2 : 2 ≤ d.site.lens) => barOrd_loop hC hL hs h2
  rcases ldst_site hE hk with ⟨a0, k0, hs⟩ | ⟨c, hs⟩ | ⟨c, hs⟩ | ⟨c, hs⟩
  · obtain ⟨r, hr, ho, -⟩ := hlt (by rw [hs]; rfl) (by rw [hs]; simp [Wg0.Site.lens])
    rw [ho, hs]
    simp only [Wg0.Site.bidx]
    omega
  · obtain ⟨r, hr, ho, -⟩ := hlt (by rw [hs]; rfl) (by rw [hs]; simp [Wg0.Site.lens])
    rw [ho, hs]
    simp only [Wg0.Site.bidx]
    omega
  · have h2 : 2 ≤ d.site.lens := by rw [hs]; simp [Wg0.Site.lens]
    have hR := Wg0.rounds_blocks hL h2
    have := c.isLt
    simp only [Wg0.barOrd, hs, Wg0.Site.reg, Wg0.Site.bidx, hR]
    omega
  · obtain ⟨r, hr, ho, -⟩ := hlt (by rw [hs]; rfl) (by rw [hs]; simp [Wg0.Site.lens])
    rw [ho, hs]
    simp only [Wg0.Site.bidx]
    omega

/-- **A barrier-12 event of warpgroup 0 is the closing barrier** (pc 1835). -/
theorem wg0_bar12_pc {h j pc : Nat} {cnt : Option Nat} {md : BarMode} (hw : MbarRow.warp L h < 4)
    (he : X.get (h, j) = some ⟨pc, .bar 12 cnt md⟩) : pc = 1835 := by
  have hr := w0_barPc hp hX hFw hw he (by omega)
  have hub : ∀ f, (Kind.bar 12 cnt md) ≠ .ub f := fun _ hf => by cases hf
  obtain ⟨d, -, ⟨hpc, hE⟩, -⟩ := wg0_at hp hX hFw he hub hr
  simp only at hpc
  rcases Wg0.evK_bar (d := d) hub hE rfl with ⟨-, hk⟩ | ⟨-, hk⟩ | ⟨h1, -⟩
  · simp only [Kind.bar.injEq] at hk
    obtain ⟨h9, -⟩ := hk
    omega
  · simp only [Kind.bar.injEq] at hk
    obtain ⟨h9, -⟩ := hk
    have := Wg0.barW_warp hp (g := h)
    omega
  · omega

/-- **A load or a store of warpgroup 0 has no barrier-12 event before it.** -/
theorem wg0_ldstBar12 {h k : Nat} {e : Event} {a : Nat} {vals : List Value} {sh : TcShape}
    (he : X.get (h, k) = some e) (hat : MbarRow.Wg0At L h e.pc)
    (hk : e.kind = .tc (.ld a vals sh) ∨ e.kind = .tc (.st a vals sh)) :
    ((X.tr h).take k).countP (Execution.isBarId 12) = 0 := by
  rw [w0_idCnt hp hX hFw hat.1 (by omega) le_rfl k (noUbBefore_of_get hX he)]
  exact idCnt_zero (Nat.mod_lt _ (by omega))
    ((ldst_ord hp hX hFw he hat hk).trans (by omega))

/-- **The deallocation of warpgroup 0 has a barrier-12 event before it.** -/
theorem wg0_deallocBar12 {h k : Nat} {e : Event} {grp : CtaGroup} {dst : Option Loc}
    {act : Tmem.Request} (he : X.get (h, k) = some e) (hat : MbarRow.Wg0At L h e.pc)
    (hk : e.kind = .tc (.resource grp dst act)) :
    1 ≤ ((X.tr h).take k).countP (Execution.isBarId 12) := by
  obtain ⟨hw, hlo, hhi⟩ := hat
  have hub : ∀ f, e.kind ≠ .ub f := fun _ hf => by rw [hk] at hf; cases hf
  obtain ⟨d, hR, hE, -⟩ := wg0_at hp hX hFw he hub ⟨hlo, hhi⟩
  obtain ⟨hC, hL, hB⟩ := hR (wg0_take_noUb hX he)
  have hs := Wg0.tmemOp_site hE (by simp [Tmem.Pair.isTmemOp, hk])
  have hbar : w0BarCnt X h k = Wg0.barOrd d := hB.2
  have h2 : 2 ≤ d.site.lens := by rw [hs]; simp [Wg0.Site.lens]
  have hR := Wg0.rounds_blocks hL h2
  have ho : Wg0.barOrd d = 3 * blocksOf P L (h / L.block) + 7 := by
    simp only [Wg0.barOrd, hs, Wg0.Site.reg, Wg0.Site.bidx, hR]
  rw [w0_idCnt hp hX hFw hw (by omega) le_rfl k (noUbBefore_of_get hX he)]
  exact idCnt_pos (by omega)

/-- **A lane of warps 0–3 that exits made a barrier-12 event.** -/
theorem wg0_exitBar12 {y j pc : Nat} (hw : warp L y < 4)
    (he : X.get (y, j) = some ⟨pc, .exit⟩) :
    1 ≤ (X.tr y).countP (Execution.isBarId 12) := by
  have hy := Frame.lt_of_get hX he
  have hge : 3 * blocksOf P L (y / L.block) + 7 ≤ w0BarCnt X y (X.tr y).length := by
    by_contra hlt
    exact (w0_lagB hp hX hFw hw hy (B := 3 * blocksOf P L (y / L.block) + 6) le_rfl
      (by omega) (LaneUbFree.of_exit hX hy he)).1 j pc he
  have h := w0_idCnt hp hX hFw hw (id := 12) (by omega) le_rfl (X.tr y).length
    (LaneUbFree.of_exit hX hy he)
  rw [List.take_length] at h
  rw [h]
  exact idCnt_pos hge

end

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
