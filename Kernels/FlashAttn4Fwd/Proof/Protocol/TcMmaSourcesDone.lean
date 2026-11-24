-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.ScoreHandoff
public import Kernels.FlashAttn4Fwd.Proof.Interface.TmemRoute
public import Kernels.FlashAttn4Fwd.Proof.Interface.TcMmaThread

@[expose] public section

/-! # A QK MMA is done before a later PV MMA reading its cells

A PV MMA `x` of stage `st` reads its A operand from the stage's probabilities (`InP st`, inside
the scores `InS st`), and a QK MMA `w` writing such a cell is the same thread's. When `w` is issued
before `x`, `w` is done before `x` (`scoreDonePv`, the premise `Safety.ScoreDonePv`):

* `w`, of score tile `u` (`u` S-full commits before it), comes before the commit of tile `u`, and
  `x` is of a tile after `u`: a PV MMA of tile `t` precedes the QK MMAs of every tile `≥ t`
  (`ScoreFacts.pv_qk`), so `x` follows the MMA thread's poll of phase `u` of the stage's P-ready
  object;
* that poll observes the P-ready arrival of tile `u` of the softmax thread of row 0 of the stage in
  the leader CTA (`PReadyHandoff`), which follows the thread's S-full poll of tile `u`
  (`RouteFacts.soft_p`);
* that S-full poll observes the completion of every MMA before the commit of tile `u`, `w` among
  them (`Score.sfull_observes`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof TcMma

noncomputable section

namespace TcMmaSources
open Score

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The thread of row 0 of stage `st`'s softmax in CTA `c`. -/
def softRow0 (L : Launch) (c st : Nat) : Nat := c * L.block + 128 * st

/-- The thread of row 0 of a stage's softmax in an issuing thread's CTA is a softmax thread of the
stage, of that CTA. -/
theorem softRow0_spec (hpre : Pre P L mem0) {g st : Nat} (hg : g < L.threads) (hst : st < 2) :
    softRow0 L (ctaOf L g) st < L.threads ∧ warpOf L (softRow0 L (ctaOf L g) st) < 8 ∧
      warpOf L (softRow0 L (ctaOf L g) st) / 4 = st ∧
      ctaOf L (softRow0 L (ctaOf L g) st) = ctaOf L g := by
  have hb := hpre.block
  unfold softRow0 warpOf ctaOf
  unfold Launch.threads at hg ⊢
  rw [hb] at hg ⊢
  have hc : g / 512 < L.grid := by
    rw [Nat.div_lt_iff_lt_mul (by decide)]
    exact hg
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : (g / 512 + 1) * 512 ≤ L.grid * 512 := Nat.mul_le_mul_right _ hc
    rw [Nat.add_mul] at this
    omega
  · omega
  · omega
  · omega

/-- **ScoreDonePv**: a QK MMA writing a cell that a later PV MMA of its thread reads as A is done
before that PV MMA. -/
theorem scoreDonePv (hpre : Pre P L mem0) (ht : ScoreFacts L X) (htc : TcFacts L X)
    (hr : RouteFacts L X) (hS : SFullHandoff L X) (hP : PReadyHandoff L X) {w x : EvId}
    {cell : Cell} (hw : X.MmaCell w cell) (hx : X.MmaACell x cell) (hthr : w.1 = x.1)
    (hlt : w.2 < x.2) : DoneBefore L X w x := by
  obtain ⟨d, s, acc, mask, index, b, hxi, hac⟩ := hx
  obtain ⟨c0, hc0⟩ := htc.mma_cell hxi
  obtain ⟨hgx, -, -, st, hst, h | h⟩ := ht.mma_cells hxi
  · have hnone := htc.qk_smem hst hxi hc0 (h c0 hc0).1
    simp [aCell, hnone] at hac
  obtain ⟨hO, -⟩ := h c0 hc0
  obtain ⟨-, -, -, hA⟩ := ht.pv_polls hxi hc0 hO
  obtain ⟨hPc, -, -⟩ := hA index cell b hac
  have hS' : InS st cell := by
    unfold InP at hPc
    exact ⟨by omega, hPc.2⟩
  obtain ⟨dw, sw, aw, mw, -, -, hwi, -⟩ := id hw
  have hwm : IsMma X w := ⟨_, _, _, _, hwi⟩
  have hxm : IsMma X x := ⟨_, _, _, _, hxi⟩
  -- `x` is of a tile after `w`'s
  set u := sCommits L X w.1 st w.2 with hu
  have hux : u + 1 ≤ pPolls L X x.1 st x.2 := by
    by_contra hn
    have := ht.pv_qk hxm hwm hthr.symm hc0 hO hw hS' (by omega)
    omega
  -- the softmax thread of row 0 of the stage, in the leader CTA
  obtain ⟨hin, hl⟩ := mma_in ht hxm
  obtain ⟨hhl, hhw, hhst, hhc⟩ := softRow0_spec hpre hgx hst
  set h := softRow0 L (ctaOf L x.1) st
  have hlh : leadCta (ctaOf L h) = ctaOf L x.1 := by rw [hhc, hl]
  have hprod : pProd L (ctaOf L x.1) st h := ⟨hhl, hlh, .inl ⟨hhw, hhst⟩⟩
  -- the MMA thread's poll of phase `u` observes the softmax arrival of tile `u`
  obtain ⟨j, pc, p, acq, sc, hjx, hwj, hcnt⟩ := MbarRing.UnitHandoff.exists_poll
    (X := X) (m := pReadyBar L (ctaOf L x.1) st) (h := x.1) (f := x.2) (c := u) hux
  obtain ⟨e, he, hsy⟩ := hP (ctaOf L x.1) st hl hst x.1 j pc p acq sc u hin hwj hcnt h hprod
  obtain ⟨rs, ⟨tx, cnt, pce, hev⟩, -⟩ := id hsy
  have hev' : X.get (h, e) = some ⟨pce,
      .arrive (pReadyBar L (leadCta (ctaOf L h)) (warpOf L h / 4)) tx cnt true rs⟩ := by
    rw [hlh, hhst]
    exact hev
  have hsp := hr.soft_p hhl hhw hev'
  have hpa : pArr L X h st e = u := by
    unfold pArr
    rw [hlh]
    exact he
  rw [hhst, hpa] at hsp
  -- the softmax thread's S-full poll of tile `u` observes `w`'s completion
  obtain ⟨j', pc', p', acq', sc', hje, hwj', hcnt'⟩ := MbarRing.UnitHandoff.exists_poll
    (X := X) (m := sFullBar L (ctaOf L h) (warpOf L h / 4)) (h := h) (f := e) (c := u)
    (by rw [hhst]; exact hsp)
  have hcw : leadCta (ctaOf L w.1) = leadCta (ctaOf L h) := by rw [hthr, hl, hlh]
  obtain ⟨ws, ho, hsc⟩ := sfull_observes ht hS hhl hhw hwj' hwm hcw (by
    unfold sPolls
    rw [hcnt', hhst])
  have hel : e < (X.tr h).length := len_of_get hev
  have hhx : baseCausality L X (h, e) x :=
    overwrite_gate ht hP hst (by rw [hlh]; exact hprod) (u := u) hpa.le hxm
      (by rw [hlh]) hux
  exact .inl ⟨(h, j'), ws, ho, hsc, (baseCausality_src (f := (h, e)) hwj' rfl rfl hje hel).trans
      hhx⟩

end TcMmaSources

end
end PTX.Kernels.FlashAttn4Fwd.Proof
