-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Reads

@[expose] public section

/-! # A QK MMA is done before a later PV MMA reading its cells

A QK MMA of tile `u` comes before the commit of tile `u`, which the stage's softmax lane of row 0
observes by its S-full poll of tile `u`; its P-full arrival of tile `u` follows that poll, and the
MMA lane's P-full poll of phase `u`, which the PV MMA follows, observes the arrival. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Tm
open PTX PTX.Proof PTX.Flow TcMma

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {A : List Assumption}

/-- The thread of row 0 of stage `st`'s softmax in CTA `c`. -/
def softRow0 (L : Launch) (c st : Nat) : Nat := c * L.block + 128 * st

/-- The thread of row 0 of a stage's softmax in an issuing thread's CTA is a softmax thread of the
stage, of that CTA. -/
theorem softRow0_spec (hpre : Pre P L mem0) {g st : Nat} (hg : g < L.threads) (hst : st < 2) :
    softRow0 L (g / L.block) st < L.threads ∧ Prologue.warpIndex L (softRow0 L (g / L.block) st) <
        8 ∧
      Prologue.warpIndex L (softRow0 L (g / L.block) st) / 4 = st ∧
      softRow0 L (g / L.block) st / L.block = g / L.block := by
  have hb := hpre.block
  unfold softRow0 Prologue.warpIndex
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
theorem scoreDonePv (hpre : Pre P L mem0) (ht : ScoreFacts L X)  (hS : SFullHandoff L X) (hP :
    PReadyHandoff L X) {w x : EvId}
    {cell : Cell} (hw : X.MmaCell w cell) (hx : X.MmaACell x cell) (hthr : w.1 = x.1)
    (hlt : w.2 < x.2) : DoneBefore L X w x := by
  obtain ⟨d, s, acc, mask, index, b, hxi, hac⟩ := hx
  obtain ⟨c0, hc0⟩ := ht.mma_cell hxi
  obtain ⟨hgx, -, st, hst, h | h⟩ := ht.mma_cells hxi
  · have hnone := ht.qk_smem hst hxi hc0 (h c0 hc0).1
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
    have := ht.pv_qk hst hxm hwm hthr.symm hc0 hO hw hS' (by omega)
    omega
  -- the softmax lane of row 0 of the stage
  have hin := mma_in ht hxm
  obtain ⟨hhl, hhw, hhst, hhc⟩ := softRow0_spec hpre hgx hst
  set h := softRow0 L (x.1 / L.block) st
  have hprod : pProd L (x.1 / L.block) st h := ⟨hhl, hhc, .inl ⟨hhw, hhst⟩⟩
  -- the MMA lane's poll of phase `u` observes the softmax arrival of tile `u`
  obtain ⟨j, pc, p, acq, sc, hjx, hwj, hcnt⟩ := MbarRing.UnitHandoff.exists_poll
    (X := X) (m := pFull L (x.1 / L.block) st) (h := x.1) (f := x.2) (c := u) hux
  obtain ⟨e, he, hsy⟩ := hP (x.1 / L.block) st hst x.1 j pc p acq sc u hin hwj hcnt h hprod
  obtain ⟨rs, ⟨tx, cnt, pce, hev⟩, -⟩ := id hsy
  have hev' : X.get (h, e) = some ⟨pce,
      .arrive (pFull L (h / L.block) (Prologue.warpIndex L h / 4)) tx cnt true rs⟩ := by
    rw [hhc, hhst]
    exact hev
  have hsp := ht.soft_p hhw hev'
  have hpa : pArr L X h st e = u := by
    unfold pArr
    rw [hhc]
    exact he
  rw [hhst, hpa] at hsp
  -- the softmax lane's S-full poll of tile `u` observes `w`'s completion
  obtain ⟨j', pc', p', acq', sc', hje, hwj', hcnt'⟩ := MbarRing.UnitHandoff.exists_poll
    (X := X) (m := sFull L (h / L.block) (Prologue.warpIndex L h / 4)) (h := h) (f := e) (c := u)
    (by rw [hhst]; exact hsp.le)
  have hcw : w.1 / L.block = h / L.block := by rw [hthr, hhc]
  obtain ⟨ws, ho, hsc⟩ := sfull_observes ht hS hhl hhw hwj' hwm hcw (by
    unfold sPolls
    rw [hcnt', hhst])
  have hel : e < (X.tr h).length := len_of_get hev
  have hhx : baseCausality L X (h, e) x :=
    overwrite_gate ht hP hst (by rw [hhc]; exact hprod) (u := u) hpa.le hxm hhc.symm hux
  exact .inl ⟨(h, j'), ws, ho, hsc, (baseCausality_src (f := (h, e)) hwj' rfl rfl hje hel).trans
      hhx⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof.Tm
