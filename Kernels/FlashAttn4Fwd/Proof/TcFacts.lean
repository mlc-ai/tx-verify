-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Safety.TcAccess
public import Kernels.FlashAttn4Fwd.Proof.Safety.TcCommit
public import Kernels.FlashAttn4Fwd.Proof.Safety.TcMmaReads
public import Kernels.FlashAttn4Fwd.Proof.Safety.TcMmaInstr
public import Kernels.FlashAttn4Fwd.Proof.Safety.HasUb
public import Kernels.FlashAttn4Fwd.Proof.Safety.Warp
public import Kernels.FlashAttn4Fwd.Proof.Protocol.TmemAlloc
public import Kernels.FlashAttn4Fwd.Proof.Protocol.PReadyPublished
public import Kernels.FlashAttn4Fwd.Proof.Protocol.OAcc
public import Kernels.FlashAttn4Fwd.Proof.Protocol.InitFirst

@[expose] public section

/-! # The Tensor Core branches' protocol inputs

This file sits at the top of the proof tree, outside the layer order (as `SafeFacts.lean` does):
it supplies the safety layer's Tensor Core and undefined-behaviour branches with the protocols'
exports, in the statements those branches take:

* the Tensor Memory orders between MMAs and stores (`tcOrders`): `Score.s_doneBefore`,
  `Score.store_done`, `OAcc.store_done`, `OAcc.done_store`;
* the A operand sources of the PV MMAs (`aSources`), with their written values, from the stores
  of `Safety.PvAStores` and `Score.p_aReadSource`;
* the commit targets' initializations (`pairInit`), from the thread facts' initializations
  (`TcFacts.init_done`), the start cluster barrier (`InitFirst.reach`) and
  `ClusterStart.init_published`;
* the base word's value (`baseZero`), from `TmemAlloc.read_zero`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof

open PTX PTX.Proof TcMma

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The Tensor Memory orders between MMAs and stores.** -/
theorem tcOrders (ht : ScoreFacts L X) (ho : OAccFacts L X) (hS : Score.SFullHandoff L X)
    (hP : Score.PReadyHandoff L X) (h2 : Score.P2Gate L X) (hR : OAcc.OReady L X) :
    Safety.TcOrders L X where
  s_done hh hw hi hc hu hf := Score.s_doneBefore ht hS hh hw hi hc hu hf
  p_done hh hw hs hf hc hlow hhigh := Score.store_done ht hP h2 hh hw hs hf hc hlow hhigh
  o_store_done hh h8 h12 hst hs hj hO hf hc hu :=
    OAcc.store_done ht ho hP hh h8 h12 hst hs hj hO hf hc hu
  o_done_store hh h8 h12 hs hj hO hx hxc hc hu :=
    OAcc.done_store ho hR hh h8 h12 hs hj hO hx hxc hc hu

/-- **Every A byte of a completed MMA has a source**, given the A operand's stores. -/
theorem aSources (hpre : Pre P L mem0) (ht : ScoreFacts L X) (ho : OAccFacts L X)
    (htc : TcFacts L X) (hP : Score.PReadyHandoff L X) (h2 : Score.P2Gate L X)
    (hS : Score.SFullHandoff L X) (hpa : Safety.PvAStores L X) : Safety.ASources L X := by
  intro i _ _ _ _ _ hdone cell ⟨d, s, acc, mask, index, pos, hi, hac⟩
  obtain ⟨c0, hc0⟩ := htc.mma_cell hi
  obtain ⟨-, -, -, st, hst, h | h⟩ := ht.mma_cells hi
  · have hnone := htc.qk_smem hst hi hc0 (h c0 hc0).1
    simp [aCell, hnone] at hac
  obtain ⟨hO, -⟩ := h c0 hc0
  obtain ⟨g, k, a, j, vals, value, hh, hw, hs, hj, rfl, htile, hwr, hlive⟩ := hpa hi hdone hac
  exact ⟨(g, k), value, Score.p_aReadSource hpre ht ho hP h2 hS hi hc0 hO hac hh hw hs hj htile
    hlive, hwr⟩

/-- **A barrier other than the handshake barrier of a CTA of the pair of an event after the
start is initialized.** -/
theorem init_exists (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : TcFacts L X) (hc : ClusterFacts L X) {b : FBar} (hb : b ≠ .dealloc) {cta g j : Nat}
    {ev : Event} (he : X.get (g, j) = some ev) (hk : ¬ PreKind ev.kind)
    (hub : ∀ f, ev.kind ≠ .ub f) (hcl : ctaOf L g / 2 = cta / 2) :
    ∃ e pc n, X.get e = some ⟨pc, .mbInit (b.loc L cta) n⟩ := by
  have hblk := hpre.block
  have hg := Frame.lt_of_get hX he
  have hcg := cta_lt hg
  have hgr := hpre.grid
  have hcta : cta < L.grid := by omega
  have h0 : cta * L.block < L.threads := by
    simp only [Launch.threads]
    exact Nat.mul_lt_mul_of_pos_right hcta (by omega)
  have hc0 : ctaOf L (cta * L.block) = cta := by
    simp only [ctaOf]; exact Nat.mul_div_cancel _ (by omega)
  have hw0 : warpOf L (cta * L.block) = 0 := by
    simp only [warpOf, Nat.mul_mod_left]
  have hr0 := InitFirst.reach hpre hX hc he hk hub h0 (by rw [hc0]; omega)
  rcases ht.init_done h0 hw0 hr0 with hi | ⟨k, -, pc, inst, l, hel, -⟩
  · obtain ⟨k, -, pc, n, hk⟩ := hi b hb
    rw [hc0] at hk
    exact ⟨_, pc, n, hk⟩
  · -- the leader lane of the warp reached its cluster arrival too; a full-mask election of the
    -- warp returns the same leader in every lane, so the leader lane did not elect another lane
    have hl32 : l < 32 := (hX.elect.1 _ _ _ _ _ hel).2.2.1
    have hh : cta * L.block + l < L.threads := by
      simp only [Launch.threads]
      rw [hblk] at ⊢
      nlinarith
    have hch : ctaOf L (cta * L.block + l) = cta := by
      simp only [ctaOf, hblk]
      omega
    have hwh : warpOf L (cta * L.block + l) = 0 := by
      simp only [warpOf, hblk]
      omega
    have hrh := InitFirst.reach hpre hX hc he hk hub hh (by rw [hch]; omega)
    rcases ht.init_done hh hwh hrh with hi | ⟨k', -, pc', inst', l', hel', hl'⟩
    · obtain ⟨k, -, pc, n, hk⟩ := hi b hb
      rw [hch] at hk
      exact ⟨_, pc, n, hk⟩
    · have hsw : SameWarp L (cta * L.block) (cta * L.block + l) :=
        ⟨⟨h0, hh, by rw [hblk]; omega⟩, by rw [hblk]; omega⟩
      have hll := hX.elect.2.2 _ _ _ _ _ _ _ _ _ hel hel' hsw
      refine absurd ?_ hl'
      rw [← hll]
      simp only [laneOf, hblk]
      omega

/-- **Every barrier but the handshake barrier of each CTA of the pair of an event after the
start has an initialization published to the event.** -/
theorem pairInit (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : TcFacts L X) (hc : ClusterFacts L X) : Safety.PairInit L X := by
  intro g j cta ev b he hk hub hb hcl
  obtain ⟨e, pci, n, hinit⟩ := init_exists hpre hX ht hc hb he hk hub hcl
  have hge := Frame.lt_of_get hX hinit
  obtain ⟨b', hm', -, -⟩ := hc.init_site hge hinit
  obtain ⟨-, hce⟩ := FBar.loc_inj hm'
  refine ⟨e, n, ⟨pci, hinit⟩, ClusterStart.init_published hpre hX hc hinit he hk hub ?_⟩
  rw [clusterOf_eq hpre, clusterOf_eq hpre, ← hce]
  omega

/-- **The base word's value.** -/
theorem baseZero (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (htm : TmemFacts L X) (hbr : TmemAlloc.BaseRead L X) : Safety.BaseZero L X :=
  fun _ hk hloc hsz hw => TmemAlloc.read_zero hpre hX htm hbr hk hloc hsz hw

end
end PTX.Kernels.FlashAttn4Fwd.Proof
