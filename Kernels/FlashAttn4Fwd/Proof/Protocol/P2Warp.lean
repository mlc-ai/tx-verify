-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.P2Obj

@[expose] public section

/-! # The second P-ready gate, from the warp rendezvous and the object's handoff

* **The warp part** (`warp_baseCausality`): a softmax lane's store of tile `u` to the columns `112
  …` is followed by a `wait::st` that happens before every arrival on the second P-ready object by a
  lane of its warp in tile `u`. The arriving lane passed its `u`-th warp barrier before arriving;
  that barrier's instance holds the storing lane's `u`-th warp barrier (`WarpBar.partner`,
  `WarpBar.ordinal_eq`: both lanes name every lane), which follows the store (the store has the warp
  barriers of the earlier tiles before it) and so the `wait::st` (`ScoreFacts.soft_st`: a warp
  barrier is not a `tcgen05` event); the rendezvous is causality (`WarpBar.sync`, DEP-WARP-BARRIER).
* **The object part** (`p2Obs`): `P2Obs` holds, from the object's handoff (`P2Handoff`): an
  arriving softmax lane is its warp's producer, and its arrival of tile `u` is its `u`-th.
* **P2Gate** (`p2Gate_of`): the MMA thread's poll of phase `u` synchronizes with the arrival of tile
  `u` of the producer of the storing lane's warp (the handoff, which provides the arrival), which
  the `wait::st` happens before (the warp part). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof TcMma

noncomputable section

namespace Score

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {K : Kernel}
  {A : List Assumption}

/-- A softmax lane's warp barriers name every lane. -/
theorem soft_mask (hF : P2Facts L X) {h g : Nat} (hh : h < L.threads) (hw : warpOf L h < 8) :
    ∀ j m inst, X.WarpBar (h, j) m inst → electMember m (laneOf L g) := by
  intro j m inst hb
  rw [hF.soft_warpBar hh hw hb]
  exact electMember_full (Nat.mod_lt _ (by decide))

/-- **The warp part.** A softmax lane's store of tile `u` to the columns `112 …` is followed by a
`wait::st` that happens before an arrival on the second P-ready object by a lane of its warp in
tile `u`. -/
theorem warp_baseCausality (hX : Consistent L K A mem0 X) (ht : ScoreFacts L X) (hF : P2Facts L X)
    {h i a g k pc' tx cnt c st : Nat} {vals : List Value} {rel : Bool} {sc : MbarScope}
    (hh : h < L.threads) (hw : warpOf L h < 8) (hs : X.TSt (h, i) a vals .s32x32b)
    (hhg : SameWarp L h g) (hst : st < 2)
    (hk : X.get (g, k) = some ⟨pc', .arrive (pReady2Bar L c st) tx cnt rel sc⟩)
    (hgk : sPolls L X g st k = sPolls L X h (warpOf L h / 4) i) :
    ∃ w pc, i < w ∧ X.get (h, w) = some ⟨pc, .tc .waitSt⟩ ∧ baseCausality L X (h, w) (g, k) := by
  have hg := hhg.1.2.1
  obtain ⟨-, hgw, hgst, -, -, -, -, -, hwb, -⟩ := hF.p2_arrive hg hst hk
  have hwe : warpOf L g = warpOf L h := hhg.2.symm
  rw [hwe] at hgw hgst
  subst hgst
  obtain ⟨-, -, h1, hwi, -, hwait⟩ := ht.soft_st hh hw hs
  obtain ⟨x, hxk, ev, hev, hq, hcnt⟩ := Flow.exists_nth Execution.isWarpBar (X.tr g)
    (n := sPolls L X h (warpOf L h / 4) i - 1) (k := k)
    (by change _ < warpBars X g k; omega)
  obtain ⟨pcx, m, inst, rfl⟩ : ∃ pc m inst, ev = ⟨pc, .warpBar m inst⟩ := by
    obtain ⟨pc, kind⟩ := ev
    cases kind <;> simp_all [Execution.isWarpBar]
  have hxw : X.WarpBar (g, x) m inst := ⟨pcx, hev⟩
  have hmg := soft_mask (g := h) hF hg (hwe ▸ hw)
  have hmh := soft_mask (g := g) hF hh hw
  obtain ⟨b, hp⟩ := WarpBar.partner hX (sameWarp_symm hhg) hxw (hmg _ _ _ hxw)
  have hord := WarpBar.ordinal_eq hX (sameWarp_symm hhg) hmg hmh hp
  obtain ⟨m', inst', -, hbw⟩ := id hp
  obtain ⟨pcs, hsget⟩ := id hs
  have hib : i < b := by
    by_contra hle
    rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hle) with hlt | rfl
    · have h2 := WarpBar.warpBars_succ hbw
      have h3 := Flow.countP_take_mono Execution.isWarpBar (X.tr h) (show b + 1 ≤ i by omega)
      change warpBars X g x = _ at hcnt
      change warpBars X h (b + 1) ≤ warpBars X h i at h3
      omega
    · obtain ⟨pcb, hpb⟩ := hbw
      rw [hsget] at hpb
      cases hpb
  obtain ⟨pcb, hbget⟩ := id hbw
  obtain ⟨w, pc, hiw, hwb', hwget, -⟩ :=
    hwait b ⟨hib, _, hbget, fun _ h => (nomatch h), fun _ h => (nomatch h)⟩
  exact ⟨w, pc, hiw, hwget, WarpBar.sync hhg hp.symm hwb' hxk (len_of_get hk)⟩

/-- **P2Gate**, from the warp rendezvous and the second objects' handoff. -/
theorem p2Gate_of (hX : Consistent L K A mem0 X) (hpre : Pre P L mem0) (ht : ScoreFacts L X)
    (hF : P2Facts L X) (hU : P2Handoff L X) : P2Gate L X := by
  intro h i a vals f hh hw hs _ hf hc hp2
  have hst : warpOf L h / 4 < 2 := by omega
  have h1 := (ht.soft_st hh hw hs).2.2.1
  obtain ⟨j, pcw, p, acq, scw, hjf, hwj, hcnt⟩ :=
    MbarRing.UnitHandoff.exists_poll (X := X) (h := f.1) (f := f.2)
      (m := pReady2Bar L (ctaOf L f.1) (warpOf L h / 4))
      (c := sPolls L X h (warpOf L h / 4) i - 1) (by unfold p2Polls at hp2; omega)
  obtain ⟨hin, hl⟩ := mma_in ht hf
  have hb := hpre.block
  have hlt : 4 * (ctaOf L h - ctaOf L f.1) + warpOf L h % 4 < 8 := by
    have := hc
    unfold leadCta warpOf ctaOf at *
    omega
  have hU' := hU _ _ hl hst
  obtain ⟨k, hk, hsy⟩ := hU' f.1 j pcw p acq scw
    (sPolls L X h (warpOf L h / 4) i - 1) hin hwj hcnt _ ⟨⟨_, hlt⟩, rfl⟩
  obtain ⟨rs, ⟨tx, cnt, pck, hx⟩, -⟩ := hsy
  have hg := event_thread_lt hX hx
  obtain ⟨hgc, hgw⟩ := p2Prod_spec (X := X) hpre (c := ctaOf L f.1) hst ⟨_, hlt⟩
  simp only at hgc hgw
  have hsame : SameWarp L h _ := sameWarp_of hh hg (by
      have := hc
      unfold leadCta at this
      simp only
      omega)
    (by simp only; omega)
  obtain ⟨-, -, -, -, -, -, -, harr, -⟩ := hF.p2_arrive hg hst hx
  obtain ⟨w, pcw', hiw, hwget, hW⟩ := warp_baseCausality hX ht hF hh hw hs hsame hst hx (by
    simp only at harr ⊢
    omega)
  exact ⟨w, pcw', hiw, hwget, hW.trans (hU'.hb (q := sPolls L X h (warpOf L h / 4) i - 1) hin hwj
    hcnt ⟨_, rfl⟩ hk.le hjf hf.lt)⟩

end Score

end
end PTX.Kernels.FlashAttn4Fwd.Proof
