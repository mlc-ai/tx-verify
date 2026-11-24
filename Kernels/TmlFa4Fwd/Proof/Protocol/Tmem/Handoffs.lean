-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.Orders
public import Lemmas.Order.WarpBarOrdinal
import Kernels.TmlFa4Fwd.Proof.Correction.Export.TmemRoute
import Kernels.TmlFa4Fwd.Proof.Protocol.Credit.Handoff
import Kernels.TmlFa4Fwd.Proof.Protocol.O.Observed
import Kernels.TmlFa4Fwd.Proof.Protocol.P.Handoff
import Kernels.TmlFa4Fwd.Proof.Protocol.O.Hist
import Kernels.TmlFa4Fwd.Proof.Protocol.P.Rounds
import Kernels.TmlFa4Fwd.Proof.Protocol.S.Notify
public import Kernels.TmlFa4Fwd.Proof.Protocol.Tmem.FactsProof
import Kernels.TmlFa4Fwd.Proof.Softmax.Export.TmemWarp
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-! # The hand-offs the Tensor Memory orders need

The S-full, P-full and O-full hand-offs are the channels' (`sHandoff`, `pHandoff`, `o_handoff`).
The second P gate (`p2Gate`): a P store to the columns `112 …` of tile `u` is followed by its
`wait::st`, then by the lane's `u`-th warp barrier, whose instance holds the elected lane's, which
its arrival on the second P barrier in tile `u` follows. The routes of the correction accesses
(`oRoute`): a rescale access of credit `q` follows the statistics rendezvous of ordinal `q`, whose
softmax arrivals follow `q + 1` S-full polls; a final one follows the O-full poll. -/

namespace PTX.Kernels.TmlFa4Fwd.Proof.Tm
open PTX PTX.Proof PTX.Flow TcMma

noncomputable section

variable {p : Params} {L : Launch} {m : Mem0} {X : Execution}

omit X in
theorem scopes_meet {x h : Nat} (hx : x < L.threads) (hh : h < L.threads)
    (hc : x / L.block = h / L.block) : ScopesMeet L .cluster x .cta h :=
  ⟨⟨hx, hh, by rw [hc]⟩, hh, hx, hc.symm⟩

section
variable (hp : Pre p L m) (hX : Consistent L kernel Assumptions.all m X) (hFw : Follow p L X)
include hp hX hFw

theorem sFullHandoff : SFullHandoff L X := by
  intro h j pc par acq sc hh hw he
  have hst : Prologue.warpIndex L h / 4 < 2 := by omega
  obtain ⟨c, O⟩ := sNotify hp hX hFw h ⟨Prologue.warpIndex L h / 4, hst⟩
  obtain ⟨i, pc', s, rank, hget, hb, ht, hcnt, hr, hobs⟩ :=
    O.observes hX (sReach hp hX hFw O (h := h) ⟨hh, rfl, hw, rfl⟩) he rfl
  obtain ⟨hl, hcta, hwc, -, -⟩ := mma_commit_of hp hX hFw hget ht
  obtain ⟨-, rfl, rfl, -⟩ := s_poll hp hX hFw ⟨Prologue.warpIndex L h / 4, hst⟩ (g := h) he
  refine ⟨(c, i), s, rank, .cta, ⟨pc', hget⟩, hcta, ?_, ?_, ht, hr, hobs, scopes_meet hl hh hcta⟩
  · rw [hb]; simp only [obj, sFull, bar, hcta]
  · unfold sCommits sPolls
    simp only [hcta]
    exact hcnt

omit hp hX hFw in
/-- A thread of CTA `c`, when there is one. -/
private theorem cta_thread {c st h : Nat} (_hst : st < 2) (hh : mmaIn L c h) :
    MmaIn L h h ∧ h / L.block = c := ⟨⟨hh.1, rfl, hh.2.2⟩, hh.2.1⟩

theorem pReadyHandoff : PReadyHandoff L X := by
  intro c st hst h j pc par acq sc q hh he hq g hg
  obtain ⟨hm, hc⟩ := cta_thread hst hh
  subst hc
  obtain ⟨hgl, hgc, hgw⟩ := hg
  refine pHandoff hp hX hFw h ⟨st, hst⟩ h j pc par acq sc q hm he hq g ?_
  exact pLane_of hp hgc (hgw.imp_right fun ⟨h1, h2⟩ => ⟨h1, by omega⟩)

/-- **The warp barrier the second P poll follows**: when an MMA follows the poll of tile `u` of a
stage's second P-full barrier, every softmax lane of the stage and CTA has made its warp barrier of
the tile, and its events before that barrier happen before the MMA. -/
theorem p2_elected {h u : Nat} {f : EvId} (hh : h < L.threads) (hw : Prologue.warpIndex L h < 8)
    (hf : IsMma X f) (hc : f.1 / L.block = h / L.block)
    (hp2 : u + 1 ≤ p2Polls L X f.1 (Prologue.warpIndex L h / 4) f.2) :
    ∃ b mask inst, X.WarpBar (h, b) mask inst ∧ warpBars X h b = u ∧
      ∀ w < b, baseCausality L X (h, w) f := by
  have ht := scoreFacts hp hX hFw
  have hst : Prologue.warpIndex L h / 4 < 2 := by omega
  have hfin : mmaIn L (f.1 / L.block) f.1 := mma_in ht hf
  have hfm : MmaIn L f.1 f.1 := ⟨hfin.1, rfl, hfin.2.2⟩
  obtain ⟨j, pcw, par, acq, scw, hjf, hwj, hcnt⟩ := MbarRing.UnitHandoff.exists_poll (X := X)
    (h := f.1) (f := f.2) (m := p2Full L (f.1 / L.block) (Prologue.warpIndex L h / 4)) (c := u) hp2
  have hU := p2Handoff hp hX hFw f.1 ⟨Prologue.warpIndex L h / 4, hst⟩
  have ha4 : Prologue.warpIndex L h % 4 < 4 := Nat.mod_lt _ (by decide)
  have hprod := p2Prod_spec (X := X) (g := f.1) hp (st := Prologue.warpIndex L h / 4) hst
    ⟨Prologue.warpIndex L h % 4, ha4⟩
  set y := p2Prod L X f.1 (Prologue.warpIndex L h / 4) ⟨Prologue.warpIndex L h % 4, ha4⟩
  obtain ⟨k, hk, hsy⟩ := hU f.1 j pcw par acq scw u hfm hwj hcnt y ⟨_, rfl⟩
  obtain ⟨hyc, hyw⟩ := hprod
  simp only at hyw
  have hyw' : Prologue.warpIndex L y = Prologue.warpIndex L h := by omega
  obtain ⟨rs, ⟨tx, cnt, pck, hx⟩, -⟩ := id hsy
  have hyl : y < L.threads := Frame.lt_of_get hX hx
  have hround := p2_round hp hX hFw hst hx
  have hyc' : y / L.block = h / L.block := hyc.trans hc
  have hyb : warpBars X y k = u + 1 := by
    have hx' : X.get (y, k) = some ⟨pck,
        .arrive (p2Full L (y / L.block) (Prologue.warpIndex L y / 4)) tx cnt true rs⟩ := by
      rw [hyc, hyw']; exact hx
    have hb := Softmax.soft_p2_wb hp hX hFw (hyw'.symm ▸ hw) hx'
    rw [hyw'] at hb
    unfold sPolls at hb
    rw [hyc] at hb
    rw [hb]
    have hk' : arrivals (obj L f.1 (112 + 8 * (Prologue.warpIndex L h / 4)))
        ((X.tr y).take k) = u := hk
    rw [hk'] at hround
    exact hround.symm
  have hsame : SameWarp L y h := ⟨⟨hyl, hh, hyc'⟩, hyw'⟩
  -- the elected lane's warp barrier of the tile and the storing lane's
  obtain ⟨b, hbk, ev, hev, hqb, hcb⟩ := exists_nth Execution.isWarpBar (X.tr y) (n := u) (k := k)
    (by change _ < warpBars X y k; omega)
  obtain ⟨pcb, mb, inst, rfl⟩ : ∃ pc m inst, ev = ⟨pc, .warpBar m inst⟩ := by
    obtain ⟨pc, kind⟩ := ev
    cases kind <;> simp [Execution.isWarpBar] at hqb
    exact ⟨_, _, _, rfl⟩
  have hbw : X.WarpBar (y, b) mb inst := ⟨pcb, hev⟩
  have hfull : ∀ {g g' : Nat}, Prologue.warpIndex L g < 8 → ∀ j m inst, X.WarpBar (g, j) m inst →
      electMember m (laneOf L g') := by
    intro g g' hg j m inst hb
    rw [Softmax.soft_wb_mask hp hX hFw hg hb]
    exact electMember_full (Nat.mod_lt _ (by decide))
  have hmy := fun j m inst => hfull (g := y) (g' := h) (hyw'.symm ▸ hw) j m inst
  have hmh := fun j m inst => hfull (g := h) (g' := y) hw j m inst
  obtain ⟨b', hpar⟩ := WarpBar.partner hX hsame hbw (hmy _ _ _ hbw)
  have hord := WarpBar.ordinal_eq hX hsame hmy hmh hpar
  have hcb' : warpBars X y b = u := hcb
  obtain ⟨m', inst', -, hbw'⟩ := id hpar
  refine ⟨b', m', inst', hbw', hord.symm.trans hcb', fun w hwb => ?_⟩
  have hW : baseCausality L X (h, w) (y, k) :=
    WarpBar.sync (sameWarp_symm hsame) hpar.symm hwb hbk (len_of_get hx)
  exact hW.trans (hU.hb (q := u) hfm hwj hcnt ⟨_, rfl⟩ hk.le hjf (isMma_lt hf))

/-- **The second P gate.** -/
theorem p2Gate : P2Gate L X := by
  intro h i a vals f hh hw hs hhi hf hc hp2
  obtain ⟨-, hlen, q, hcol, h1, -, -⟩ := Softmax.soft_st hp hX hFw hw hs
  have hq := q.isLt
  have hcol' : 128 * (Prologue.warpIndex L h / 4) + 112 ≤ a % 65536 := by
    have := hhi 0 (by omega)
    unfold InPHigh at this
    simp only [tcDataCell32] at this
    omega
  have hwi := Softmax.soft_st_wb hp hX hFw hw hs hcol'
  obtain ⟨u, hu⟩ : ∃ u, sPolls L X h (Prologue.warpIndex L h / 4) i = u + 1 :=
    ⟨sPolls L X h (Prologue.warpIndex L h / 4) i - 1, by omega⟩
  rw [hu] at hwi hp2
  obtain ⟨b', m', inst', hbw', hbu, hhb⟩ := p2_elected hp hX hFw hh hw hf hc hp2
  obtain ⟨pcb', hbget⟩ := id hbw'
  obtain ⟨pcs, hsget⟩ := id hs
  have hib : i < b' := by
    by_contra hle
    rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hle) with hlt | rfl
    · have h2 := WarpBar.warpBars_succ hbw'
      have h3 := countP_take_mono Execution.isWarpBar (X.tr h) (show b' + 1 ≤ i by omega)
      change warpBars X h (b' + 1) ≤ warpBars X h i at h3
      omega
    · rw [hsget] at hbget
      cases hbget
  obtain ⟨w, pcw', hiw, hwb, hwget, -⟩ := Softmax.soft_st_wait hp hX hFw hw hs
    (e := b') ⟨hib, _, hbget, fun _ h => (nomatch h), fun _ h => (nomatch h)⟩
  exact ⟨w, pcw', hiw, hwget, hhb w hwb⟩

/-- **The O-full hand-off.** -/
theorem oFullHandoff : OFullHandoff L X := by
  intro h j pc par st acq sc hh h8 h12 hst he
  obtain ⟨rfl, rfl, rfl, h0⟩ := Correction.corr_o_poll hp hX hFw h8 (by omega) hst he
  have he' : X.get (h, j) = some ⟨pc, .wait (obj L h (oOff ⟨st, hst⟩)) 0 true true .cta⟩ := he
  obtain ⟨⟨y, i⟩, pc', s, rank, hc, ht⟩ := o_commit_exists hp hX hFw (z := h) he'
  obtain ⟨hy, hcta, hwy, hb, -⟩ := mma_commit_of hp hX hFw hc ht
  have hob : obj L y (oOff ⟨st, hst⟩) = obj L h (oOff ⟨st, hst⟩) := obj_cta hcta _
  have hH := o_hist hp hX hFw (st := ⟨st, hst⟩) (z := y) hc (by rw [hob]; exact ht)
  rw [hob] at hH
  have hobs := hH.observes_arrive hX (List.mem_singleton_self _) he'
  obtain ⟨ir, jr, d, w, hd, hid, -⟩ := hH.poll_observes hX he'
    (.inl ⟨_, List.mem_singleton_self _, rfl⟩)
  obtain ⟨-, -, -, -, hr⟩ := MbarRing.Reach.notify_rec hX (List.mem_of_getElem? hd) hid
  have hsb : s.mbar = oFull L (y / L.block) st := by rw [hcta]; exact hb
  refine ⟨(y, i), s, rank, .cta, ⟨pc', hc⟩, hcta, hsb, ?_, ht, hr, ⟨⟨_, _, he'⟩, hobs⟩,
    scopes_meet hy hh hcta⟩
  rw [h0]
  exact (mma_o_commit hp hX hFw ⟨st, hst⟩ hwy hc hsb).1

/-- **The routes of the correction accesses.** -/
theorem oRoute : ORoute L X := by
  intro h i a st vals hh h8 h12 hl hcells
  have hb := hp.block
  -- the stage is the columns'
  have hcol : 256 + 128 * st ≤ a % 65536 ∧ a % 65536 < 384 + 128 * st ∧ st < 2 := by
    have hlen : 0 < vals.length := by
      rcases hl with hl | hl
      · obtain ⟨_, _, _, _, -, -, -, _, ⟨_, -, -, e⟩ | ⟨_, -, -, e⟩⟩ :=
          Correction.corr_ld_state hp hX hFw h8 (by omega) hl <;> omega
      · obtain ⟨_, _, _, _, -, -, -, _, _, -, -, e⟩ :=
          Correction.corr_st_state hp hX hFw h8 (by omega) hl
        omega
    have h0 := hcells 0 hlen
    unfold InO at h0
    simp only [tcDataCell32] at h0
    refine ⟨by omega, by omega, ?_⟩
    rcases hl with hl | hl
    · obtain ⟨-, st', hst', e1, e2, -⟩ := Correction.corr_ld hp hX hFw h8 (by omega) hl
      omega
    · obtain ⟨-, st', hst', e1, e2, -⟩ := Correction.corr_st hp hX hFw h8 (by omega) hl
      omega
  obtain ⟨hc1, hc2, hst⟩ := hcol
  have hil : i < (X.tr h).length := hl.elim tLd_lt tSt_lt
  rcases Correction.corr_route hp hX hFw h8 (by omega) hl hc1 hc2 hst with ⟨hn, R, hR, hqR⟩ | ⟨ho,
      -⟩
  · -- the statistics rendezvous of ordinal `q`
    left
    set q := pArr L X h st i
    obtain ⟨kk, hkk⟩ : ∃ kk, Prologue.warpIndex L h = 8 + kk := ⟨_, (Nat.add_sub_of_le h8).symm⟩
    have hk4 : kk < 4 := by omega
    have hid : Prologue.warpIndex L h - 5 + 4 * st = statId st kk := by unfold statId; omega
    rw [hid] at hn
    obtain ⟨j, pcj, cnt, md, hji, hbar, hord⟩ :=
      exists_bar (X := X) (g := h) (x := i) (c := q) (id := statId st kk) (by
        show q + 1 ≤ _
        unfold barOrd
        omega)
    obtain ⟨rfl, hmd⟩ := stat_of_bar hp hX hFw hk4 hst hbar
    obtain rfl : md = .sync := by
      rcases hmd with ⟨hw, -⟩ | ⟨-, h⟩
      · omega
      · exact h
    obtain ⟨g, hgc, hgw⟩ : ∃ g, g / L.block = h / L.block ∧ Prologue.warpIndex L g = kk + 4 * st :=
      ⟨h / L.block * L.block + 32 * (kk + 4 * st), by rw [hb]; omega,
        by unfold Prologue.warpIndex; rw [hb]; omega⟩
    have hg : g < L.threads := thread_lt_of_cta hh hgc
    obtain ⟨e, pce, hearr, heord, -⟩ :=
      stat_rendezvous hp hX hFw hst hk4 hbar (by omega) hgc hgw
    have hgw8 : Prologue.warpIndex L g < 8 := by omega
    have hgs : Prologue.warpIndex L g / 4 = st := by omega
    have hord' : barOrd X g e (statId st kk) = q := heord.trans hord
    have hidg : statId st kk = Prologue.warpIndex L g + 3 := by unfold statId; omega
    have hpoll : sPolls L X g st e = q + 1 := by
      have hso : sobj L g 80 = sFull L (g / L.block) st := by
        simp only [sobj, obj, sFull, bar, hgs, Nat.add_comm]
      rcases soft_bar hp hX hFw hgw8 hearr with ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨-, -, -, -, h1⟩
      · unfold statId at h0; omega
      · unfold statId at h0; omega
      · unfold statId at h0; omega
      · unfold barOrd at hord'
        rw [hord', hso] at h1
        rcases h1 with h1 | ⟨-, h2⟩
        · exact h1
        · have := h2.corr hp hh hgc hR
          omega
    obtain ⟨j', pc', p', acq', sc', hj'e, hget, hcnt⟩ := MbarRing.UnitHandoff.exists_poll
      (X := X) (m := sFull L (g / L.block) st) (h := g) (f := e) (c := q) hpoll.ge
    refine ⟨g, j', pc', p', acq', sc', hg, hgc, hgw8, hgs, hget, hcnt, ?_⟩
    exact (stat_sources hp hX hFw hst hk4).arrive_sync_baseCausality hX (stat_shape hp hst hk4)
      ⟨hg, hh, hgc⟩ hearr hbar (by omega) heord hj'e hji hil
  · right
    obtain ⟨j, pc, par, acq, sc, hji, hget, -⟩ := MbarRing.UnitHandoff.exists_poll
      (X := X) (m := oFull L (h / L.block) st) (h := h) (f := i) (c := 0) ho
    refine ⟨j, pc, par, acq, sc, hji, hget, fun x hx hxc hxcta _ => ?_⟩
    obtain ⟨cell, hcl, hO⟩ := hxc
    obtain ⟨-, u, jj, hpv⟩ := pv_of_cell hp hX hFw hx hcl hO
    have := hpv.oc
    unfold oCommits
    omega

/-- **The hand-offs of the Tensor Memory orders.** -/
theorem handoffs : Handoffs L X :=
  ⟨sFullHandoff hp hX hFw, pReadyHandoff hp hX hFw, p2Gate hp hX hFw, oFullHandoff hp hX hFw,
    oRoute hp hX hFw⟩

end

end
end PTX.Kernels.TmlFa4Fwd.Proof.Tm
