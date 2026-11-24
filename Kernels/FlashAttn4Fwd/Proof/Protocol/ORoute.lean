-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Protocol.TmemReachPath

@[expose] public section

/-! # The routes of the correction's loads

**ORoute** (`oRoute`, the premise of `OAcc.oready`): a correction load of stage `st`'s
accumulator of credit `q` (`q` arrivals on the stage's P-ready object before it) is a rescale's or
a final pass's (`RouteFacts.corr_ld`).

* **rescale**: the load follows the correction's `bar.sync` on its statistics barrier of the
  stage of an ordinal `G` with `q + 1 ≤ genTiles n G`. The partner softmax warp's lane made its
  `bar.arrive` of ordinal `G` (`Stats.SoftArrives`, `soft_partner`), after an event with
  `genTiles n G` S-full polls before it (`RouteFacts.soft_gen`); that event happens before the
  load (`NamedBar.Sources.arrive_sync_baseCausality`, Core `CtaBarSync` with a `bar.arrive` source,
  as in `Stats.stats_baseCausality`) (`sync_route`).
* **final**: the load follows the correction's successful O-full poll of item `I` with
  `q ≤ n (I + 1)`; a PV MMA of the stage with at most `q` P-ready polls before it has
  `n · (O-full commits before it) < q ≤ n (I + 1)` (`RouteFacts.mma_pv`), so at most `I` O-full
  commits before it. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Flow PTX.Proof TcMma

noncomputable section

namespace OAcc
open Score

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution} {K : Kernel}
  {A : List Assumption}

/-- **The rescale route**: a correction event after its statistics `bar.sync` of stage `st` of an
ordinal `G` with `v ≤ genTiles n G` follows a softmax event of the stage and CTA with at least
`v` S-full polls before it. -/
theorem sync_route (H : RouteCtx P L mem0 K A X) {h i st v : Nat} (hh : h < L.threads)
    (h8 : 8 ≤ warpOf L h) (h12 : warpOf L h < 12) (hst : st < 2) (hlen : i < (X.tr h).length)
    (hs : CorrSync L X h st i v) :
    ∃ g e, g < L.threads ∧ ctaOf L g = ctaOf L h ∧ warpOf L g < 8 ∧ warpOf L g / 4 = st ∧
      e < (X.tr g).length ∧ v ≤ sPolls L X g st e ∧ baseCausality L X (g, e) (h, i) := by
  obtain ⟨y, pcy, hyi, hyget, hG⟩ := hs
  have hpass : y + 1 < (X.tr h).length := by omega
  obtain ⟨hgl, hgc, hgw, b, pc', cnt, md, hb, hord⟩ := soft_partner H hh h8 h12 hst hyget hpass
  have hw' : warpOf L (partnerLane L h st) < 8 := by omega
  obtain ⟨e, heb, hge⟩ := H.rt.soft_gen hgl hw' hb (by unfold statsId; omega)
  have hws : warpOf L (partnerLane L h st) / 4 = st := by omega
  rw [hord, hws] at hge
  have hk : warpOf L h - 8 < 4 := by omega
  refine ⟨partnerLane L h st, e, hgl, hgc, hw', hws, by
    have : b < (X.tr (partnerLane L h st)).length := len_of_get hb
    omega,
    by omega, ?_⟩
  exact (Stats.sources H.stf hk).arrive_sync_baseCausality H.cons (Stats.shape H.pre hst hk)
    ⟨hgl, hh, by unfold ctaOf at hgc; exact hgc⟩ hb hyget hpass
    (by unfold barOrd at hord; exact hord) heb hyi hlen

/-- **ORoute**: the routes of the correction's loads. -/
theorem oRoute (H : RouteCtx P L mem0 K A X) : ORoute L X := by
  intro h i a st vals hh h8 h12 hld hcells
  obtain ⟨st', hst', hpos, hcells', hroute⟩ := H.rt.corr_ld hh h8 h12 hld
  have hst : st = st' := by
    have h1 := hcells 0 hpos
    have h2 := hcells' 0 hpos
    unfold InO at h1 h2
    omega
  subst hst
  have hlen : i < (X.tr h).length := TLd.lt hld
  rcases hroute with hs | ⟨j, pc, p, acq, sc, hji, hget, hq⟩
  · exact .inl (sync_route H hh h8 h12 hst' hlen hs)
  · right
    refine ⟨j, pc, p, acq, sc, hji, hget, fun x hx hxc _ hu => ?_⟩
    obtain ⟨cell, hc, hO⟩ := hxc
    obtain ⟨d, s, acc, mask, hm⟩ := hx
    have hpv := H.rt.mma_pv ⟨d, s, acc, mask, hm⟩ hc hO
    have hlt : kvTiles L * oFullCommits L X x.1 st x.2 <
        kvTiles L * (okPolls (oFullBar L (ctaOf L h) st) ((X.tr h).take j) + 1) := by omega
    have := Nat.lt_of_mul_lt_mul_left hlt
    change oFullCommits L X x.1 st x.2 ≤ _
    omega

end OAcc

end
end PTX.Kernels.FlashAttn4Fwd.Proof
