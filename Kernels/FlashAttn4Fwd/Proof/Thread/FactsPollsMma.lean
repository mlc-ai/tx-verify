-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsPollsOn
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaBase
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.MmaRing
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.PReady
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.P2
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.Handshake

@[expose] public section

/-! # The MMA lane's polls

The `poll` fields of the MMA warp's poll classes (`MmaRingPollFacts`, `PReadyPollFacts`,
`P2PollFacts`, `HandshakePollFacts`): an MMA lane at a poll site polls the site's barrier
(`Mma.pollBar`) of its CTA with the site's parity (`Mma.site_event`, `wait_ev`), which is that of
its successful polls of the barrier (`Mma.Counts`: `qFull`, `kvFull`, `pReady`, `pReady2`,
`dealloc`, with the trip register's range `Mma.Inv.trip`). The poll sites of an item are the
leader CTA's (`Mma.Inv.i`), after the warp's `bar.sync 2` (`Mma.Counts.bar2`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- An MMA poll site's event is a wait on the site's barrier with the site's parity. -/
theorem mma_poll_site (hpre : Pre P L mem0) {g : Nat} (hg : g < L.threads) {d : Mma.D}
    {B : FBar} (hB : Mma.pollBar L d = some B) :
    (∀ t ins, (code L g).AtD (.inr (.mma d)) t →
      kernel.code[(code L g).pc (.inr (.mma d))]? = some ins → ∀ f,
        eventTmpl asms L g t ins.op ≠ .ub f) ∧
    ∀ t ins, (code L g).AtD (.inr (.mma d)) t →
      kernel.code[(code L g).pc (.inr (.mma d))]? = some ins → ∀ l p ok acq sc u,
      Fires ((code L g).pc (.inr (.mma d))) (eventTmpl asms L g t ins.op)
        ⟨(code L g).pc (.inr (.mma d)), .wait l p ok acq sc⟩ (some u) →
        l = Mma.bar L g B ∧ p = Mma.pollPar L d := by
  refine ⟨fun t ins hat hc f hf => ?_, fun t ins hat hc l p ok acq sc u hfire => ?_⟩
  · have hfu : Fires d.site.pc (eventTmpl asms L g t ins.op) ⟨d.site.pc, .ub f⟩ none := by
      rw [hf]
      exact ⟨rfl, rfl⟩
    have hev := Mma.site_event hpre hg hat.2.2.2.2 hc hfu
    obtain ⟨site, i, tt, base, pro⟩ := d
    cases site <;> simp [Mma.pollBar] at hB <;> simp [Mma.Ev] at hev
  · obtain ⟨B', hB', hl, hp⟩ := wait_ev (Mma.site_event hpre hg hat.2.2.2.2 hc hfire) rfl
    rw [hB] at hB'
    obtain rfl := Option.some.inj hB'
    exact ⟨hl, hp⟩

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
include hpre hX

/-- The common part of an MMA poll: `PollsOn` of the site's barrier, from the parity relation of
the role's counts at the trace's end. -/
theorem mma_pollsOn (ht : Frame.Tracked (code L) X) {g : Nat} {d : Mma.D} {B : FBar} {δ : Nat}
    (hg : g < L.threads) (hσ : St L X g (X.tr g).length = some (some (.inr (.mma d))))
    (hk : mmaKind d.site = .wait) (hB : Mma.pollBar L d = some B)
    (hpar : Mma.Counts L g d (X.tr g) → Mma.Inv L g d →
      Mma.pollPar L d % 2 = (okPolls (B.loc L (ctaOf L g)) (X.tr g) + δ) % 2) :
    PollsOn L X g (B.loc L (ctaOf L g)) δ := by
  obtain ⟨hub, hev⟩ := mma_poll_site hpre hg hB
  refine pollsOn_of_end hpre hX ht hg hσ hk (fun _ t ins hat _ hc => hub t ins hat hc)
    (fun hJ t ins hat hi hc l p ok acq sc u hf => ?_)
  obtain ⟨rfl, rfl⟩ := hev t ins hat hc l p ok acq sc u hf
  exact ⟨rfl, hpar hJ hi.1⟩

/-- The MMA lane at an item site is the leader CTA's lane of warp 12, past its `bar.sync 2`. -/
theorem mma_item_state (ht : Frame.Tracked (code L) X) (hok : Cross.SitesTmplOk L) {g : Nat}
    {d : Mma.D} (hg : g < L.threads) (hσ : St L X g (X.tr g).length = some (some (.inr (.mma d))))
    (hs : Mma.ItemSite d.site) :
    warpOf L g = 12 ∧ ctaOf L g % 2 = 0 ∧
      ∃ j pc, X.get (g, j) = some ⟨pc, .bar 2 (some 416) .sync⟩ := by
  have hw := Cross.role_of_state hpre hX hg hσ
  obtain ⟨hJ, hi⟩ := end_good hpre hX ht hok hg hσ
  have hJ' : Mma.Counts L g d ((X.tr g).take (X.tr g).length) := by
    rw [List.take_length]; exact hJ
  have hi' : Mma.Inv L g d := hi.1
  have hr := (hi'.i hs).2
  have hb : 0 < Mma.bar2A d.site := by
    obtain ⟨site, _⟩ := d
    cases site <;> simp_all [Mma.ItemSite, Mma.bar2A]
  obtain ⟨b, -, pc, hb, -⟩ := bar2_nth hJ' hb
  exact ⟨hw, by simpa [Mma.rank, ctaOf] using hr, b, pc, hb⟩

/-- **`MmaRingPollFacts.poll`**. -/
theorem MmaRingPollFacts_poll (ht : Frame.Tracked (code L) X) (hok : Cross.SitesTmplOk L) :
    ∀ {g : Nat} {d : Mma.D}, g < L.threads →
      St L X g (X.tr g).length = some (some (.inr (.mma d))) →
      ((∃ k, d.site = .qWait k) ∨ ∃ k, d.site = .kvWait k) →
      ctaOf L g % 2 = 0 ∧ warpOf L g = 12 ∧
        (∃ j pc, X.get (g, j) = some ⟨pc, .bar 2 (some 416) .sync⟩) ∧
        ∀ b, Mma.pollBar L d = some b → PollsOn L X g (b.loc L (ctaOf L g)) 0 := by
  intro g d hg hσ hs
  have hitem : Mma.ItemSite d.site := by
    rcases hs with ⟨k, hk⟩ | ⟨k, hk⟩ <;> rw [hk] <;> trivial
  obtain ⟨hw, hc, hbar⟩ := mma_item_state hpre hX ht hok hg hσ hitem
  refine ⟨hc, hw, hbar, fun b hB => ?_⟩
  have hk : mmaKind d.site = .wait := by
    rcases hs with ⟨k, hk⟩ | ⟨k, hk⟩ <;> rw [hk] <;> rfl
  refine mma_pollsOn hpre hX ht hg hσ hk hB fun hJ hi => ?_
  obtain ⟨site, ii, tt, base, pro⟩ := d
  rcases hs with ⟨kk, hk'⟩ | ⟨kk, hk'⟩ <;> simp only at hk' <;> subst hk' <;>
    simp only [Mma.pollBar, Option.some.injEq] at hB <;> subst hB
  · rw [Nat.add_zero]
    change _ = okPolls (Mma.bar L g (.qFull kk)) _ % 2
    rw [hJ.qFull]
    fin_cases kk <;> simp [Mma.pollPar, Mma.cnt, Mma.qA, Mma.Site.after, Mma.Site.ord, Mma.qOrd]
  · rw [Nat.add_zero]
    change _ = okPolls (Mma.bar L g (.kvFull _)) _ % 2
    rw [hJ.kvFull, Mma.kv_cnt]
    simp only [Mma.pollPar, Mma.kvPar, Mma.slots, Mma.slotOf, Mma.kvSlot]
    omega

/-- **`PReadyPollFacts.poll`**. -/
theorem PReadyPollFacts_poll (ht : Frame.Tracked (code L) X) (hok : Cross.SitesTmplOk L) :
    ∀ {g : Nat} {d : Mma.D} {k : Fin 4}, g < L.threads →
      St L X g (X.tr g).length = some (some (.inr (.mma d))) → d.site = .pWait k →
        warpOf L g = 12 ∧ leadCta (ctaOf L g) = ctaOf L g ∧
          PollsOn L X g (pReadyBar L (ctaOf L g) (k.val % 2)) 0 := by
  intro g d k hg hσ hs
  obtain ⟨hw, hc, -⟩ := mma_item_state hpre hX ht hok hg hσ (by rw [hs]; trivial)
  refine ⟨hw, by simp only [leadCta]; omega, ?_⟩
  have hB : Mma.pollBar L d = some (.pReady (Mma.stOf k)) := by simp [Mma.pollBar, hs]
  refine mma_pollsOn hpre hX ht hg hσ (by rw [hs]; rfl) hB fun hJ hi => ?_
  rw [Nat.add_zero]
  change _ = okPolls (Mma.bar L g (.pReady (Mma.stOf k))) _ % 2
  rw [hJ.pReady]
  have htr := hi.trip
  obtain ⟨site, ii, tt, base, pro⟩ := d
  simp only at hs
  subst hs
  fin_cases k <;> simp [Mma.TripOk, Mma.region] at htr <;>
    simp [Mma.pollPar, Mma.pPar, Mma.pBase, Mma.cnt, Mma.pA, Mma.Site.after, Mma.Site.inTrip,
      Mma.Site.loop, Mma.Site.ord, Mma.pOrd, Mma.stOf]

/-- **`P2PollFacts.poll`**. -/
theorem P2PollFacts_poll (ht : Frame.Tracked (code L) X) (hok : Cross.SitesTmplOk L) :
    ∀ {g : Nat} {d : Mma.D} {k : Fin 4} {lead : Bool}, g < L.threads →
      St L X g (X.tr g).length = some (some (.inr (.mma d))) → d.site = .p2Wait k lead →
        warpOf L g = 12 ∧ leadCta (ctaOf L g) = ctaOf L g ∧
          PollsOn L X g (pReady2Bar L (ctaOf L g) (k.val % 2)) 0 := by
  intro g d k lead hg hσ hs
  obtain ⟨hw, hc, -⟩ := mma_item_state hpre hX ht hok hg hσ (by rw [hs]; trivial)
  refine ⟨hw, by simp only [leadCta]; omega, ?_⟩
  have hB : Mma.pollBar L d = some (.pReady2 (Mma.stOf k)) := by simp [Mma.pollBar, hs]
  refine mma_pollsOn hpre hX ht hg hσ (by rw [hs]; rfl) hB fun hJ hi => ?_
  rw [Nat.add_zero]
  change _ = okPolls (Mma.bar L g (.pReady2 (Mma.stOf k))) _ % 2
  rw [hJ.pReady2]
  have htr := hi.trip
  obtain ⟨site, ii, tt, base, pro⟩ := d
  simp only at hs
  subst hs
  fin_cases k <;> simp [Mma.TripOk, Mma.region] at htr <;>
    simp [Mma.pollPar, Mma.pPar, Mma.pBase, Mma.cnt, Mma.p2A, Mma.Site.after, Mma.Site.inTrip,
      Mma.Site.loop, Mma.Site.ord, Mma.p2Ord, Mma.stOf]

/-- **`HandshakePollFacts.poll`**. -/
theorem HandshakePollFacts_poll (ht : Frame.Tracked (code L) X) (hok : Cross.SitesTmplOk L) :
    ∀ {g : Nat} {d : Mma.D}, g < L.threads →
      St L X g (X.tr g).length = some (some (.inr (.mma d))) → d.site = .waitDealloc →
        PollsOn L X g (FBar.loc L (ctaOf L g) .dealloc) 0 ∧
          okPolls (FBar.loc L (ctaOf L g) .dealloc) (X.tr g) = 0 := by
  intro g d hg hσ hs
  have hzero : Mma.Counts L g d (X.tr g) →
      okPolls (FBar.loc L (ctaOf L g) .dealloc) (X.tr g) = 0 := fun hJ => by
    have := hJ.dealloc
    rw [hs] at this
    exact this
  have hB : Mma.pollBar L d = some .dealloc := by simp [Mma.pollBar, hs]
  refine ⟨mma_pollsOn hpre hX ht hg hσ (by rw [hs]; rfl) hB fun hJ _ => ?_,
    hzero (end_good hpre hX ht hok hg hσ).1⟩
  rw [hzero hJ]
  simp [Mma.pollPar, hs]

end
end PTX.Kernels.FlashAttn4Fwd.Proof
