-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaPollAgree
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsWarp
public import Kernels.FlashAttn4Fwd.Proof.Interface.TmemRoute

@[expose] public section

/-! # The lanes of the MMA warp at their elections of one ordinal

Two lanes' elections of one ordinal are one instance (`ElectOk`, `ElectOrdinal`), so they are at
one position: the prologue's election of warp 12, or one election site of the role
(`Mma.electSite_pc`). A lane's elections before an election site are the prologue's one and
`(8 n + 4) i + elA site + 8 t` of the role (`Counts.elects`), which with the trip facts gives the
item and the trip. The P-ready polls before it are a function of the site, the item and the trip
(`Counts.pReady`, `Counts.pReady2`; `RouteFacts.mma_elect`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The election sites are at distinct positions, none the prologue's election of warp 12. -/
theorem Mma.electSite_pc : Mma.allSites.all (fun s => Mma.allSites.all fun s' =>
    !(s.isElect && s'.isElect && decide (s.pc = s'.pc)) || decide (s = s')) = true ∧
    Mma.allSites.all (fun s => !s.isElect || decide (s.pc ≠ Prologue.Site.elect12.pc)) = true ∧
    Mma.allSites.all (fun s => !s.isElect ||
      (decide (Mma.region s = 1) && s.loop == 0) ||
      (decide (Mma.region s = 2) && s.loop == 1 && decide (Mma.elA s ≤ 12)) ||
      (decide (Mma.region s = 3) && s.loop == 1)) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- The state of an election of warp 12: the prologue's election, or an election site. -/
theorem mma_elect_state (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g k pc mask inst l : Nat} (hw : warpOf L g = 12)
    (he : X.Elect (g, k) pc mask inst l) :
    (pc = Prologue.Site.elect12.pc ∧ ∀ x ∈ (X.tr g).take k, Prologue.ProKind x.kind) ∨
    ∃ d : Mma.D, Mma.Counts L g d ((X.tr g).take k) ∧ Mma.Inv L g d ∧ d.site.isElect = true ∧
      pc = d.site.pc := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, t, ins, o, hσ, hJ, hat, hi, hc, hf⟩ :=
    event_origin hpre hX ht (fun g hg => roleJ_run hpre hg) he nofun
  have hpc := fires_pc hf
  rcases d with p | r
  · have hat' : At t p.site.pc (Prologue.facts L g p) :=
      ⟨hat.1, hat.2.1, hat.2.2.1, hat.2.2.2.1, hat.2.2.2.2⟩
    have hev : Prologue.EvOk L g p.site (.elect mask inst l) := by
      rcases Prologue.event_cases hpre hat' hc hf with h | ⟨⟨f, hf'⟩, -⟩
      · exact h
      · cases hf'
    refine .inl ⟨?_, hJ.1⟩
    obtain ⟨s⟩ := p
    cases s <;> simp [Prologue.EvOk] at hev
    · exact hpc
    · rename_i k'
      exact absurd (hi.warp0 (.inl ⟨k', rfl⟩)) (by omega)
  · obtain ⟨m, rfl⟩ := mma_of_warp hpre hX hg hw hσ
    refine .inr ⟨m, hJ, hi.1, ?_, hpc⟩
    cases hs : m.site.isElect
    · have := Mma.notElect_site hc hf hs
      simp [Mma.isElectE] at this
    · rfl

/-- The elections before an election site give the item and the trip. -/
theorem Mma.elect_it {g g' : Nat} {d d' : Mma.D} (hi : Mma.Inv L g d) (hi' : Mma.Inv L g' d')
    (hs : d.site = d'.site) (he : d.site.isElect = true)
    (hc : Mma.cnt L Mma.elA 8 4 d = Mma.cnt L Mma.elA 8 4 d') : d.i = d'.i ∧ d.t = d'.t := by
  have htr := hi.trip
  have htr' := hi'.trip
  have h12 := List.all_eq_true.mp Mma.electSite_pc.2.2 d.site (Mma.mem_allSites _)
  rw [he] at h12
  obtain ⟨site, i, t, base, pro⟩ := d
  obtain ⟨site', i', t', base', pro'⟩ := d'
  simp only at hs he hc htr htr' h12 ⊢
  subst hs
  unfold Mma.cnt at hc
  simp only at hc
  have hpos : 0 < 8 * Mma.trips L + 4 := by omega
  unfold Mma.TripOk at htr htr'
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h12
  rcases h12 with (⟨h1, hl⟩ | ⟨⟨h1, hl⟩, ha⟩) | ⟨h1, hl⟩ <;> rw [h1] at htr htr' <;>
    simp only at htr htr' <;> rw [hl] at hc
  · subst htr htr'
    exact ⟨Nat.eq_of_mul_eq_mul_left hpos (by simpa using hc), rfl⟩
  · have hc' : (8 * Mma.trips L + 4) * i + (Mma.elA site + 8 * t) =
        (8 * Mma.trips L + 4) * i' + (Mma.elA site + 8 * t') := by simp at hc; omega
    obtain ⟨h1, h2⟩ := divmod_unique hc' (by omega) (by omega)
    exact ⟨h1, by omega⟩
  · have ht : t = t' := by omega
    subst ht
    exact ⟨Nat.eq_of_mul_eq_mul_left hpos (by simp only [Nat.mul_one] at hc; omega), rfl⟩

theorem isElectE_eq (x : Event) : Mma.isElectE x = isElectEv x := by
  obtain ⟨_, k⟩ := x
  cases k <;> rfl

/-- A count formula is a function of the site, the item and the trip. -/
theorem Mma.cnt_congr {A : Mma.Site → Nat} {m k : Nat} {d d' : Mma.D} (hs : d.site = d'.site)
    (hi : d.i = d'.i) (ht : d.t = d'.t) : Mma.cnt L A m k d = Mma.cnt L A m k d' := by
  simp only [Mma.cnt, hs, hi, ht]

/-- The full mask names every lane. -/
theorem electMember_lane (g : Nat) : electMember 4294967295 (laneOf L g) := by
  have hl : laneOf L g < 32 := Nat.mod_lt _ (by decide)
  revert hl
  generalize laneOf L g = lane
  revert lane
  decide

/-- **An election has an election of each lane its mask names**, of its instance, at the same
site with the same mask and leader (DEP-WARP-ELECT: the elections of the lanes are its needs). -/
theorem elect_participant (hX : Consistent L kernel asms mem0 X) {h g y pc mask inst l : Nat}
    (hs : SameWarp L h g) (hy : X.Elect (h, y) pc mask inst l)
    (hm : electMember mask (laneOf L g)) : ∃ j, X.Elect (g, j) pc mask inst l := by
  obtain ⟨j, pc1, pc2, m1, m2, i1, l1, l2, h1, h2⟩ := ElectOrd.partner hX hs hy hm
  have e1 : X.get (h, y) = some ⟨pc, .elect mask inst l⟩ := hy
  have e2 : X.get (h, y) = some ⟨pc1, .elect m1 i1 l1⟩ := h1
  rw [e1] at e2
  simp only [Option.some.injEq, Event.mk.injEq, Kind.elect.injEq] at e2
  obtain ⟨rfl, rfl, rfl, rfl⟩ := e2
  obtain ⟨rfl, rfl, rfl, -⟩ := hX.elect.2.1 _ _ _ _ _ _ _ _ _ hy h2 hs
  exact ⟨j, h2⟩

/-- **The field `RouteFacts.mma_elect`.** -/
theorem RouteFacts_mma_elect (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {h h' e e' pc pc' mask mask' inst inst' l l' st : Nat}
    (_ : h < L.threads) (hw : warpOf L h = 12) (hs : SameWarp L h h') (hst : st < 2)
    (he : X.Elect (h, e) pc mask inst l) (he' : X.Elect (h', e') pc' mask' inst' l')
    (hc : ((X.tr h).take e).countP isElectEv = ((X.tr h').take e').countP isElectEv) :
    pPolls L X h st e = pPolls L X h' st e' ∧ p2Polls L X h st e = p2Polls L X h' st e' := by
  have hw' : warpOf L h' = 12 := by rw [← hw]; exact hs.2.symm
  have hcta : h / L.block = h' / L.block := hs.1.2.2
  obtain rfl := elect_full hX he
  obtain ⟨j, hj⟩ := elect_participant hX hs he (electMember_lane (L := L) h')
  have ho := electOrdinal hX (ElectMutual.of_full fun he => elect_full hX he) hs he hj
  have hje : j = e' := elect_eq_of_elections hj he' (by
    simp only at ho
    unfold elections
    omega)
  subst hje
  have hpc : pc' = pc := by
    have h1 : X.get (h', j) = some ⟨pc, .elect 4294967295 inst l⟩ := hj
    have h2 : X.get (h', j) = some ⟨pc', .elect mask' inst' l'⟩ := he'
    rw [h1] at h2
    simp only [Option.some.injEq, Event.mk.injEq] at h2
    exact h2.1.symm
  subst hpc
  rcases mma_elect_state hpre hX ht hw he with ⟨hp, hk⟩ | ⟨d, hJ, hi, hel, hdp⟩ <;>
    rcases mma_elect_state hpre hX ht hw' he' with ⟨hp', hk'⟩ | ⟨d', hJ', hi', hel', hdp'⟩
  · have hz : ∀ (q m : Nat) (es : List Event), (∀ x ∈ es, Prologue.ProKind x.kind) →
        okPolls ⟨.shared, q, m⟩ es = 0 := fun q m es hes =>
      List.countP_eq_zero.mpr fun x hx => by
        simp [((Prologue.ProKind.quiet (hes x hx)).1 _).1]
    exact ⟨(hz _ _ _ hk).trans (hz _ _ _ hk').symm, (hz _ _ _ hk).trans (hz _ _ _ hk').symm⟩
  · have := List.all_eq_true.mp Mma.electSite_pc.2.1 d'.site (Mma.mem_allSites _)
    simp [hel', ← hdp', hp] at this
  · have := List.all_eq_true.mp Mma.electSite_pc.2.1 d.site (Mma.mem_allSites _)
    simp [hel, ← hdp, hp'] at this
  · have hsite : d.site = d'.site := by
      have := List.all_eq_true.mp (List.all_eq_true.mp Mma.electSite_pc.1 d.site
        (Mma.mem_allSites _)) d'.site (Mma.mem_allSites _)
      simpa [hel, hel', ← hdp, ← hdp'] using this
    have he1 := hJ.elects
    have he2 := hJ'.elects
    rw [show ((X.tr h).take e).countP Mma.isElectE = ((X.tr h).take e).countP isElectEv from
      List.countP_congr fun x _ => by rw [isElectE_eq]] at he1
    rw [show ((X.tr h').take j).countP Mma.isElectE =
      ((X.tr h').take j).countP isElectEv from
      List.countP_congr fun x _ => by rw [isElectE_eq]] at he2
    obtain ⟨hii, htt⟩ := Mma.elect_it hi hi' hsite hel (by omega)
    have hb : ∀ b : FBar, Mma.bar L h b = Mma.bar L h' b := fun b => by simp [Mma.bar, hcta]
    unfold pPolls p2Polls
    rw [show pReadyBar L (ctaOf L h) st = Mma.bar L h (.pReady ⟨st, hst⟩) from rfl,
      show pReadyBar L (ctaOf L h') st = Mma.bar L h' (.pReady ⟨st, hst⟩) from rfl,
      show pReady2Bar L (ctaOf L h) st = Mma.bar L h (.pReady2 ⟨st, hst⟩) from rfl,
      show pReady2Bar L (ctaOf L h') st = Mma.bar L h' (.pReady2 ⟨st, hst⟩) from rfl,
      hJ.pReady, hJ'.pReady, hJ.pReady2, hJ'.pReady2]
    exact ⟨Mma.cnt_congr hsite hii htt, Mma.cnt_congr hsite hii htt⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof
