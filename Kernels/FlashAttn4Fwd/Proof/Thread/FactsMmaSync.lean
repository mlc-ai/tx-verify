-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsTmemLife
public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaCommit
public import Kernels.FlashAttn4Fwd.Proof.Interface.P2

@[expose] public section

/-! # The MMA warp's P-ready polls

A poll of warp 12 on a P-ready or second P-ready barrier is a poll site of its own CTA's barrier
of the stage (`mma_wait`), with the parity `pPar` of the item and trip, which is the parity of
the thread's earlier successful polls of the barrier (`Counts.pReady`, `Counts.pReady2`: `n i + t`
of them); the instruction is an acquire wait, widened to cluster scope by the assumption
`clusterMbar` at these sites. Other roles' polls of these barriers are the other packages'
part.

One thread of a pair issues the MMAs and the commits: each issuer is a lane of warp 12 of the
leader CTA that led every election of its trace (`lead_of_site`), and one lane of a warp leads
(`electLead_unique`; `ScoreFacts.tc_one`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The P-ready poll sites are cluster-scope sites of the assumption. -/
theorem asms_cluster_p : ∀ k : Fin 4,
    asms.any (·.clusterScopeMbar (Mma.Site.pWait k).pc) = true ∧
    ∀ b : Bool, asms.any (·.clusterScopeMbar (Mma.Site.p2Wait k b).pc) = true := by
  decide +kernel

/-- **The field `PReadyFacts.p_poll`, for warp 12.** -/
theorem PReadyFacts_p_poll_mma (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g i pc p c st : Nat} {ok acq : Bool} {sc : MbarScope}
    (_ : g < L.threads) (hw : warpOf L g = 12) (hst : st < 2)
    (he : X.get (g, i) = some ⟨pc, .wait (pReadyBar L c st) p ok acq sc⟩) :
    ctaOf L g = c ∧ warpOf L g = 12 ∧
      p % 2 = okPolls (pReadyBar L c st) ((X.tr g).take i) % 2 ∧
      (ok = true → acq = true ∧ sc = .cluster) := by
  rw [show pReadyBar L c st = pReadyBar L c (⟨st, hst⟩ : Fin 2) from rfl, pReadyBar_eq] at he ⊢
  obtain ⟨d, B, t, ins, hJ, hi, hB, hm, hp, hpc, hc, p', b, off, par, sc0, hop, hfl⟩ :=
    mma_wait hpre hX ht hw he
  obtain ⟨rfl, rfl⟩ := FBar.loc_inj hm
  refine ⟨rfl, hw, ?_, fun _ => ?_⟩
  · change p % 2 = okPolls (Mma.bar L g (.pReady ⟨st, hst⟩)) _ % 2
    rw [hJ.pReady, hp]
    have htr := hi.trip
    obtain ⟨site, ii, tt, base, pro⟩ := d
    cases site <;> simp [Mma.pollBar] at hB
    rename_i k
    fin_cases k <;> simp [Mma.stOf, Fin.ext_iff] at hB <;> subst hB <;>
      simp [Mma.TripOk, Mma.region] at htr <;>
      simp [Mma.pollPar, Mma.pPar, Mma.pBase, Mma.cnt, Mma.pA, Mma.Site.after, Mma.Site.inTrip,
        Mma.Site.loop, Mma.Site.ord, Mma.pOrd]
  · obtain ⟨site, ii, tt, base, pro⟩ := d
    cases site <;> simp [Mma.pollBar] at hB
    rename_i k
    simp only at hc hpc
    have hcl := (asms_cluster_p k).1
    fin_cases k <;> code_at hc <;> subst hc <;> simp only [Op.mbarWait.injEq] at hop <;>
      obtain ⟨-, -, -, -, rfl, rfl⟩ := hop <;> exact ⟨rfl, hfl (by rw [hpc]; exact hcl) rfl rfl⟩

/-- **The field `P2Facts.p2_poll`, for warp 12.** -/
theorem P2Facts_p2_poll_mma (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g i pc p c st : Nat} {ok acq : Bool} {sc : MbarScope}
    (_ : g < L.threads) (hw : warpOf L g = 12) (hst : st < 2)
    (he : X.get (g, i) = some ⟨pc, .wait (pReady2Bar L c st) p ok acq sc⟩) :
    ctaOf L g = c ∧ warpOf L g = 12 ∧
      p % 2 = okPolls (pReady2Bar L c st) ((X.tr g).take i) % 2 ∧
      (ok = true → acq = true ∧ sc = .cluster) := by
  rw [show pReady2Bar L c st = pReady2Bar L c (⟨st, hst⟩ : Fin 2) from rfl, pReady2Bar_eq]
    at he ⊢
  obtain ⟨d, B, t, ins, hJ, hi, hB, hm, hp, hpc, hc, p', b, off, par, sc0, hop, hfl⟩ :=
    mma_wait hpre hX ht hw he
  obtain ⟨rfl, rfl⟩ := FBar.loc_inj hm
  refine ⟨rfl, hw, ?_, fun _ => ?_⟩
  · change p % 2 = okPolls (Mma.bar L g (.pReady2 ⟨st, hst⟩)) _ % 2
    rw [hJ.pReady2, hp]
    have htr := hi.trip
    obtain ⟨site, ii, tt, base, pro⟩ := d
    cases site <;> simp [Mma.pollBar] at hB
    rename_i k ld
    fin_cases k <;> simp [Mma.stOf, Fin.ext_iff] at hB <;> subst hB <;>
      simp [Mma.TripOk, Mma.region] at htr <;>
      simp [Mma.pollPar, Mma.pPar, Mma.pBase, Mma.cnt, Mma.p2A, Mma.Site.after, Mma.Site.inTrip,
        Mma.Site.loop, Mma.Site.ord, Mma.p2Ord]
  · obtain ⟨site, ii, tt, base, pro⟩ := d
    cases site <;> simp [Mma.pollBar] at hB
    rename_i k ld
    simp only at hc hpc
    have hcl := (asms_cluster_p k).2 ld
    fin_cases k <;> code_at hc <;> subst hc <;> simp only [Op.mbarWait.injEq] at hop <;>
      obtain ⟨-, -, -, -, rfl, rfl⟩ := hop <;> exact ⟨rfl, hfl (by rw [hpc]; exact hcl) rfl rfl⟩

/-- **An issuer of an MMA or a commit** is a lane of warp 12 of a leader CTA that led every
election of its trace, and one returned its lane. -/
theorem issuer (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {i : EvId} (h : IsMma X i ∨ ∃ s, X.Commit i s) :
    warpOf L i.1 = 12 ∧ ctaOf L i.1 % 2 = 0 ∧ ElectLead L i.1 (X.tr i.1) ∧
      Elected (X.tr i.1) (laneOf L i.1) := by
  have hJl : ∀ {d : Mma.D}, Mma.Counts L i.1 d ((X.tr i.1).take i.2) → d.site.lead = true →
      ElectLead L i.1 (X.tr i.1) ∧ Elected (X.tr i.1) (laneOf L i.1) := fun hJ hl => by
    obtain ⟨e, he, inst, hk⟩ := hJ.elected hl
    exact ⟨lead_of_site hX hJ hl, e, List.mem_of_mem_take he, _, inst, hk⟩
  rcases h with hm | ⟨s, pc, he⟩
  · obtain ⟨hw, d, hJ, hi, hs⟩ := mma_issue_state hpre hX ht hm
    have hr := (hi.i (by obtain ⟨site, _⟩ := d; cases site <;> simp_all [Mma.Site.isMma,
      Mma.ItemSite])).2
    refine ⟨hw, by simpa [Mma.rank, ctaOf] using hr, hJl hJ ?_⟩
    obtain ⟨site, _⟩ := d
    cases site <;> simp_all [Mma.Site.isMma, Mma.Site.lead]
  · obtain ⟨hw, d, c, hJ, -, hs, -, hr, -⟩ := commit_state hpre hX ht he
    exact ⟨hw, by simpa [Mma.rank, ctaOf] using hr, hJl hJ (by rw [hs]; rfl)⟩

/-- **The field `ScoreFacts.tc_one`.** -/
theorem ScoreFacts_tc_one (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {i i' : EvId} (hm : IsMma X i)
    (h' : IsMma X i' ∨ ∃ s, X.Commit i' s)
    (hc : leadCta (ctaOf L i.1) = leadCta (ctaOf L i'.1)) : i.1 = i'.1 := by
  obtain ⟨hw, he, hL, hE⟩ := issuer hpre hX ht (.inl hm)
  obtain ⟨hw', he', hL', hE'⟩ := issuer hpre hX ht h'
  have hg : i.1 < L.threads := by
    obtain ⟨_, _, _, _, pc, hget⟩ := hm
    exact Frame.lt_of_get hX hget
  have hg' : i'.1 < L.threads := by
    rcases h' with ⟨_, _, _, _, pc, hget⟩ | ⟨_, pc, hget⟩ <;> exact Frame.lt_of_get hX hget
  have hcta : i.1 / L.block = i'.1 / L.block := by
    simp only [leadCta, ctaOf] at hc he he'
    omega
  have hsw : SameWarp L i.1 i'.1 := ⟨⟨hg, hg', hcta⟩, by
    simp only [warpOf] at hw hw'
    omega⟩
  exact electLead_unique hX.elect hsw (elect_mask_full hX _) (elect_mask_full hX _) hE hE' hL hL'

/-- The ring full poll sites are cluster-scope sites of the assumption. -/
theorem asms_cluster_full : (∀ k : Fin 2, asms.any (·.clusterScopeMbar (Mma.Site.qWait k).pc) =
    true) ∧ ∀ k : Fin 4, asms.any (·.clusterScopeMbar (Mma.Site.kvWait k).pc) = true := by
  decide +kernel

/-- **The field `RingFacts.poll`, for warp 12** (its polls of ring barriers are of the full
barriers). -/
theorem RingFacts_poll_mma (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g k pc p c : Nat} {b : FBar} {ok acq : Bool}
    {sc : MbarScope} (_ : g < L.threads) (hw : warpOf L g = 12)
    (he : X.get (g, k) = some ⟨pc, .wait (b.loc L c) p ok acq sc⟩) (hr : b.ring) :
    c = ctaOf L g ∧ (b.isFull → warpOf L g = 12 ∧ ctaOf L g % 2 = 0) ∧
      (b.isEmpty → warpOf L g = 14) ∧
      p % 2 = (okPolls (b.loc L c) ((X.tr g).take k) + b.pollOffset) % 2 ∧
      (ok = true → acq = true ∧ sc = .cluster) := by
  obtain ⟨d, B, t, ins, hJ, hi, hB, hm, hp, hpc, hc, p', b', off, par, sc0, hop, hfl⟩ :=
    mma_wait hpre hX ht hw he
  obtain ⟨rfl, rfl⟩ := FBar.loc_inj hm
  have hitem : Mma.ItemSite d.site := by
    obtain ⟨site, _⟩ := d
    cases site <;> simp [Mma.pollBar] at hB <;> subst hB <;> simp_all [Mma.ItemSite, FBar.ring]
  have hr0 := (hi.i hitem).2
  obtain ⟨site, ii, tt, base, pro⟩ := d
  cases site <;> simp [Mma.pollBar] at hB <;> subst hB <;> simp [FBar.ring] at hr
  all_goals simp only at hc hpc
  case qWait kk =>
    refine ⟨rfl, fun _ => ⟨hw, by simpa [Mma.rank, ctaOf] using hr0⟩, fun h => by
      simp [FBar.isEmpty] at h, ?_, fun _ => ?_⟩
    · change p % 2 = (okPolls (Mma.bar L g (.qFull kk)) _ + 0) % 2
      rw [hJ.qFull, hp]
      fin_cases kk <;> simp [Mma.pollPar, Mma.cnt, Mma.qA, Mma.Site.after, Mma.Site.ord,
        Mma.qOrd]
    · have hcl := asms_cluster_full.1 kk
      fin_cases kk <;> code_at hc <;> subst hc <;> simp only [Op.mbarWait.injEq] at hop <;>
        obtain ⟨-, -, -, -, rfl, rfl⟩ := hop <;>
        exact ⟨rfl, hfl (by rw [hpc]; exact hcl) rfl rfl⟩
  case kvWait kk =>
    refine ⟨rfl, fun _ => ⟨hw, by simpa [Mma.rank, ctaOf] using hr0⟩, fun h => by
      simp [FBar.isEmpty] at h, ?_, fun _ => ?_⟩
    · change p % 2 = (okPolls (Mma.bar L g (.kvFull _)) _ + 0) % 2
      rw [hJ.kvFull, hp, Mma.kv_cnt]
      simp only [Mma.pollPar, Mma.kvPar, Mma.slots, Mma.slotOf, Mma.kvSlot]
      omega
    · have hcl := asms_cluster_full.2 kk
      fin_cases kk <;> code_at hc <;> subst hc <;> simp only [Op.mbarWait.injEq] at hop <;>
        obtain ⟨-, -, -, -, rfl, rfl⟩ := hop <;>
        exact ⟨rfl, hfl (by rw [hpc]; exact hcl) rfl rfl⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof
