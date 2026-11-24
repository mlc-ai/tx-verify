-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaCommit

@[expose] public section

/-! # The counts of the MMA warp's commits

A commit fires at a site of the elected lane, so its thread led every election of its trace
(`lead_of_site`) and the run invariant's commit counts hold at it:

* a commit to stage `st`'s S-full barrier of item `i` has `n i + x` commits there before it, `x`
  below the item's `n` tiles; one to an O-full barrier has `i`; the item passed the loop test
  (`Mma.Inv.i`; `ExitFacts.sfull_commit`, `ExitFacts.ofull_commit`);
* a commit to a ring empty barrier releases a use the thread polled the partner full barrier
  for (`RingFacts.commit`: the KV use `U` it releases is below the uses polled, the Q stage is
  polled once per item);
* the commit to `qEmpty 0` is commit site 7, and the thread's commit to `qEmpty 1` with as many
  earlier ones is site 8 of the same item, the thread's next commit (`Counts.commits` counts all
  commits; `ExitFacts.q_next`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- The barrier a commit names is its site's. -/
theorem commit_bar {g : Nat} {d : Mma.D} {c : Fin 12} {b : FBar} {sp : TcCommit.Spec}
    (hsp : sp = Mma.cSpec L g (Mma.bar L g (Mma.cBar L d c))) (hm : sp.mbar = b.loc L (ctaOf L g)) :
    Mma.cBar L d c = b := by
  subst hsp
  exact (FBar.loc_inj hm).1

/-- The KV ring trips of an item are the key-value blocks. -/
theorem trips_eq (hpre : Pre P L mem0) : Mma.trips L = kvBlocks P := by
  simp [Mma.trips, kvBlocks, skOf_eq hpre]

theorem mma_trips_pos (hpre : Pre P L mem0) : 0 < Mma.trips L := by
  have := skOf_eq hpre
  have := hpre.skPos
  unfold Mma.trips
  omega

/-- The ring uses `U < N` of a slot grow with `N`. -/
theorem slots_mono {N N' : Nat} (h : N ≤ N') (s : Fin 6) : Mma.slots N s ≤ Mma.slots N' s :=
  Nat.div_le_div_right (by omega)

theorem slots_succ_le {U N : Nat} (h : U < N) (s : Fin 6) (hs : U % 6 = s.val) :
    Mma.slots U s + 1 ≤ Mma.slots N s := by
  have := Mma.slots_succ U s
  simp only [hs, ite_true] at this
  rw [← this]
  exact slots_mono h s

/-- **The field `ExitFacts.sfull_commit`.** -/
theorem ExitFacts_sfull_commit (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g k pc st : Nat} {sp : TcCommit.Spec} (_ : g < L.threads)
    (hst : st < 2) (he : X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩)
    (hm : sp.mbar = sFullBar L (ctaOf L g) st) :
    workOf L g (((X.tr g).take k).countP (commitsTo sp.mbar) / kvBlocks P) < totOf L := by
  obtain ⟨-, d, c, hJ, hi, hs, hsp, -, -⟩ := commit_state hpre hX ht he
  have hL := lead_of_site hX hJ (by rw [hs]; rfl)
  rw [show sFullBar L (ctaOf L g) st = sFullBar L (ctaOf L g) (⟨st, hst⟩ : Fin 2) from rfl,
    sFullBar_eq] at hm
  have hb := commit_bar hsp hm
  have hcnt := hJ.sFull (hL.take k) ⟨st, hst⟩
  rw [show FBar.loc L (ctaOf L g) (.sFull ⟨st, hst⟩) = Mma.bar L g (.sFull ⟨st, hst⟩) from rfl]
    at hm
  rw [hm, hcnt, ← trips_eq hpre]
  have hw := (hi.i (by rw [hs]; trivial)).1
  have hn := mma_trips_pos hpre
  have htr := hi.trip
  suffices hq : Mma.cnt L (Mma.sA ⟨st, hst⟩) 1 0 d / Mma.trips L = d.i by
    rw [hq]
    exact hw
  apply Nat.div_eq_of_lt_le
  all_goals
    obtain ⟨site, i, tt, base, pro⟩ := d
    simp only at hs hb htr ⊢
    subst hs
    fin_cases c <;> simp [Mma.cBar] at hb <;> subst hb <;>
      simp [Mma.TripOk, Mma.region] at htr <;>
      simp [Mma.cnt, Mma.sA, Mma.Site.after, Mma.Site.inTrip, Mma.Site.loop, Mma.Site.ord,
        Mma.elCOrd] <;> nlinarith

/-- **The field `ExitFacts.ofull_commit`.** -/
theorem ExitFacts_ofull_commit (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g k pc st : Nat} {sp : TcCommit.Spec} (_ : g < L.threads)
    (hst : st < 2) (he : X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩)
    (hm : sp.mbar = oFullBar L (ctaOf L g) st) :
    workOf L g (((X.tr g).take k).countP (commitsTo sp.mbar)) < totOf L := by
  obtain ⟨-, d, c, hJ, hi, hs, hsp, -, -⟩ := commit_state hpre hX ht he
  have hL := lead_of_site hX hJ (by rw [hs]; rfl)
  rw [show oFullBar L (ctaOf L g) st = oFullBar L (ctaOf L g) (⟨st, hst⟩ : Fin 2) from rfl,
    oFullBar_eq] at hm
  have hb := commit_bar hsp hm
  have hcnt := hJ.oFull (hL.take k) ⟨st, hst⟩
  rw [show FBar.loc L (ctaOf L g) (.oFull ⟨st, hst⟩) = Mma.bar L g (.oFull ⟨st, hst⟩) from rfl]
    at hm
  rw [hm, hcnt]
  have hw := (hi.i (by rw [hs]; trivial)).1
  suffices hq : Mma.cnt L (Mma.ofA ⟨st, hst⟩) 0 1 d = d.i by
    rw [hq]
    exact hw
  obtain ⟨site, i, tt, base, pro⟩ := d
  simp only at hs hb ⊢
  subst hs
  fin_cases c <;> simp [Mma.cBar] at hb <;> subst hb <;>
    simp [Mma.cnt, Mma.ofA, Mma.Site.after, Mma.Site.loop, Mma.Site.ord, Mma.elCOrd]

/-- **The field `ExitFacts.q_next`.** -/
theorem ExitFacts_q_next (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g j j' pc pc' : Nat} {sp sp' : TcCommit.Spec}
    (_ : g < L.threads) (he : X.get (g, j) = some ⟨pc, .tc (.commit sp)⟩)
    (hm : sp.mbar = FBar.loc L (ctaOf L g) (.qEmpty 0)) :
    pc = 995 ∧
      (X.get (g, j') = some ⟨pc', .tc (.commit sp')⟩ →
        sp'.mbar = FBar.loc L (ctaOf L g) (.qEmpty 1) →
        ((X.tr g).take j').countP (commitsTo sp'.mbar) =
          ((X.tr g).take j).countP (commitsTo sp.mbar) →
        j < j' ∧
          ∀ k, j < k → k < j' → ∀ pck spk, X.get (g, k) ≠ some ⟨pck, .tc (.commit spk)⟩) := by
  obtain ⟨-, d, c, hJ, hi, hs, hsp, -, hpc⟩ := commit_state hpre hX ht he
  have hL := lead_of_site hX hJ (by rw [hs]; rfl)
  have hb := commit_bar hsp hm
  obtain rfl : c = 7 := by fin_cases c <;> simp [Mma.cBar] at hb ⊢
  refine ⟨by rw [hpc, hs]; decide, fun he' hm' hcnt => ?_⟩
  obtain ⟨-, d', c', hJ', hi', hs', hsp', -, -⟩ := commit_state hpre hX ht he'
  have hb' := commit_bar hsp' hm'
  obtain rfl : c' = 8 := by fin_cases c' <;> simp [Mma.cBar] at hb' ⊢
  have h0 := hJ.qEmpty (hL.take j) 0
  have h1 := hJ'.qEmpty (hL.take j') 1
  have T := hJ.commits (hL.take j)
  have T' := hJ'.commits (hL.take j')
  have htr := hi.trip
  have htr' := hi'.trip
  rw [hm, hm'] at hcnt
  change ((X.tr g).take j').countP (commitsTo (Mma.bar L g (.qEmpty 1))) =
    ((X.tr g).take j).countP (commitsTo (Mma.bar L g (.qEmpty 0))) at hcnt
  rw [h0, h1] at hcnt
  obtain ⟨site, i, tt, base, pro⟩ := d
  obtain ⟨site', i', tt', base', pro'⟩ := d'
  simp only at hs hs' hcnt T T' htr htr'
  subst hs hs'
  simp [Mma.TripOk, Mma.region] at htr htr'
  simp [Mma.cnt, Mma.qeA, Mma.Site.after, Mma.Site.loop, Mma.Site.ord, Mma.elCOrd] at hcnt
  subst hcnt
  have htt : tt' = tt := by omega
  subst htt
  simp [Mma.cnt, Mma.comA, Mma.sA, Mma.relA, Mma.qeA, Mma.ofA, Mma.Site.after,
    Mma.Site.inTrip, Mma.Site.loop, Mma.Site.ord, Mma.elCOrd] at T T'
  have hsucc := PTX.Flow.countP_take_succ (p := Mma.isTcCommit) he rfl
  refine ⟨?_, fun k hjk hkj pck spk hk => ?_⟩
  · by_contra hle
    have := PTX.Flow.countP_take_mono Mma.isTcCommit (X.tr g) (Nat.le_of_not_lt hle)
    omega
  · have h2 := PTX.Flow.countP_take_succ (p := Mma.isTcCommit) hk rfl
    have m1 := PTX.Flow.countP_take_mono Mma.isTcCommit (X.tr g) (show j + 1 ≤ k by omega)
    have m2 := PTX.Flow.countP_take_mono Mma.isTcCommit (X.tr g) (show k + 1 ≤ j' by omega)
    omega

/-- **The field `RingFacts.commit`.** -/
theorem RingFacts_commit (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g k pc c : Nat} {b : FBar} {sp : TcCommit.Spec}
    {r : Fin 16} (_ : g < L.threads) (he : X.get (g, k) = some ⟨pc, .tc (.commit sp)⟩)
    (htg : TcCommit.target sp r = some (b.loc L c)) (hring : b.ring) :
    b.isEmpty ∧ warpOf L g = 12 ∧ ctaOf L g % 2 = 0 ∧ LeadAt L X g k ∧
      sp.mbar = b.loc L (ctaOf L g) ∧ sp.clusterBase = ctaOf L g ∧ sp.clusterSize = 2 ∧
      ((X.tr g).take k).countP (commitsTo sp.mbar) + 1 ≤
        okPolls (b.partner.loc L (ctaOf L g)) ((X.tr g).take k) := by
  obtain ⟨hw, -, hlead, hmb⟩ := Mma.commit_fbar hpre hX (mma_commitRun hpre hX ht) he htg
  obtain ⟨-, d, cc, hJ, hi, hs, hsp, hr, -⟩ := commit_state hpre hX ht he
  have hL := (lead_of_site hX hJ (by rw [hs]; rfl)).take k
  have hb := commit_bar hsp hmb
  simp only [Mma.rank] at hr
  have hbase : sp.clusterBase = ctaOf L g ∧ sp.clusterSize = 2 := by
    subst hsp
    refine ⟨?_, rfl⟩
    show g / L.block / 2 * 2 = g / L.block
    omega
  refine ⟨?_, hw, hr, hlead, hmb, hbase.1, hbase.2, ?_⟩
  · subst hb
    fin_cases cc <;> simp_all [Mma.cBar, FBar.ring, FBar.isEmpty]
  rw [hmb]
  change ((X.tr g).take k).countP (commitsTo (Mma.bar L g b)) + 1 ≤
    okPolls (Mma.bar L g b.partner) ((X.tr g).take k)
  have htr := hi.trip
  obtain ⟨site, i, tt, base, pro⟩ := d
  simp only at hs htr hb
  subst hs hb
  simp [Mma.TripOk, Mma.region] at htr
  fin_cases cc <;> simp only [Mma.cBar, FBar.ring, FBar.partner] at hring ⊢
  all_goals try simp at hring
  all_goals first
    | (rw [hJ.qEmpty hL, hJ.qFull]
       simp [Mma.cnt, Mma.qeA, Mma.qA, Mma.Site.after, Mma.Site.ord, Mma.elCOrd])
    | (rw [hJ.kvEmpty hL, hJ.kvFull]
       apply slots_succ_le
       · simp [Mma.cnt, Mma.relA, Mma.kvA, Mma.Site.after, Mma.Site.inTrip, Mma.Site.loop,
           Mma.Site.ord, Mma.elCOrd]
       · simp [Mma.cnt, Mma.relA, Mma.Site.after, Mma.Site.inTrip, Mma.Site.loop, Mma.Site.ord,
           Mma.elCOrd, Mma.slotOf, Mma.kvSlot, Mma.kvUse, Mma.kvBase]
         try ring_nf)

/-- **The field `RouteFacts.mma_commit`.** -/
theorem RouteFacts_mma_commit (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {y : EvId} {s : TcCommit.Spec} {st : Nat}
    (hcm : X.Commit y s) (hst : st < 2)
    (hm : s.mbar = sFullBar L (ctaOf L y.1) st ∨ s.mbar = oFullBar L (ctaOf L y.1) st) :
    y.1 < L.threads ∧ warpOf L y.1 = 12 ∧ leadCta (ctaOf L y.1) = ctaOf L y.1 ∧
      ∃ k pc inst l, k < y.2 ∧ X.Elect (y.1, k) pc fullMask inst l ∧
        (s.mbar = sFullBar L (ctaOf L y.1) st → sCommits L X y.1 st y.2 ≤ pPolls L X y.1 st k ∧
          sCommits L X y.1 st y.2 ≤ p2Polls L X y.1 st k) ∧
        (s.mbar = oFullBar L (ctaOf L y.1) st →
          kvTiles L * (oFullCommits L X y.1 st y.2 + 1) ≤ pPolls L X y.1 st k) := by
  obtain ⟨g, k⟩ := y
  obtain ⟨pc, he⟩ := hcm
  have hg := Frame.lt_of_get hX he
  obtain ⟨hw, d, c, hJ, hi, hs, hsp, hr, -⟩ := commit_state hpre hX ht he
  have hL := (lead_of_site hX hJ (by rw [hs]; rfl)).take k
  obtain ⟨x, inst, hlast, hkx⟩ := hJ.commitElect c hs
  obtain ⟨j, rfl, hj⟩ := getLast_take hlast
    (Nat.le_of_lt (List.getElem?_eq_some_iff.mp he).1)
  have hnw : ∀ l p ok acq sc, x.kind ≠ .wait l p ok acq sc := fun _ _ _ _ _ h => by
    rw [hkx] at h
    cases h
  have hP := okPolls_take_succ (pReadyBar L (ctaOf L g) st) hj hnw
  have hP2 := okPolls_take_succ (pReady2Bar L (ctaOf L g) st) hj hnw
  simp only [Mma.rank] at hr
  refine ⟨hg, hw, by simp only [leadCta, ctaOf] at hr ⊢; omega, j, x.pc, inst, laneOf L g,
    by omega, by
      show (X.tr g)[j]? = _
      rw [show (X.tr g)[j]? = some x from hj]
      obtain ⟨xpc, xk⟩ := x
      simp only at hkx
      rw [hkx]
      rfl,
    ?_, ?_⟩ <;> intro hm' <;>
    simp only [sCommits, pPolls, p2Polls, oFullCommits, ← hP, ← hP2]
  · rw [show sFullBar L (ctaOf L g) st = sFullBar L (ctaOf L g) (⟨st, hst⟩ : Fin 2) from rfl,
      sFullBar_eq] at hm' ⊢
    rw [show pReadyBar L (ctaOf L g) st = pReadyBar L (ctaOf L g) (⟨st, hst⟩ : Fin 2) from rfl,
      pReadyBar_eq,
      show pReady2Bar L (ctaOf L g) st = pReady2Bar L (ctaOf L g) (⟨st, hst⟩ : Fin 2) from rfl,
      pReady2Bar_eq]
    have hb := commit_bar (sp := s) hsp hm'
    change ((X.tr g).take (j + 1)).countP (commitsTo (Mma.bar L g (.sFull ⟨st, hst⟩))) ≤
        okPolls (Mma.bar L g (.pReady ⟨st, hst⟩)) _ ∧
      ((X.tr g).take (j + 1)).countP (commitsTo (Mma.bar L g (.sFull ⟨st, hst⟩))) ≤
        okPolls (Mma.bar L g (.pReady2 ⟨st, hst⟩)) _
    rw [hJ.sFull hL, hJ.pReady, hJ.pReady2]
    have htr := hi.trip
    obtain ⟨site, i, tt, base, pro⟩ := d
    simp only at hs hb htr ⊢
    subst hs
    fin_cases c <;> simp [Mma.cBar] at hb <;> subst hb <;>
      simp [Mma.TripOk, Mma.region] at htr <;>
      simp [Mma.cnt, Mma.sA, Mma.pA, Mma.p2A, Mma.Site.after, Mma.Site.inTrip, Mma.Site.loop,
        Mma.Site.ord, Mma.elCOrd]
  · rw [show oFullBar L (ctaOf L g) st = oFullBar L (ctaOf L g) (⟨st, hst⟩ : Fin 2) from rfl,
      oFullBar_eq] at hm' ⊢
    rw [show pReadyBar L (ctaOf L g) st = pReadyBar L (ctaOf L g) (⟨st, hst⟩ : Fin 2) from rfl,
      pReadyBar_eq]
    have hb := commit_bar (sp := s) hsp hm'
    change kvTiles L * (((X.tr g).take (j + 1)).countP
        (commitsTo (Mma.bar L g (.oFull ⟨st, hst⟩))) + 1) ≤
      okPolls (Mma.bar L g (.pReady ⟨st, hst⟩)) _
    rw [hJ.oFull hL, hJ.pReady]
    have htr := hi.trip
    change Mma.trips L * _ ≤ _
    obtain ⟨site, i, tt, base, pro⟩ := d
    simp only at hs hb htr ⊢
    subst hs
    fin_cases c <;> simp [Mma.cBar] at hb <;> subst hb <;>
      simp [Mma.TripOk, Mma.region] at htr <;>
      simp [Mma.cnt, Mma.ofA, Mma.pA, Mma.Site.after, Mma.Site.inTrip, Mma.Site.loop,
        Mma.Site.ord, Mma.elCOrd] <;> nlinarith

end
end PTX.Kernels.FlashAttn4Fwd.Proof
