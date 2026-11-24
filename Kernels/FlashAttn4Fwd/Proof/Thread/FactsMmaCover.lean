-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsMmaSteps

@[expose] public section

/-! # The MMA blocks before the commits (`CoverFacts`)

A commit is the MMA thread's at a commit site `.commit c` (`mma_commitRun`, `commit_site`), and
the thread led every election of its trace. Its count of earlier MMAs is
`32 n i + 8 B` with `B` the asm blocks of the item before the commit (`mmaA` at the site), so
the thread made every MMA of a smaller number before it (`mma_at_val`):

* the commit to stage `st`'s S-full object after the QK block of score tile `u` (sites 0, 1 of
  the first K, 3, 5 of a trip) follows step 7 of that block (`CoverFacts_qk_sfull`);
* it follows step 7 of the stage's PV block of tile `u - 1`: the loop's PV block of the same
  trip, or the last V's block of the item before (`CoverFacts_pv_sfull`);
* the commit to stage `st`'s O-full object of item `i` (sites 9, 10 after the last V) follows
  step 7 of every PV block of the stage of the items up to `i` (`CoverFacts_pv_ofull`). -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow TcMma

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

/-- **The state of a commit**, with the role's run invariant, the state invariant, and the
thread's elections all returning its lane. -/
theorem commit_st (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g y pc : Nat} {sp : TcCommit.Spec}
    (he : X.get (g, y) = some ⟨pc, .tc (.commit sp)⟩) :
    ∃ (d : Mma.D) (c : Fin 12), Mma.Counts L g d ((X.tr g).take y) ∧ Mma.Inv L g d ∧
      d.site = .commit c ∧ sp = Mma.cSpec L g (Mma.bar L g (Mma.cBar L d c)) ∧
      ElectLead L g (X.tr g) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨-, d, t, ins, o, hJ, hi, h, hc, hf⟩ := mma_commitRun hpre hX ht he
  obtain ⟨c, hs, rfl⟩ := Mma.commit_site hpre hg h hc hf rfl
  refine ⟨d, c, hJ, hi, hs, rfl, ?_⟩
  rcases electLead_or_nonLead hX.elect (electMask_full hX g) with hl | hl
  · exact hl
  · have := (hJ.nonLead (hl.take y)).1
    rw [hs] at this
    cases this

/-- The MMAs before a commit. -/
theorem commit_mmas {g : Nat} {d : Mma.D} {c : Fin 12} {es : List Event}
    (hJ : Mma.Counts L g d es) (hl : ElectLead L g es) (hs : d.site = .commit c) :
    es.countP Mma.isMma =
      32 * Mma.trips L * d.i + Mma.mmaA (.commit c) + 32 * (d.t * (Mma.Site.commit c).loop) := by
  rw [hJ.mmas hl]
  unfold Mma.cnt
  rw [hs]
  ring

/-- **Step 7 of a QK block** before an event that follows more MMAs. -/
theorem qk_block_done (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g y i t : Nat} {b : Fin 8} (hp : Mma.isPv b = false)
    (htr : Mma.TripAt (Mma.trips L) b t)
    (hK : 32 * Mma.trips L * i + 8 * Mma.blk b t + 7 + 1 ≤ ((X.tr g).take y).countP Mma.isMma) :
    ∃ k < y, QkAt X g (Mma.mmaStage b) k ∧
      sCommits L X g (Mma.mmaStage b) k = Mma.trips L * i + Mma.sv (Mma.mmaStage b) b t ∧
      qkStep L X g (Mma.mmaStage b) k = 7 := by
  obtain ⟨k, hk, d, h, hi, htt⟩ := mma_at_val hpre hX ht htr (by decide) hK
  refine ⟨k, hk, (qkAt_iff hpre hX ht (Mma.mmaStage_lt b)).mpr ⟨d, b, _, h, hp, rfl⟩, ?_,
    qkStep_eq hpre hX ht h hp⟩
  rw [h.sCommits, hi, htt]

/-- **Step 7 of a PV block** before an event that follows more MMAs. -/
theorem pv_block_done (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {g y i t : Nat} {b : Fin 8} (hp : Mma.isPv b = true)
    (htr : Mma.TripAt (Mma.trips L) b t)
    (hK : 32 * Mma.trips L * i + 8 * Mma.blk b t + 7 + 1 ≤ ((X.tr g).take y).countP Mma.isMma) :
    ∃ k < y, PvAt X g (Mma.mmaStage b) k ∧
      pPolls L X g (Mma.mmaStage b) k = Mma.trips L * i + (1 + t) ∧
      pvStep L X g (Mma.mmaStage b) k = 7 := by
  obtain ⟨k, hk, d, h, hi, htt⟩ := mma_at_val hpre hX ht htr (by decide) hK
  refine ⟨k, hk, (pvAt_iff hpre hX ht).mpr ⟨d, b, _, h, hp, rfl⟩, ?_,
    pvStep_eq hpre hX ht h hp⟩
  rw [h.pPolls, hi, htt, Mma.pv_own hp]

/-- A commit to stage `st`'s S-full object is at site 0, 1, 3 or 5 of the stage. -/
theorem sfull_site {g st : Nat} {d : Mma.D} {c : Fin 12} (hst : st < 2)
    (hm : (Mma.cSpec L g (Mma.bar L g (Mma.cBar L d c))).mbar = sFullBar L (ctaOf L g) st) :
    (st = 0 ∧ (c = 0 ∨ c = 3)) ∨ (st = 1 ∧ (c = 1 ∨ c = 5)) := by
  rw [show sFullBar L (ctaOf L g) st = FBar.loc L (ctaOf L g) (.sFull ⟨st, hst⟩) from rfl] at hm
  have := (FBar.loc_inj hm).1
  fin_cases c <;> simp [Mma.cBar, Fin.ext_iff] at this <;> simp [this]

/-- A commit to stage `st`'s O-full object is at site 9 or 10. -/
theorem ofull_site {g st : Nat} {d : Mma.D} {c : Fin 12} (hst : st < 2)
    (hm : (Mma.cSpec L g (Mma.bar L g (Mma.cBar L d c))).mbar = oFullBar L (ctaOf L g) st) :
    (st = 0 ∧ c = 9) ∨ (st = 1 ∧ c = 10) := by
  rw [show oFullBar L (ctaOf L g) st = FBar.loc L (ctaOf L g) (.oFull ⟨st, hst⟩) from rfl] at hm
  have := (FBar.loc_inj hm).1
  fin_cases c <;> simp [Mma.cBar, Fin.ext_iff] at this <;> simp [this]

/-- The S-full commits of stage `st` before a commit of the thread. -/
theorem commit_sCommits {g y : Nat} {d : Mma.D} {c : Fin 12} (st : Fin 2)
    (hJ : Mma.Counts L g d ((X.tr g).take y)) (hl : ElectLead L g ((X.tr g).take y))
    (hs : d.site = .commit c) :
    sCommits L X g st y =
      Mma.trips L * d.i + Mma.sA st (.commit c) + d.t * (Mma.Site.commit c).loop := by
  unfold sCommits
  rw [show sFullBar L (ctaOf L g) st = Mma.bar L g (.sFull st) from rfl, hJ.sFull hl st]
  unfold Mma.cnt
  rw [hs]
  ring

/-- **The field `CoverFacts.qk_sfull`.** -/
theorem CoverFacts_qk_sfull (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {y : EvId} {s : TcCommit.Spec} {st : Nat} (hc : X.Commit y s)
    (hst : st < 2) (hm : s.mbar = sFullBar L (ctaOf L y.1) st) :
    ∃ k < y.2, QkAt X y.1 st k ∧ sCommits L X y.1 st k = sCommits L X y.1 st y.2 ∧
      qkStep L X y.1 st k = 7 := by
  obtain ⟨g, y⟩ := y
  obtain ⟨pc, he⟩ := hc
  obtain ⟨d, c, hJ, hinv, hs, rfl, hl⟩ := commit_st hpre hX ht he
  have hM := commit_mmas hJ (hl.take y) hs
  have hS := commit_sCommits ⟨st, hst⟩ hJ (hl.take y) hs
  have htrip := hinv.trip
  unfold Mma.TripOk at htrip
  rw [hs] at htrip
  simp only at hS ⊢
  rw [Nat.mul_assoc] at hM
  rcases sfull_site hst hm with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ <;>
    simp [Mma.region, Mma.mmaA, Mma.sA, Mma.Site.after, Mma.Site.inTrip, Mma.Site.loop,
      Mma.Site.ord, Mma.elCOrd, Mma.blockPos] at htrip hM hS
  · obtain ⟨k, hk, hq, hc, h7⟩ := qk_block_done
      (g := g) (y := y) (b := 0) (i := d.i) (t := 0) hpre hX ht rfl
      (by simp [Mma.TripAt]) (by rw [Nat.mul_assoc]; simp [Mma.blk]; omega)
    exact ⟨k, hk, hq, by simp [Mma.sv, Mma.mmaStage] at hc; omega, h7⟩
  · obtain ⟨k, hk, hq, hc, h7⟩ := qk_block_done
      (g := g) (y := y) (b := 3) (i := d.i) (t := d.t) hpre hX ht rfl
      (by simp [Mma.TripAt]; omega) (by rw [Nat.mul_assoc]; simp [Mma.blk]; omega)
    exact ⟨k, hk, hq, by simp [Mma.sv, Mma.mmaStage] at hc; omega, h7⟩
  · obtain ⟨k, hk, hq, hc, h7⟩ := qk_block_done
      (g := g) (y := y) (b := 1) (i := d.i) (t := 0) hpre hX ht rfl
      (by simp [Mma.TripAt]) (by rw [Nat.mul_assoc]; simp [Mma.blk]; omega)
    exact ⟨k, hk, hq, by simp [Mma.sv, Mma.mmaStage] at hc; omega, h7⟩
  · obtain ⟨k, hk, hq, hc, h7⟩ := qk_block_done
      (g := g) (y := y) (b := 5) (i := d.i) (t := d.t) hpre hX ht rfl
      (by simp [Mma.TripAt]; omega) (by rw [Nat.mul_assoc]; simp [Mma.blk]; omega)
    exact ⟨k, hk, hq, by simp [Mma.sv, Mma.mmaStage] at hc; omega, h7⟩

/-- The O-full commits of stage `st` before a commit of the thread. -/
theorem commit_oFull {g y : Nat} {d : Mma.D} {c : Fin 12} (st : Fin 2)
    (hJ : Mma.Counts L g d ((X.tr g).take y)) (hl : ElectLead L g ((X.tr g).take y))
    (hs : d.site = .commit c) :
    oFullCommits L X g st y = d.i + Mma.ofA st (.commit c) := by
  unfold oFullCommits
  rw [show oFullBar L (ctaOf L g) st = Mma.bar L g (.oFull st) from rfl, hJ.oFull hl st]
  unfold Mma.cnt
  rw [hs]
  ring

/-- **The field `CoverFacts.pv_sfull`.** -/
theorem CoverFacts_pv_sfull (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {y : EvId} {s : TcCommit.Spec} {st : Nat} (hc : X.Commit y s)
    (hst : st < 2) (hm : s.mbar = sFullBar L (ctaOf L y.1) st)
    (h1 : 1 ≤ sCommits L X y.1 st y.2) :
    ∃ k < y.2, PvAt X y.1 st k ∧ pPolls L X y.1 st k = sCommits L X y.1 st y.2 ∧
      pvStep L X y.1 st k = 7 := by
  obtain ⟨g, y⟩ := y
  obtain ⟨pc, he⟩ := hc
  obtain ⟨d, c, hJ, hinv, hs, rfl, hl⟩ := commit_st hpre hX ht he
  have hn := trips_pos hpre
  have hM := commit_mmas hJ (hl.take y) hs
  have hS := commit_sCommits ⟨st, hst⟩ hJ (hl.take y) hs
  have htrip := hinv.trip
  unfold Mma.TripOk at htrip
  rw [hs] at htrip
  simp only at hS h1 ⊢
  rw [Nat.mul_assoc] at hM
  rcases sfull_site hst hm with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ <;>
    simp [Mma.region, Mma.mmaA, Mma.sA, Mma.Site.after, Mma.Site.inTrip, Mma.Site.loop,
      Mma.Site.ord,
      Mma.elCOrd, Mma.blockPos] at htrip hM hS <;> rw [hS] at h1 ⊢
  · -- the last V's PV block of stage 0 of the item before
    obtain ⟨i', hi'⟩ : ∃ i', d.i = i' + 1 := ⟨d.i - 1, by
      rcases Nat.eq_zero_or_pos d.i with h0 | h0
      · rw [h0] at h1; simp at h1
      · omega⟩
    have e1 : Mma.trips L * d.i = Mma.trips L * i' + Mma.trips L := by
      rw [hi', Nat.mul_add, Nat.mul_one]
    obtain ⟨k, hk, hq, hc, h7⟩ := pv_block_done
      (g := g) (y := y) (b := 6) (i := i') (t := Mma.trips L - 1)
      hpre hX ht rfl (by simp [Mma.TripAt]; omega)
      (by rw [Nat.mul_assoc]; simp [Mma.blk]; omega)
    exact ⟨k, hk, hq, by simp [Mma.mmaStage] at hc; omega, h7⟩
  · obtain ⟨k, hk, hq, hc, h7⟩ := pv_block_done
      (g := g) (y := y) (b := 2) (i := d.i) (t := d.t) hpre hX ht rfl
      (by simp [Mma.TripAt]; omega) (by rw [Nat.mul_assoc]; simp [Mma.blk]; omega)
    exact ⟨k, hk, hq, by simp [Mma.mmaStage] at hc; omega, h7⟩
  · obtain ⟨i', hi'⟩ : ∃ i', d.i = i' + 1 := ⟨d.i - 1, by
      rcases Nat.eq_zero_or_pos d.i with h0 | h0
      · rw [h0] at h1; simp at h1
      · omega⟩
    have e1 : Mma.trips L * d.i = Mma.trips L * i' + Mma.trips L := by
      rw [hi', Nat.mul_add, Nat.mul_one]
    obtain ⟨k, hk, hq, hc, h7⟩ := pv_block_done
      (g := g) (y := y) (b := 7) (i := i') (t := Mma.trips L - 1)
      hpre hX ht rfl (by simp [Mma.TripAt]; omega)
      (by rw [Nat.mul_assoc]; simp [Mma.blk]; omega)
    exact ⟨k, hk, hq, by simp [Mma.mmaStage] at hc; omega, h7⟩
  · obtain ⟨k, hk, hq, hc, h7⟩ := pv_block_done
      (g := g) (y := y) (b := 4) (i := d.i) (t := d.t) hpre hX ht rfl
      (by simp [Mma.TripAt]; omega) (by rw [Nat.mul_assoc]; simp [Mma.blk]; omega)
    exact ⟨k, hk, hq, by simp [Mma.mmaStage] at hc; omega, h7⟩

/-- **The field `CoverFacts.pv_ofull`.** -/
theorem CoverFacts_pv_ofull (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) {y : EvId} {s : TcCommit.Spec} {st v : Nat}
    (hc : X.Commit y s) (hst : st < 2) (hm : s.mbar = oFullBar L (ctaOf L y.1) st) (hv1 : 1 ≤ v)
    (hv : v ≤ kvTiles L * (oFullCommits L X y.1 st y.2 + 1)) :
    ∃ k < y.2, PvAt X y.1 st k ∧ pPolls L X y.1 st k = v ∧ pvStep L X y.1 st k = 7 := by
  obtain ⟨g, y⟩ := y
  obtain ⟨pc, he⟩ := hc
  obtain ⟨d, c, hJ, hinv, hs, rfl, hl⟩ := commit_st hpre hX ht he
  have hn := trips_pos hpre
  have hM := commit_mmas hJ (hl.take y) hs
  have hO := commit_oFull ⟨st, hst⟩ hJ (hl.take y) hs
  have htrip := hinv.trip
  unfold Mma.TripOk at htrip
  rw [hs] at htrip
  simp only at hO hv ⊢
  rw [Nat.mul_assoc] at hM
  rw [show kvTiles L = Mma.trips L from rfl] at hv
  -- tile `v - 1`: item `a`, trip `u`
  obtain ⟨a, u, hu, hw⟩ : ∃ a u, u < Mma.trips L ∧ v - 1 = Mma.trips L * a + u :=
    ⟨(v - 1) / Mma.trips L, (v - 1) % Mma.trips L, Nat.mod_lt _ (by omega),
      (Nat.div_add_mod _ _).symm⟩
  rcases ofull_site hst hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [Mma.region, Mma.mmaA, Mma.ofA, Mma.Site.after, Mma.Site.inTrip, Mma.Site.loop,
      Mma.Site.ord, Mma.elCOrd, Mma.blockPos] at htrip hM hO <;> rw [hO] at hv
  all_goals
    rw [Nat.mul_add, Nat.mul_one] at hv
    have hai : a ≤ d.i := by
      by_contra hlt
      have : Mma.trips L * (d.i + 1) ≤ Mma.trips L * a := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_add, Nat.mul_one] at this
      omega
    have hmul : Mma.trips L * a ≤ Mma.trips L * d.i := Nat.mul_le_mul_left _ hai
  · by_cases hl1 : u + 1 < Mma.trips L
    · obtain ⟨k, hk, hq, hc, h7⟩ := pv_block_done
        (g := g) (y := y) (b := 2) (i := a) (t := u) hpre hX ht rfl
        (by simp [Mma.TripAt]; omega) (by rw [Nat.mul_assoc]; simp [Mma.blk]; omega)
      exact ⟨k, hk, hq, by simp [Mma.mmaStage] at hc; omega, h7⟩
    · obtain ⟨k, hk, hq, hc, h7⟩ := pv_block_done
        (g := g) (y := y) (b := 6) (i := a) (t := u) hpre hX ht rfl
        (by simp [Mma.TripAt]; omega) (by rw [Nat.mul_assoc]; simp [Mma.blk]; omega)
      exact ⟨k, hk, hq, by simp [Mma.mmaStage] at hc; omega, h7⟩
  · by_cases hl1 : u + 1 < Mma.trips L
    · obtain ⟨k, hk, hq, hc, h7⟩ := pv_block_done
        (g := g) (y := y) (b := 4) (i := a) (t := u) hpre hX ht rfl
        (by simp [Mma.TripAt]; omega) (by rw [Nat.mul_assoc]; simp [Mma.blk]; omega)
      exact ⟨k, hk, hq, by simp [Mma.mmaStage] at hc; omega, h7⟩
    · obtain ⟨k, hk, hq, hc, h7⟩ := pv_block_done
        (g := g) (y := y) (b := 7) (i := a) (t := u) hpre hX ht rfl
        (by simp [Mma.TripAt]; omega) (by rw [Nat.mul_assoc]; simp [Mma.blk]; omega)
      exact ⟨k, hk, hq, by simp [Mma.mmaStage] at hc; omega, h7⟩

/-- **The thread layer's facts for the coverage of the Tensor Memory loads.** -/
theorem coverFacts (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
    (ht : Frame.Tracked (code L) X) : CoverFacts L X where
  qk_sfull := CoverFacts_qk_sfull hpre hX ht
  pv_sfull := CoverFacts_pv_sfull hpre hX ht
  pv_ofull := CoverFacts_pv_ofull hpre hX ht

end
end PTX.Kernels.FlashAttn4Fwd.Proof
