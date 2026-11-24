-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLagsOutput
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.OFull
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.SFull
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.Handshake

@[expose] public section

/-! # Producer lag of the MMA warp (`OFullPollFacts.lag`, `SFullPollFacts.lag`,
`HandshakePollFacts.lag`)

An MMA state of an item is in band M of a slot of its item: slot 0 before the trip loop, slot
`t + 1` in trip `t`, slot `n` after it (`mma_item`); its position in the item (`Site.ord`) is
below 100, in `[100, 200)` and from 200 on in these three parts (`region_ord`). Before the items
its time is fixed; after them (the exit stage, in the tail) the leader CTA's lane has done every
item of the cluster (`Mma.Counts.done`).

* **O full.** A correction thread at `oWait st` of item `i` has made `i` successful polls of the
  O-full object (`Correction.Counts.oFull`). A self-elected lane of the pair leader's MMA warp
  with at most `i` O-full commits of the stage (`Mma.Counts.oFull`: `i' + ofA`) is in an item no
  later than `i`, in band M, before the poll in band C of slot `n` of item `i`.
* **S full.** A softmax thread at `sW` of item `i` in slot `s` (`0`, or `t + 1` in trip `t`) has
  made `n i + s` successful polls (`Softmax.Counts.score`). A self-elected MMA lane with at most
  as many S-full commits of the stage (`n i' + sA + t'` in or after the loop) is in an earlier
  item, or in item `i` in band M of slot at most `s`: each trip's commit follows its part's
  first site (`mma_sfull_lt`).
* **Handshake.** The other CTA's MMA lane with no arrival on the waiter's handshake barrier
  (`Mma.Counts.handoff`) is before its `arrivePeer`, in an item of the cluster or the exit
  stage's first sites, before the waiter's `waitDealloc`. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow Progress

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace Lag

/-- Two threads of one cluster have its items. -/
theorem T_eq_of_pair (hpre : Pre P L mem0) {y g : Nat} (h : ctaOf L y / 2 = ctaOf L g / 2) :
    Work.T L y = Work.T L g := by
  simp only [Work.T, Work.cid]
  rw [clusterOf_eq hpre, clusterOf_eq hpre, h]

/-- Every election of a self-elected thread's trace prefix returned its lane. -/
theorem electLead_of_self {y : Nat} (hse : SelfElected L X y) (k : Nat) :
    ElectLead L y ((X.tr y).take k) := by
  intro e he mask inst ld hk
  obtain ⟨j, hj, hje⟩ := List.getElem_of_mem (List.mem_of_mem_take he)
  obtain ⟨pc, kind⟩ := e
  simp only at hk
  subst hk
  exact hse j pc mask inst ld (by
    show (X.tr y)[j]? = _
    rw [List.getElem?_eq_getElem hj, hje])

theorem mmaOff_lt (s : Mma.Site) : Time.mmaOff s < 100 := by
  cases s with
  | qWait k => revert k; decide
  | kvWait k => revert k; decide
  | pWait k => revert k; decide
  | p2Wait k b => revert k b; decide
  | shfl k => revert k; decide
  | elM b => revert b; decide
  | mma b j => revert b j; decide
  | elC c => revert c; decide
  | commit c => revert c; decide
  | _ => decide

/-- The part of the item of an item site, and its position in the item. -/
theorem region_ord (s : Mma.Site) (h : s.phase = 1) :
    (Mma.region s = 1 ∧ 1 ≤ s.ord ∧ s.ord < 100) ∨
      (Mma.region s = 2 ∧ 100 ≤ s.ord ∧ s.ord < 200) ∨ (Mma.region s = 3 ∧ 200 ≤ s.ord) := by
  cases s with
  | qWait k => revert k; decide
  | kvWait k => revert k; decide
  | pWait k => revert k; decide
  | p2Wait k b => revert k b; decide
  | shfl k => revert k; decide
  | elM b => revert b; decide
  | mma b j => revert b j; decide
  | elC c => revert c; decide
  | commit c => revert c; decide
  | _ => simp [Mma.Site.phase] at h

/-- A site outside the items has position 0, and is one of the item sites otherwise. -/
theorem ord_of_phase (s : Mma.Site) (h : s.phase ≠ 1) : s.ord = 0 := by
  cases s <;> simp_all [Mma.Site.phase, Mma.Site.ord]

theorem itemSite_of_phase (s : Mma.Site) (h : s.phase = 1) : Mma.ItemSite s := by
  cases s <;> simp_all [Mma.Site.phase, Mma.ItemSite]

theorem phase_cases (s : Mma.Site) : s.phase = 0 ∨ s.phase = 1 ∨ s.phase = 2 := by
  cases s <;> simp [Mma.Site.phase]

/-- An MMA site before the items is at a fixed time. -/
theorem mma_fixed (n T : Nat) (c : Mma.D) (h : c.site.phase = 0) :
    Time.mma n T c ≤ Time.base := by
  obtain ⟨site, i, t, b, p⟩ := c
  cases site <;> simp_all [Mma.Site.phase, Time.mma, Time.regT, Time.allocT, Time.allocWriteT,
    Time.bar0T, Time.ldBaseT, Time.shflQT, Time.base]

/-- The time of an item site: band M of slot 0, `t + 1` or `n` by its part. -/
theorem mma_time (n T : Nat) (c : Mma.D) (h : c.site.phase = 1) :
    Time.mma n T c = Time.mmaAt n c.i
      (if Mma.region c.site = 1 then 0 else if Mma.region c.site = 2 then c.t + 1 else n)
      (Time.mmaOff c.site) := by
  obtain ⟨site, i, t, b, p⟩ := c
  cases site <;> (try simp [Mma.Site.phase] at h) <;> simp only [Time.mma] <;> split_ifs <;> rfl

/-- **An MMA state of an item** is in band M of slot `0`, `t + 1` or `n` of its item, by the
part of the item its position is in. -/
theorem mma_item {y : Nat} (T : Nat) {c : Mma.D} (hinv : Mma.Inv L y c) (h : c.site.phase = 1) :
    ∃ s o, Time.mma (Work.n L) T c = Time.slotTime (Work.n L) c.i s (Time.bandM + o) ∧
      o < 100 ∧ ((s = 0 ∧ 1 ≤ c.site.ord ∧ c.site.ord < 100) ∨
        (s = c.t + 1 ∧ 100 ≤ c.site.ord ∧ c.site.ord < 200 ∧ c.t + 1 < Work.n L) ∨
        (s = Work.n L ∧ 200 ≤ c.site.ord ∧ c.t + 1 = Work.n L)) := by
  have hn : Mma.trips L = Work.n L := rfl
  rw [mma_time _ _ c h]
  have htrip := hinv.trip
  unfold Mma.TripOk at htrip
  rw [hn] at htrip
  rcases region_ord c.site h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩ <;>
    simp only [h1] at htrip ⊢ <;> simp only [Nat.reduceEqDiff, ↓reduceIte]
  · exact ⟨0, _, rfl, mmaOff_lt _, .inl ⟨rfl, h2, h3⟩⟩
  · exact ⟨c.t + 1, _, rfl, mmaOff_lt _, .inr (.inl ⟨rfl, h2, h3, htrip⟩)⟩
  · exact ⟨Work.n L, _, rfl, mmaOff_lt _, .inr (.inr ⟨rfl, h2, htrip⟩)⟩

/-- An MMA state after the items, of the leader CTA, has done every item of the cluster. -/
theorem mma_done (hpre : Pre P L mem0) {y : Nat} {c : Mma.D} {es : List Event}
    (hJ : Mma.Counts L y c es) (hrank : Mma.rank L y = 0) (h : c.site.phase = 2) :
    Work.T L y ≤ c.i := by
  have h1 := hJ.done h hrank
  by_contra hc
  have := (Work.mma_work_lt (g := y) (i := c.i) hpre).mpr (by omega)
  omega

/-- **A self-elected MMA state with at most `i` O-full commits of stage `k`**, `i` an item of
the cluster, is before band C of slot `n` of item `i`, and not at its exit. -/
theorem mma_ofull_lt (hpre : Pre P L mem0) {y : Nat} {c : Mma.D} {es : List Event}
    (hJ : Mma.Counts L y c es) (hinv : Mma.Inv L y c) (hel : ElectLead L y es)
    (hrank : Mma.rank L y = 0) {k : Fin 2} {i o : Nat} (hiT : i < Work.T L y) (ho : 300 ≤ o)
    (hc : es.countP (commitsTo (Mma.bar L y (.oFull k))) < i + 1) :
    Time.mma (Work.n L) (Work.T L y) c + 1 < Time.slotTime (Work.n L) i (Work.n L) o ∧
      c.site ≠ .exit := by
  have h := hJ.oFull hel k
  rw [h] at hc
  simp only [Mma.cnt, Nat.zero_mul, Nat.zero_add, Nat.one_mul] at hc
  rcases phase_cases c.site with h0 | h1 | h2
  · refine ⟨?_, fun he => by rw [he] at h0; simp [Mma.Site.phase] at h0⟩
    have h1 := mma_fixed (Work.n L) (Work.T L y) c h0
    have h2 : Time.base + 2 ≤ Time.slotTime (Work.n L) i (Work.n L) o :=
      le_slotTime_of (by simp only [Time.base]; omega)
    omega
  · obtain ⟨s, o', ht, ho', hcase⟩ := mma_item (Work.T L y) hinv h1
    refine ⟨?_, fun he => by rw [he] at h1; simp [Mma.Site.phase] at h1⟩
    rw [ht]
    refine slotTime_lt ?_ ?_ ?_ <;> (try simp only [Time.bandM, Time.span]) <;> omega
  · exfalso
    have := mma_done hpre hJ hrank h2
    have h0 := ord_of_phase c.site (by omega)
    simp only [Mma.ofA, Mma.Site.after, h0, Nat.not_lt_zero, ↓reduceIte] at hc
    omega

/-- **A self-elected MMA state with at most `n i + s` S-full commits of stage `k`** (`s < n`), `i`
an item of the cluster, is before band S of slot `s` of item `i`, and not at its exit. -/
theorem mma_sfull_lt (hpre : Pre P L mem0) {y : Nat} {c : Mma.D} {es : List Event}
    (hJ : Mma.Counts L y c es) (hinv : Mma.Inv L y c) (hel : ElectLead L y es)
    (hrank : Mma.rank L y = 0) {k : Fin 2} {i s o : Nat} (hiT : i < Work.T L y)
    (hs : s + 1 ≤ Work.n L) (ho : 300 ≤ o)
    (hc : es.countP (commitsTo (Mma.bar L y (.sFull k))) < Work.n L * i + s + 1) :
    Time.mma (Work.n L) (Work.T L y) c + 1 < Time.slotTime (Work.n L) i s o ∧
      c.site ≠ .exit := by
  have hn : Mma.trips L = Work.n L := rfl
  have h := hJ.sFull hel k
  rw [h] at hc
  simp only [Mma.cnt, Nat.one_mul, Nat.add_zero, hn] at hc
  have hlt := mul_add_lt (m := Work.n L) (a := c.i) (b := i)
    (x := Mma.sA k c.site + c.t * c.site.loop) (y := s + 1) hs (by omega)
  have hk := k.isLt
  rcases phase_cases c.site with h0 | h1 | h2
  · refine ⟨?_, fun he => by rw [he] at h0; simp [Mma.Site.phase] at h0⟩
    have h1 := mma_fixed (Work.n L) (Work.T L y) c h0
    have h2 : Time.base + 2 ≤ Time.slotTime (Work.n L) i s o :=
      le_slotTime_of (by simp only [Time.base]; omega)
    omega
  · obtain ⟨s', o', ht, ho', hcase⟩ := mma_item (Work.T L y) hinv h1
    refine ⟨?_, fun he => by rw [he] at h1; simp [Mma.Site.phase] at h1⟩
    rw [ht]
    simp only [Mma.sA, Mma.Site.after, Mma.Site.inTrip, Mma.Site.loop] at hlt
    refine slotTime_lt ?_ ?_ ?_ <;> (try simp only [Time.bandM, Time.span]) <;>
      split_ifs at hlt <;> omega
  · exfalso
    have := mma_done hpre hJ hrank h2
    omega

/-- **An MMA state with no arrival on its peer's handshake barrier** is before the
`waitDealloc` of the cluster's tail, and not at its exit. -/
theorem mma_hand_lt (hpre : Pre P L mem0) {y : Nat} {c : Mma.D} {es : List Event}
    (hJ : Mma.Counts L y c es) (hinv : Mma.Inv L y c)
    (hc : arrivals (FBar.loc L (Mma.peer L y) .dealloc) es = 0) :
    Time.mma (Work.n L) (Work.T L y) c + 1 < Time.mmaTail (Work.n L) (Work.T L y) 20 ∧
      c.site ≠ .exit := by
  rw [hJ.handoff] at hc
  rcases phase_cases c.site with h0 | h1 | h2
  · refine ⟨?_, fun he => by rw [he] at h0; simp [Mma.Site.phase] at h0⟩
    have h1 := mma_fixed (Work.n L) (Work.T L y) c h0
    have h2 : Time.base + 2 ≤ Time.mmaTail (Work.n L) (Work.T L y) 20 :=
      le_slotTime_of (by simp only [Time.base]; omega)
    omega
  · obtain ⟨s', o', ht, ho', hcase⟩ := mma_item (Work.T L y) hinv h1
    refine ⟨?_, fun he => by rw [he] at h1; simp [Mma.Site.phase] at h1⟩
    rw [ht]
    have hi := (Work.mma_work_lt hpre).mp (hinv.i (itemSite_of_phase _ h1)).1
    unfold Time.mmaTail Time.tailTime
    refine slotTime_lt ?_ ?_ (.inl hi) <;> (try simp only [Time.bandM, Time.span]) <;> omega
  · obtain ⟨site, i, t, b, p⟩ := c
    simp only at h2 hc ⊢
    cases site <;> simp [Mma.Site.phase, Mma.handoffA] at h2 hc <;>
      simp [Time.mma, Time.mmaTail, Time.tailTime, Time.slotTime]

/-- The rank of a thread of a pair-leader CTA. -/
theorem rank_lead {y g : Nat} (h : ctaOf L y = leadCta (ctaOf L g)) : Mma.rank L y = 0 := by
  have h' : y / L.block = ctaOf L g / 2 * 2 := h
  simp only [Mma.rank, h']
  omega

end Lag

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

open Lag in
/-- **The field `OFullPollFacts.lag`**. -/
theorem OFullPollFacts_lag :
    ∀ {g y : Nat} {d : Correction.D} {st : Fin 2}, g < L.threads →
    St L X g (X.tr g).length = some (some (.inr (.corr d))) → d.site = .oWait st →
    y < L.threads → warpOf L y = 12 → ctaOf L y = leadCta (ctaOf L g) → SelfElected L X y →
    (X.tr y).countP (commitsTo (oFullBar L (ctaOf L y) st)) ≤
      okPolls (oFullBar L (ctaOf L g) st) (X.tr g) →
      Lags L X y g (.inr (.corr d)) := by
  intro g y d st hg hσ hs hy hw hcta hse hle hub
  obtain ⟨hJ, hinv⟩ := end_state hpre hX ht hub hg hσ
  change Correction.Counts L g d (X.tr g) at hJ
  change Correction.Inv L g d at hinv
  have hp := hJ.oFull st.val st.isLt
  have hloc : Correction.ownLoc L g (192 + 8 * st.val) = oFullBar L (ctaOf L g) st := by
    simp [Correction.ownLoc, oFullBar, Correction.sb]
  have hop : Correction.oPos st.val d = 0 := by
    rw [Correction.oPos, hs]; rcases Store.fin2_cases st with rfl | rfl <;> rfl
  rw [hloc, hop, Nat.add_zero] at hp
  have hi : d.i < Work.T L g := hinv.item (by rw [hs]; rfl)
  have hT : Work.T L y = Work.T L g :=
    T_eq_of_pair hpre (by rw [hcta]; simp only [leadCta]; omega)
  have hW : stateTime L g (.inr (.corr d)) =
      Time.slotTime (Work.n L) d.i (Work.n L) (Time.bandC st.val + 8) := by
    obtain ⟨site, i, t, aw, a⟩ := d
    simp only at hs
    subst hs
    rfl
  have hW0 : Time.base + 2 ≤ stateTime L g (.inr (.corr d)) := by
    rw [hW]; exact le_slotTime_of (by simp only [Time.bandC, Time.base]; omega)
  refine lags_mma hpre hX ht hub hy hw (commitsTo (oFullBar L (ctaOf L y) st)) (d.i + 1)
    (stateTime L g (.inr (.corr d)) - 2) (by omega) (fun c es hk0 hJc hinvc hcnt => ?_)
    (by omega) (by omega)
  obtain ⟨k, rfl⟩ := hk0
  obtain ⟨h1, h2⟩ := mma_ofull_lt hpre hJc hinvc (electLead_of_self hse k) (rank_lead hcta)
    (k := st) (o := Time.bandC st.val + 8) (by rw [hT]; exact hi)
    (by simp only [Time.bandC]; omega) hcnt
  rw [hW, hT] at *
  exact ⟨by omega, h2⟩

open Lag in
/-- **The field `SFullPollFacts.lag`**. -/
theorem SFullPollFacts_lag :
    ∀ {g y : Nat} {d : Softmax.D} {lp : Bool}, g < L.threads →
    St L X g (X.tr g).length = some (some (.inr (.softmax d))) → d.site = .sW lp →
    y < L.threads → warpOf L y = 12 → ctaOf L y = leadCta (ctaOf L g) → SelfElected L X y →
    (X.tr y).countP (commitsTo (sFullBar L (ctaOf L y) (warpOf L g / 4))) ≤
      okPolls (sFullBar L (ctaOf L g) (warpOf L g / 4)) (X.tr g) →
      Lags L X y g (.inr (.softmax d)) := by
  intro g y d lp hg hσ hs hy hw hcta hse hle hub
  obtain ⟨hJ, hinv⟩ := end_state hpre hX ht hub hg hσ
  change Softmax.Counts L g d (X.tr g) at hJ
  change Softmax.Inv L g d at hinv
  have hst : warpOf L g / 4 < 2 := by have := hinv.warp; omega
  have hn : Softmax.trips L = Work.n L := rfl
  have hn1 := n_pos hpre
  have hp := hJ.score
  have hloc : Softmax.ownLoc L g (128 + 8 * Softmax.stOf L g) =
      sFullBar L (ctaOf L g) (warpOf L g / 4) := by
    simp [Softmax.ownLoc, sFullBar, Softmax.sb]
  rw [hloc, hn] at hp
  have hi : d.i < Work.T L g := hinv.item (by rw [hs]; rfl)
  have hT : Work.T L y = Work.T L g :=
    T_eq_of_pair hpre (by rw [hcta]; simp only [leadCta]; omega)
  -- the waiter's slot `s`: `n i + s` successful polls, its poll at band S of slot `s`
  obtain ⟨s, hs1, hps, hW⟩ : ∃ s, s + 1 ≤ Work.n L ∧
      okPolls (sFullBar L (ctaOf L g) (warpOf L g / 4)) (X.tr g) = Work.n L * d.i + s ∧
      stateTime L g (.inr (.softmax d)) =
        Time.slotTime (Work.n L) d.i s (Time.bandS (warpOf L g / 4) + 2) := by
    have htrip := hinv.trip
    rw [hn] at htrip
    obtain ⟨site, i, t⟩ := d
    simp only at hs htrip hp ⊢
    subst hs
    cases lp
    · exact ⟨0, hn1, by rw [hp]; simp [Softmax.sPos, Softmax.Site.tile0Ld, Softmax.Site.inTrip],
        rfl⟩
    · refine ⟨t + 1, by have := htrip rfl; omega, ?_, rfl⟩
      rw [hp]; simp only [Softmax.sPos]; omega
  have hW0 : Time.base + 2 ≤ stateTime L g (.inr (.softmax d)) := by
    rw [hW]; exact le_slotTime_of (by simp only [Time.bandS, Time.base]; omega)
  refine lags_mma hpre hX ht hub hy hw
    (commitsTo (sFullBar L (ctaOf L y) (warpOf L g / 4))) (Work.n L * d.i + s + 1)
    (stateTime L g (.inr (.softmax d)) - 2) (by omega) (fun c es hk0 hJc hinvc hcnt => ?_)
    (by omega) (by omega)
  obtain ⟨k, rfl⟩ := hk0
  obtain ⟨h1, h2⟩ := mma_sfull_lt hpre hJc hinvc (electLead_of_self hse k) (rank_lead hcta)
    (k := ⟨warpOf L g / 4, hst⟩) (o := Time.bandS (warpOf L g / 4) + 2)
    (by rw [hT]; exact hi) hs1 (by simp only [Time.bandS]; omega) hcnt
  rw [hW, hT] at *
  exact ⟨by omega, h2⟩

open Lag in
/-- **The field `HandshakePollFacts.lag`**. -/
theorem HandshakePollFacts_lag :
    ∀ {g y : Nat} {d : Mma.D}, g < L.threads → y < L.threads →
    ctaOf L y = pairCta (ctaOf L g) → warpOf L y = 12 →
    St L X g (X.tr g).length = some (some (.inr (.mma d))) → d.site = .waitDealloc →
    arrivals (FBar.loc L (ctaOf L g) .dealloc) (X.tr y) = 0 →
      Lags L X y g (.inr (.mma d)) := by
  intro g y d hg hy hcta hw hσ hs h0 hub
  have hT : Work.T L y = Work.T L g :=
    T_eq_of_pair hpre (by rw [hcta]; simp only [pairCta]; omega)
  have hpeer : Mma.peer L y = ctaOf L g := by
    have h' : y / L.block = ctaOf L g / 2 * 2 + (1 - ctaOf L g % 2) := hcta
    simp only [Mma.peer, Mma.rank, clusterOf_eq hpre, ctaOf, h']
    simp only [ctaOf] at h'
    omega
  have hW : stateTime L g (.inr (.mma d)) = Time.mmaTail (Work.n L) (Work.T L g) 20 := by
    obtain ⟨site, i, t, b, p⟩ := d
    simp only at hs
    subst hs
    rfl
  have hW0 : Time.base + 2 ≤ stateTime L g (.inr (.mma d)) := by
    rw [hW]; exact le_slotTime_of (by simp only [Time.base]; omega)
  refine lags_mma hpre hX ht hub hy hw (arrivesOn (FBar.loc L (ctaOf L g) .dealloc)) 1
    (stateTime L g (.inr (.mma d)) - 2) (by omega) (fun c es _ hJc hinvc hcnt => ?_)
    (by change arrivals _ _ < 1; omega) (by omega)
  have hc : arrivals (FBar.loc L (Mma.peer L y) .dealloc) es = 0 := by
    rw [hpeer]; change es.countP _ = 0; omega
  obtain ⟨h1, h2⟩ := mma_hand_lt hpre hJc hinvc hc
  rw [hW, ← hT]
  exact ⟨by omega, h2⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof
