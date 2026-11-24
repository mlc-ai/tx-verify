-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLagsMma
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.MmaRing

@[expose] public section

/-! # Producer lag at the MMA warp's ring polls (`MmaRingPollFacts.arrive`, `copies`)

An MMA thread at `qWait k` of item `i` has made `i` successful polls of Q stage `k`'s full
barrier and polls in band M of slot 0; at `kvWait k` of trip `t` it polls the full barrier of the
slot of ring use `U = 2 n i + u` (`u = kvU k t`, `u < 2 n`), has made as many successful polls of
it as the ring uses below `U` on that slot (`slotCount U (U % 6)`), and polls in band M of slot
`(u + 1) / 2` (`mma_ring`).

A self-elected loader lane counts, per slot, its arrivals and copies of the ring uses below
`kvArrived` and `kvDone` (`Loader.Ledger`: `kvArr`, `kvIss`), and per Q stage `qArrived` and
`qIssued`. A lane with no more arrivals (fewer copies) on the polled slot than the waiter's polls
(times the copies per use, plus one use) has `kvArrived ≤ U` (`kvDone ≤ U`): the slot counts of
`U` and `U + 1` differ by one. A loader state of an item is in band L of slot `s` with
`2 n i' + 2 s` at most each of these counts (`loader_shape`), so such a state is in an earlier
item, or in item `i` in a slot at most `u / 2`, before the poll in band M of slot `(u + 1) / 2`
(`loader_kv_lt`). For Q stage `k` the lane has `qArrived ≤ i` (`qIssued < 2 (i + 1)`), so it is
in an earlier item or in slot 0 of item `i` (`loader_q_lt`). After the items each count is that
of all the cluster's items, above the waiter's. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow Progress

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace Lag

theorem uB_step {i j : Nat} (h : i < j) : Loader.uB L i + 2 * Work.n L ≤ Loader.uB L j := by
  unfold Loader.uB
  have := Nat.mul_le_mul_left (2 * Work.n L) h
  rw [Nat.mul_succ] at this
  exact this

theorem kvUse_eq (i u : Nat) : Mma.kvUse L i u = Loader.uB L i + u := rfl

/-- **A loader state of an item** is in band L of slot `s` of its item (`s < n`), and its counts
of KV arrivals and completed KV uses are at least `2 n i + 2 s`; in a trip's slot (`s > 0`) it
has made both Q stages' arrivals and copies of its item. -/
theorem loader_shape {y : Nat} (T : Nat) {c : Loader.D} (hinv : Loader.Inv L y c)
    (hn1 : 1 ≤ Work.n L) (h : c.site.inItem = true) :
    ∃ s o, Time.loader (Work.n L) T c = Time.slotTime (Work.n L) c.i s o ∧ o < 64 ∧
      s + 1 ≤ Work.n L ∧ Loader.uB L c.i + 2 * s ≤ Loader.kvArrived L y c ∧
      Loader.uB L c.i + 2 * s ≤ Loader.kvDone L y c ∧
      ∀ st, c.i ≤ Loader.qArrived L y c st ∧ 2 * c.i ≤ Loader.qIssued L y c st ∧
        (0 < s → Loader.qArrived L y c st = c.i + 1 ∧ Loader.qIssued L y c st = 2 * c.i + 2) := by
  obtain ⟨site, i, t, s, ph, qp⟩ := c
  have htrip := hinv.trip
  simp only at htrip h ⊢
  rcases site with _ | _ | u | u | u | ⟨u, j⟩ | ⟨u, j⟩ | k | _ | _ | _ | _ <;>
    simp only [Loader.Site.inItem, Bool.false_eq_true] at h
  all_goals (try cases u)
  all_goals (try rcases Store.fin2_cases j with rfl | rfl)
  all_goals
    refine ⟨_, _, rfl, ?_, ?_, ?_, ?_, fun st => ⟨?_, ?_, fun h0 => ⟨?_, ?_⟩⟩⟩ <;>
    (try simp only [Loader.Site.inTrip, Time.loaderSlot, Time.loaderBand, Time.bandL,
      Loader.kvArrived, Loader.kvPolled, Loader.kvDone, Loader.qArrived, Loader.qIssued,
      Fin.val_zero, Fin.val_one, Fin.isValue, reduceCtorEq, forall_const] at *) <;>
    (try split_ifs) <;> omega

/-- The counts after the items: those of all the cluster's items. -/
theorem loader_tail {y : Nat} {c : Loader.D} (h : c.site.inItem = false)
    (hs : c.site ≠ .setMaxReg) :
    Loader.kvArrived L y c = Loader.uB L (Work.T L y) ∧
      Loader.kvDone L y c = Loader.uB L (Work.T L y) ∧
      ∀ st, Work.T L y ≤ Loader.qArrived L y c st ∧ Loader.qIssued L y c st = 2 * Work.T L y := by
  obtain ⟨site, i, t, s, ph, qp⟩ := c
  simp only at h hs ⊢
  rcases site with _ | _ | u | u | u | ⟨u, j⟩ | ⟨u, j⟩ | k | _ | _ | _ | _ <;>
    simp only [Loader.Site.inItem, Bool.true_eq_false] at h <;>
    simp only [ne_eq, not_true_eq_false] at hs <;>
    refine ⟨rfl, rfl, fun st => ⟨?_, rfl⟩⟩ <;>
    simp only [Loader.qArrived] <;> omega

theorem loader_fixed (n T : Nat) {c : Loader.D} (hs : c.site = .setMaxReg) :
    Time.loader n T c ≤ Time.base := by
  obtain ⟨site, i, t, s, ph, qp⟩ := c
  simp only at hs
  subst hs
  simp [Time.loader, Time.regT, Time.base]

/-- **A loader state that has not arrived on (or completed the copies of) ring use `U = 2 n i
+ u`** (`u < 2 n`, `i` an item of the cluster) is before band M of slot `(u + 1) / 2` of item `i`,
and not at its exit. -/
theorem loader_kv_lt {y : Nat} {c : Loader.D} (hinv : Loader.Inv L y c) (hn1 : 1 ≤ Work.n L)
    {i u o : Nat} (hiT : i < Work.T L y) (hu : u < 2 * Work.n L)
    (hc : Loader.kvArrived L y c ≤ Loader.uB L i + u ∨ Loader.kvDone L y c ≤ Loader.uB L i + u) :
    Time.loader (Work.n L) (Work.T L y) c + 1 <
      Time.slotTime (Work.n L) i ((u + 1) / 2) (Time.bandM + o) ∧ c.site ≠ .exit := by
  by_cases hI : c.site.inItem = true
  · obtain ⟨s, o', ht, ho', hs, h1, h2, -⟩ := loader_shape (y := y) (Work.T L y) hinv hn1 hI
    refine ⟨?_, fun he => by rw [he] at hI; simp [Loader.Site.inItem] at hI⟩
    rw [ht]
    rcases Nat.lt_trichotomy c.i i with hlt | heq | hgt
    · exact slotTime_lt (by omega) (by simp only [Time.span]; omega) (.inl hlt)
    · rw [heq] at h1 h2 ⊢
      refine slotTime_lt (by omega) (by simp only [Time.span]; omega) (.inr ⟨rfl, ?_⟩)
      simp only [Time.bandM]
      omega
    · have := uB_step (L := L) hgt
      omega
  · by_cases hs : c.site = .setMaxReg
    · refine ⟨?_, by rw [hs]; simp⟩
      have h1 := loader_fixed (Work.n L) (Work.T L y) hs
      have h2 : Time.base + 2 ≤ Time.slotTime (Work.n L) i ((u + 1) / 2) (Time.bandM + o) :=
        le_slotTime_of (by simp only [Time.base, Time.bandM]; omega)
      omega
    · obtain ⟨h1, h2, -⟩ := loader_tail (L := L) (y := y) (by simpa using hI) hs
      have := uB_step (L := L) hiT
      have := uB_step (L := L) (show i < i + 1 by omega)
      have : Loader.uB L (i + 1) ≤ Loader.uB L (Work.T L y) := by
        rcases Nat.lt_or_ge (i + 1) (Work.T L y) with h | h
        · have := uB_step (L := L) h; omega
        · rw [show Work.T L y = i + 1 by omega]
      omega

/-- **A loader state that has not arrived on (or completed the copies of) Q stage `st` of item
`i`** (an item of the cluster) is before band M of slot 0 of item `i`, and not at its exit. -/
theorem loader_q_lt {y : Nat} {c : Loader.D} (hinv : Loader.Inv L y c) (hn1 : 1 ≤ Work.n L)
    {i st o : Nat} (hiT : i < Work.T L y)
    (hc : Loader.qArrived L y c st ≤ i ∨ Loader.qIssued L y c st < 2 * i + 2) :
    Time.loader (Work.n L) (Work.T L y) c + 1 < Time.slotTime (Work.n L) i 0 (Time.bandM + o) ∧
      c.site ≠ .exit := by
  by_cases hI : c.site.inItem = true
  · obtain ⟨s, o', ht, ho', hs, -, -, hq⟩ := loader_shape (y := y) (Work.T L y) hinv hn1 hI
    obtain ⟨hq1, hq2, hq3⟩ := hq st
    refine ⟨?_, fun he => by rw [he] at hI; simp [Loader.Site.inItem] at hI⟩
    rw [ht]
    refine slotTime_lt (by omega) (by simp only [Time.span]; omega) ?_
    simp only [Time.bandM]
    rcases Nat.eq_zero_or_pos s with h0 | h0
    · omega
    · have := hq3 h0; omega
  · by_cases hs : c.site = .setMaxReg
    · refine ⟨?_, by rw [hs]; simp⟩
      have h1 := loader_fixed (Work.n L) (Work.T L y) hs
      have h2 : Time.base + 2 ≤ Time.slotTime (Work.n L) i 0 (Time.bandM + o) :=
        le_slotTime_of (by simp only [Time.base, Time.bandM]; omega)
      omega
    · obtain ⟨-, -, h3⟩ := loader_tail (L := L) (y := y) (by simpa using hI) hs
      have := h3 st
      omega

/-- **An MMA thread at a ring poll** of item `i` (an item of the cluster, its CTA a pair leader)
polls Q stage `k` with `i` successful polls, in band M of slot 0, or the slot of ring use
`U = 2 n i + u` (`u < 2 n`) with the ring uses below `U` on that slot, in band M of slot
`(u + 1) / 2`. -/
theorem mma_ring (hpre : Pre P L mem0) {g : Nat} {d : Mma.D} {es : List Event} {b : FBar}
    (hJ : Mma.Counts L g d es) (hinv : Mma.Inv L g d)
    (hs : (∃ k, d.site = .qWait k) ∨ ∃ k, d.site = .kvWait k) (hb : Mma.pollBar L d = some b) :
    d.i < Work.T L g ∧ Mma.rank L g = 0 ∧
      ((∃ k : Fin 2, b = .qFull k ∧ okPolls (b.loc L (ctaOf L g)) es = d.i ∧
          Time.mma (Work.n L) (Work.T L g) d =
            Time.slotTime (Work.n L) d.i 0 (Time.bandM + Time.mmaOff d.site)) ∨
        (∃ u, u < 2 * Work.n L ∧ b = .kvFull (Mma.slotOf L d.i u) ∧
          okPolls (b.loc L (ctaOf L g)) es =
            Loader.slotCount (Mma.kvUse L d.i u) (Mma.kvUse L d.i u % 6) ∧
          Time.mma (Work.n L) (Work.T L g) d =
            Time.slotTime (Work.n L) d.i ((u + 1) / 2) (Time.bandM + Time.mmaOff d.site))) := by
  have hn : Mma.trips L = Work.n L := rfl
  have hn1 := n_pos hpre
  have hph : d.site.phase = 1 := by rcases hs with ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] <;> rfl
  have hT := mma_time (Work.n L) (Work.T L g) d hph
  have hi := (hinv.i (itemSite_of_phase _ hph))
  have hiT := (Work.mma_work_lt hpre).mp hi.1
  refine ⟨hiT, hi.2, ?_⟩
  have htrip := hinv.trip
  unfold Mma.TripOk at htrip
  rw [hn] at htrip
  obtain ⟨site, i, t, bb, pr⟩ := d
  simp only at hs hb hT htrip ⊢
  rcases hs with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have hq := hJ.qFull k
    simp only [Mma.pollBar, Option.some.injEq] at hb
    subst hb
    refine .inl ⟨k, rfl, ?_, ?_⟩
    · rw [show (FBar.qFull k).loc L (ctaOf L g) = Mma.bar L g (.qFull k) from rfl, hq]
      fin_cases k <;> simp [Mma.cnt, Mma.qA, Mma.Site.after, Mma.Site.ord, Mma.qOrd]
    · rw [hT]; fin_cases k <;> rfl
  · have hk := hJ.kvFull (Mma.slotOf L i (Mma.kvU k t))
    simp only [Mma.pollBar, Option.some.injEq] at hb
    subst hb
    refine .inr ⟨Mma.kvU k t, ?_, rfl, ?_, ?_⟩
    · fin_cases k <;> simp [Mma.region, Mma.kvU] at htrip ⊢ <;> omega
    · rw [show (FBar.kvFull (Mma.slotOf L i (Mma.kvU k t))).loc L (ctaOf L g) =
        Mma.bar L g (.kvFull (Mma.slotOf L i (Mma.kvU k t))) from rfl, hk]
      simp only [Mma.slots, Loader.slotCount, Mma.slotOf, Mma.kvSlot]
      congr 2
      fin_cases k <;> simp [Mma.cnt, Mma.kvA, Mma.Site.after, Mma.Site.inTrip, Mma.Site.loop,
        Mma.Site.ord, Mma.kvOrd, Mma.kvU, Mma.kvUse, Mma.kvBase, hn] <;> ring
    · rw [hT]
      fin_cases k <;> simp [Mma.region, Mma.kvU, Time.mmaAt] at htrip ⊢ <;> congr 1 <;> omega

end Lag

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

/-- The waiter's facts at a ring poll, from its end state. -/
theorem Lag.ring_waiter (hub : ¬ HasUb X) {g : Nat} {d : Mma.D} {b : FBar}
    (hg : g < L.threads) (hσ : St L X g (X.tr g).length = some (some (.inr (.mma d))))
    (hs : (∃ k, d.site = .qWait k) ∨ ∃ k, d.site = .kvWait k) (hb : Mma.pollBar L d = some b) :
    d.i < Work.T L g ∧ ctaOf L g % 2 = 0 ∧
      ((∃ k : Fin 2, b = .qFull k ∧ okPolls (b.loc L (ctaOf L g)) (X.tr g) = d.i ∧
          stateTime L g (.inr (.mma d)) =
            Time.slotTime (Work.n L) d.i 0 (Time.bandM + Time.mmaOff d.site)) ∨
        (∃ u, u < 2 * Work.n L ∧ b = .kvFull (Mma.slotOf L d.i u) ∧
          okPolls (b.loc L (ctaOf L g)) (X.tr g) =
            Loader.slotCount (Mma.kvUse L d.i u) (Mma.kvUse L d.i u % 6) ∧
          stateTime L g (.inr (.mma d)) =
            Time.slotTime (Work.n L) d.i ((u + 1) / 2) (Time.bandM + Time.mmaOff d.site))) := by
  obtain ⟨hJ, hinv⟩ := Lag.end_state hpre hX ht hub hg hσ
  change Mma.Counts L g d (X.tr g) at hJ
  obtain ⟨h1, h2, h3⟩ := Lag.mma_ring hpre hJ hinv.1 hs hb
  exact ⟨h1, h2, h3⟩

open Lag in
/-- **The field `MmaRingPollFacts.arrive`**. -/
theorem MmaRingPollFacts_arrive :
    ∀ {g y : Nat} {d : Mma.D} {b : FBar}, g < L.threads → y < L.threads →
    St L X g (X.tr g).length = some (some (.inr (.mma d))) →
    ((∃ k, d.site = .qWait k) ∨ ∃ k, d.site = .kvWait k) → Mma.pollBar L d = some b →
    ctaOf L y = ctaOf L g → warpOf L y = 14 → SelfElected L X y →
    arrivals (b.loc L (ctaOf L g)) (X.tr y) ≤ okPolls (b.loc L (ctaOf L g)) (X.tr g) →
    Lags L X y g (.inr (.mma d)) := by
  intro g y d b hg hy hσ hs hb hcta hw hse hle hub
  obtain ⟨hiT, hev, hcase⟩ := ring_waiter hpre hX ht hub hg hσ hs hb
  have hT := T_eq_of_cta hcta
  have hn1 := n_pos hpre
  have hr : Work.rank L y = 0 := by simp only [Work.rank]; rw [hcta]; exact hev
  rcases hcase with ⟨k, rfl, hp, hW⟩ | ⟨u, hu, rfl, hp, hW⟩
  · have hW0 : Time.base + 2 ≤ stateTime L g (.inr (.mma d)) := by
      rw [hW]; exact le_slotTime_of (by simp only [Time.bandM, Time.base]; omega)
    refine lags_loader hpre hX ht hub hy hw (arrivesOn ((FBar.qFull k).loc L (ctaOf L g)))
      (d.i + 1) (stateTime L g (.inr (.mma d)) - 2) (by omega)
      (fun c es hk0 hJc hinvc hcnt => ?_) (by change arrivals _ _ < _; omega) (by omega)
    obtain ⟨j, rfl⟩ := hk0
    have h := hJc.qArr (electLead_of_self hse j) k
    simp only [hr, ↓reduceIte] at h
    rw [hcta] at h
    change List.countP _ _ = _ at h
    obtain ⟨h1, h2⟩ := loader_q_lt hinvc hn1 (st := k.val) (o := Time.mmaOff d.site)
      (by rw [hT]; exact hiT) (.inl (by omega))
    rw [hW]
    exact ⟨by omega, h2⟩
  · have hW0 : Time.base + 2 ≤ stateTime L g (.inr (.mma d)) := by
      rw [hW]; exact le_slotTime_of (by simp only [Time.bandM, Time.base]; omega)
    refine lags_loader hpre hX ht hub hy hw
      (arrivesOn ((FBar.kvFull (Mma.slotOf L d.i u)).loc L (ctaOf L g)))
      (Loader.slotCount (Mma.kvUse L d.i u) (Mma.kvUse L d.i u % 6) + 1)
      (stateTime L g (.inr (.mma d)) - 2) (by omega)
      (fun c es hk0 hJc hinvc hcnt => ?_) (by change arrivals _ _ < _; omega) (by omega)
    obtain ⟨j, rfl⟩ := hk0
    have h := hJc.kvArr (electLead_of_self hse j) (Mma.slotOf L d.i u)
    simp only [hr, ↓reduceIte] at h
    rw [hcta] at h
    change List.countP _ _ = _ at h
    have hA : Loader.kvArrived L y c ≤ Mma.kvUse L d.i u := by
      simp only [Loader.slotCount, Mma.slotOf, Mma.kvSlot] at h hcnt
      omega
    rw [kvUse_eq] at hA
    obtain ⟨h1, h2⟩ := loader_kv_lt hinvc hn1 (o := Time.mmaOff d.site)
      (by rw [hT]; exact hiT) hu (.inl hA)
    rw [hW]
    exact ⟨by omega, h2⟩

open Lag in
/-- **The field `MmaRingPollFacts.copies`**. -/
theorem MmaRingPollFacts_copies :
    ∀ {g y : Nat} {d : Mma.D} {b : FBar}, g < L.threads → y < L.threads →
    St L X g (X.tr g).length = some (some (.inr (.mma d))) →
    ((∃ k, d.site = .qWait k) ∨ ∃ k, d.site = .kvWait k) → Mma.pollBar L d = some b →
    ctaOf L y / 2 = ctaOf L g / 2 → warpOf L y = 14 → SelfElected L X y →
    (X.tr y).countP (issuesTo (b.loc L (ctaOf L g))) <
      b.copies * (okPolls (b.loc L (ctaOf L g)) (X.tr g) + 1) →
    Lags L X y g (.inr (.mma d)) := by
  intro g y d b hg hy hσ hs hb hcta hw hse hle hub
  obtain ⟨hiT, hev, hcase⟩ := ring_waiter hpre hX ht hub hg hσ hs hb
  have hT := T_eq_of_pair hpre hcta
  have hn1 := n_pos hpre
  have he : Loader.evenCta L y = ctaOf L g := by
    simp only [Loader.evenCta]; omega
  rcases hcase with ⟨k, rfl, hp, hW⟩ | ⟨u, hu, rfl, hp, hW⟩
  · have hW0 : Time.base + 2 ≤ stateTime L g (.inr (.mma d)) := by
      rw [hW]; exact le_slotTime_of (by simp only [Time.bandM, Time.base]; omega)
    rw [hp] at hle
    refine lags_loader hpre hX ht hub hy hw (issuesTo ((FBar.qFull k).loc L (ctaOf L g)))
      (2 * (d.i + 1)) (stateTime L g (.inr (.mma d)) - 2) (by omega)
      (fun c es hk0 hJc hinvc hcnt => ?_) hle (by omega)
    obtain ⟨j, rfl⟩ := hk0
    have h := hJc.qIss (electLead_of_self hse j) k
    rw [he] at h
    obtain ⟨h1, h2⟩ := loader_q_lt hinvc hn1 (st := k.val) (o := Time.mmaOff d.site)
      (by rw [hT]; exact hiT) (.inr (by omega))
    rw [hW]
    exact ⟨by omega, h2⟩
  · have hW0 : Time.base + 2 ≤ stateTime L g (.inr (.mma d)) := by
      rw [hW]; exact le_slotTime_of (by simp only [Time.bandM, Time.base]; omega)
    rw [hp] at hle
    refine lags_loader hpre hX ht hub hy hw
      (issuesTo ((FBar.kvFull (Mma.slotOf L d.i u)).loc L (ctaOf L g)))
      ((FBar.kvFull (Mma.slotOf L d.i u)).copies *
        (Loader.slotCount (Mma.kvUse L d.i u) (Mma.kvUse L d.i u % 6) + 1))
      (stateTime L g (.inr (.mma d)) - 2) (by omega)
      (fun c es hk0 hJc hinvc hcnt => ?_) hle (by omega)
    obtain ⟨j, rfl⟩ := hk0
    have h := hJc.kvIss (electLead_of_self hse j) (Mma.slotOf L d.i u)
    rw [he] at h
    have hD : Loader.kvDone L y c ≤ Mma.kvUse L d.i u := by
      rw [h] at hcnt
      simp only [Loader.kvIssued, Loader.slotCount, Mma.slotOf, Mma.kvSlot, FBar.copies,
        Fin.val_mk] at hcnt
      by_contra hc
      by_cases hpar : Mma.kvUse L d.i u % 6 % 2 = 0 <;>
        by_cases hm : Loader.kvDone L y c % 6 = Mma.kvUse L d.i u % 6 <;>
        simp only [hpar, hm, ↓reduceIte] at hcnt <;> omega
    rw [kvUse_eq] at hD
    obtain ⟨h1, h2⟩ := loader_kv_lt hinvc hn1 (o := Time.mmaOff d.site)
      (by rw [hT]; exact hiT) hu (.inr hD)
    rw [hW]
    exact ⟨by omega, h2⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof
