-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLagsRing
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.Loader

@[expose] public section

/-! # Producer lag at the loader's empty polls (`LoaderPollFacts.lag`)

A loader thread at a poll site has made, on the polled empty barrier, the successful polls of
the polls before it (`Loader.Ledger`: `qPoll`, `kvPoll`; `loader_wait`):

* Q stage `st`: `P` polls, `P = i` at `wait q0`, `wait q1` of item `i`, `P = T` at the drain's
  last poll; the poll is at slot 0 of item `P` (the tail is the slot time of item `T`).
* the KV ring: the polls of the uses below `U = kvPolled` on the slot of `U`, `U = 2 n i + u`
  (`u < 2 n`) at a use's poll, in band L of slot `u / 2` of item `i`, and `U = 2 n T + k` at the
  drain's poll `k`, in the tail.

The pair leader's MMA lane, self-elected, counts its commits to each Q-empty object (`i' + qeA`)
and to each KV-empty object (the ring uses below `R = cnt relA` on the slot). With fewer commits
than the waiter's polls it is in an item before `P` (`mma_lt_item`), or has `R + 6 ≤ U`: it has
not released the ring use six before `U`, which the MMA warp releases in its consuming slot. A
state of an item in slot `s` has released at least `2 s - 1` uses of its item (`mma_rel`), so it
is in an earlier item or in a slot below `u / 2` of item `i`, in band M before the loader's band
L of slot `u / 2` (`mma_kv_lt`). After the items the MMA lane has released every use and Q stage
of the cluster's items. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow Progress

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace Lag

/-- An MMA site before the items is two below the slots' start. -/
theorem mma_fixed_lt (n T : Nat) (c : Mma.D) (h : c.site.phase = 0) :
    Time.mma n T c + 2 ≤ Time.base := by
  obtain ⟨site, i, t, b, p⟩ := c
  cases site <;> simp_all [Mma.Site.phase, Time.mma, Time.regT, Time.allocT, Time.allocWriteT,
    Time.bar0T, Time.ldBaseT, Time.shflQT, Time.base]

/-- The KV uses an MMA state has released: `2 n` per item, and those of its item. -/
theorem rel_eq (c : Mma.D) :
    Mma.cnt L Mma.relA 2 0 c = Loader.uB L c.i + (Mma.relA c.site + 2 * (c.t * c.site.loop)) := by
  have hn : Mma.trips L = Work.n L := rfl
  simp only [Mma.cnt, Loader.uB, Nat.add_zero, hn]
  omega

/-- **An MMA state that is in an item before `i`, or before the items**, is before slot 0 of
item `i`, and not at its exit. -/
theorem mma_lt_item {y : Nat} {c : Mma.D} (hinv : Mma.Inv L y c) {i o : Nat}
    (hph : c.site.phase ≠ 2) (hci : c.site.phase = 1 → c.i < i) :
    Time.mma (Work.n L) (Work.T L y) c + 1 < Time.slotTime (Work.n L) i 0 o ∧ c.site ≠ .exit := by
  rcases phase_cases c.site with h0 | h1 | h2
  · refine ⟨?_, fun he => by rw [he] at h0; simp [Mma.Site.phase] at h0⟩
    have h1 := mma_fixed_lt (Work.n L) (Work.T L y) c h0
    have h2 : Time.base ≤ Time.slotTime (Work.n L) i 0 o := le_slotTime_of (by omega)
    omega
  · obtain ⟨s, o', ht, ho', hcase⟩ := mma_item (Work.T L y) hinv h1
    refine ⟨?_, fun he => by rw [he] at h1; simp [Mma.Site.phase] at h1⟩
    rw [ht]
    have := hci h1
    exact slotTime_lt (by omega) (by simp only [Time.bandM, Time.span]; omega) (.inl this)
  · exact absurd h2 hph

/-- A state of an item in slot `s` has released at least `2 s - 1` of its item's KV uses. -/
theorem mma_rel {y : Nat} (T : Nat) {c : Mma.D} (hinv : Mma.Inv L y c) (h1 : c.site.phase = 1) :
    ∃ s o, Time.mma (Work.n L) T c = Time.slotTime (Work.n L) c.i s (Time.bandM + o) ∧
      o < 100 ∧ s ≤ Work.n L ∧ 2 * s ≤ Mma.relA c.site + 2 * (c.t * c.site.loop) + 1 := by
  obtain ⟨s, o, ht, ho, hcase⟩ := mma_item T hinv h1
  refine ⟨s, o, ht, ho, by omega, ?_⟩
  simp only [Mma.relA, Mma.Site.after, Mma.Site.inTrip, Mma.Site.loop]
  split_ifs <;> omega

/-- **A self-elected MMA state that has not released ring use `U - 6`** (`U = 2 n i + u`,
`u < 2 n`, `i` an item of the cluster) is before band L of slot `u / 2` of item `i`, and not at
its exit. -/
theorem mma_kv_lt (hpre : Pre P L mem0) {y : Nat} {c : Mma.D} {es : List Event}
    (hJ : Mma.Counts L y c es) (hinv : Mma.Inv L y c) (hrank : Mma.rank L y = 0) {i u o : Nat}
    (hiT : i < Work.T L y) (hu : u < 2 * Work.n L)
    (hR : Mma.cnt L Mma.relA 2 0 c + 6 ≤ Loader.uB L i + u) :
    Time.mma (Work.n L) (Work.T L y) c + 1 < Time.slotTime (Work.n L) i (u / 2) o ∧
      c.site ≠ .exit := by
  rw [rel_eq] at hR
  rcases phase_cases c.site with h0 | h1 | h2
  · refine ⟨?_, fun he => by rw [he] at h0; simp [Mma.Site.phase] at h0⟩
    have h1 := mma_fixed_lt (Work.n L) (Work.T L y) c h0
    have h2 : Time.base ≤ Time.slotTime (Work.n L) i (u / 2) o := le_slotTime_of (by omega)
    omega
  · obtain ⟨s, o', ht, ho', hs, hrel⟩ := mma_rel (Work.T L y) hinv h1
    refine ⟨?_, fun he => by rw [he] at h1; simp [Mma.Site.phase] at h1⟩
    rw [ht]
    rcases Nat.lt_trichotomy c.i i with hlt | heq | hgt
    · exact slotTime_lt hs (by simp only [Time.bandM, Time.span]; omega) (.inl hlt)
    · rw [heq] at hR ⊢
      exact slotTime_lt hs (by simp only [Time.bandM, Time.span]; omega)
        (.inr ⟨rfl, .inl (by omega)⟩)
    · have := uB_step (L := L) hgt
      omega
  · exfalso
    have hd := mma_done hpre hJ hrank h2
    have h0 := ord_of_phase c.site (by omega)
    simp only [Mma.relA, Mma.Site.after, Mma.Site.inTrip, Mma.Site.loop, h0, Nat.not_lt_zero,
      false_and, ↓reduceIte] at hR
    have := uB_step (L := L) (show i < c.i by omega)
    omega

/-- **A loader thread at a poll site**: its successful polls of the polled empty barrier, and
the time of its poll. -/
theorem loader_wait {g : Nat} {d : Loader.D} {es : List Event} (hJ : Loader.Counts L g d es)
    (hinv : Loader.Inv L g d) (hn1 : 1 ≤ Work.n L) (hk : loaderKind d.site = .wait) :
    (∃ st : Fin 2, (loaderPollBar d).partner = .qEmpty st ∧ ∃ p o, p ≤ Work.T L g ∧ 2 ≤ o ∧
      okPolls (FBar.loc L (ctaOf L g) (.qEmpty st)) es = p ∧
      Time.loader (Work.n L) (Work.T L g) d = Time.slotTime (Work.n L) p 0 o) ∨
    (∃ U, (loaderPollBar d).partner = .kvEmpty ⟨U % 6, Nat.mod_lt _ (by decide)⟩ ∧
      okPolls (FBar.loc L (ctaOf L g) (.kvEmpty ⟨U % 6, Nat.mod_lt _ (by decide)⟩)) es =
        Loader.slotCount U (U % 6) ∧
      ((∃ u o, u < 2 * Work.n L ∧ U = Loader.uB L d.i + u ∧ d.i < Work.T L g ∧
          Time.loader (Work.n L) (Work.T L g) d = Time.slotTime (Work.n L) d.i (u / 2) o) ∨
        (∃ k, k < 6 ∧ U = Loader.uB L (Work.T L g) + k ∧
          Time.loader (Work.n L) (Work.T L g) d = Time.slotTime (Work.n L) (Work.T L g) 0 (2 * k))))
    := by
  have hring := hJ.ring.1
  have hitem := hinv.item
  have htrip := hinv.trip
  obtain ⟨site, i, t, s, ph, qp⟩ := d
  simp only at hring hitem htrip hk ⊢
  rcases site with _ | _ | u | u | u | ⟨u, j⟩ | ⟨u, j⟩ | k | _ | _ | _ | _ <;>
    simp only [loaderKind, reduceCtorEq] at hk
  · cases u
    · refine .inr ⟨Loader.uB L i, ?_, ?_, .inl ⟨0, _, by omega, rfl, hitem rfl, rfl⟩⟩
      · simp only [loaderPollBar, FBar.partner, Loader.kvB] at hring ⊢; congr 2; omega
      · rw [hJ.kvPoll]; rfl
    · refine .inl ⟨0, rfl, i, Time.bandL + 16 * 1 + 1, (hitem rfl).le, by decide, ?_, rfl⟩
      rw [hJ.qPoll]; rfl
    · refine .inl ⟨1, rfl, i, Time.bandL + 16 * 2 + 1, (hitem rfl).le, by decide, ?_, rfl⟩
      rw [hJ.qPoll]; simp [Loader.qPolled]
    · refine .inr ⟨Loader.uB L i + 1, ?_, ?_, .inl ⟨1, _, by omega, rfl, hitem rfl, rfl⟩⟩
      · simp only [loaderPollBar, FBar.partner, Loader.kvB] at hring ⊢; congr 2; omega
      · rw [hJ.kvPoll]; rfl
    · have ht2 := htrip rfl
      refine .inr ⟨Loader.uB L i + (2 + 2 * t), ?_, ?_,
        .inl ⟨2 + 2 * t, Time.bandL + 16 * 0 + 1, by omega, rfl, hitem rfl, ?_⟩⟩
      · simp only [loaderPollBar, FBar.partner, Loader.kvB] at hring ⊢; congr 2; omega
      · rw [hJ.kvPoll]; simp only [Loader.kvPolled]; congr 1; omega
      · simp only [Time.loader, Time.loaderUse, Time.loaderSlot, Time.loaderBand]
        congr 1; omega
    · have ht2 := htrip rfl
      refine .inr ⟨Loader.uB L i + (3 + 2 * t), ?_, ?_,
        .inl ⟨3 + 2 * t, Time.bandL + 16 * 1 + 1, by omega, rfl, hitem rfl, ?_⟩⟩
      · simp only [loaderPollBar, FBar.partner, Loader.kvB] at hring ⊢; congr 2; omega
      · rw [hJ.kvPoll]; simp only [Loader.kvPolled]; congr 1; omega
      · simp only [Time.loader, Time.loaderUse, Time.loaderSlot, Time.loaderBand]
        congr 1; omega
  · refine .inr ⟨Loader.uB L (Work.T L g) + k.val, ?_, ?_, .inr ⟨k.val, k.isLt, rfl, rfl⟩⟩
    · simp only [loaderPollBar, FBar.partner, Loader.kvB] at hring ⊢; congr 2; omega
    · rw [hJ.kvPoll]; rfl
  · refine .inl ⟨1, rfl, Work.T L g, 12, le_rfl, by decide, ?_, rfl⟩
    rw [hJ.qPoll]; rfl

end Lag

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

open Lag in
/-- **The field `LoaderPollFacts.lag`**. -/
theorem LoaderPollFacts_lag :
    ∀ {g y : Nat} {d : Loader.D}, g < L.threads → y < L.threads →
    St L X g (X.tr g).length = some (some (.inr (.loader d))) → loaderKind d.site = .wait →
    warpOf L y = 12 → ctaOf L y = pairBase L g → SelfElected L X y →
    (X.tr y).countP (commitsTo ((loaderPollBar d).partner.loc L (ctaOf L y))) + 1 ≤
      okPolls ((loaderPollBar d).partner.loc L (ctaOf L g)) (X.tr g) →
    Lags L X y g (.inr (.loader d)) := by
  intro g y d hg hy hσ hk hw hcta hse hle hub
  obtain ⟨hJ, hinv⟩ := end_state hpre hX ht hub hg hσ
  change Loader.Counts L g d (X.tr g) at hJ
  change Loader.Inv L g d at hinv
  have hn1 := n_pos hpre
  have hT : Work.T L y = Work.T L g :=
    T_eq_of_pair hpre (by rw [hcta]; simp only [pairBase]; omega)
  have hrank : Mma.rank L y = 0 := by
    have h' : y / L.block = 2 * (ctaOf L g / 2) := hcta
    simp only [Mma.rank, h']
    omega
  have hW := fun (x : Nat) (h : x = Time.loader (Work.n L) (Work.T L g) d) =>
    (show stateTime L g (.inr (.loader d)) = x from h.symm)
  rcases loader_wait hJ hinv hn1 hk with ⟨st, hpb, p, o, hpT, ho, hp, htime⟩ |
    ⟨U, hpb, hp, hcase⟩
  · rw [hpb, hp] at hle
    have hS := hW _ htime.symm
    have hW0 : Time.base + 2 ≤ stateTime L g (.inr (.loader d)) := by
      rw [hS]; exact le_slotTime_of (by omega)
    refine lags_mma hpre hX ht hub hy hw (commitsTo ((FBar.qEmpty st).loc L (ctaOf L y))) p
      (stateTime L g (.inr (.loader d)) - 2) (by omega)
      (fun c es hk0 hJc hinvc hcnt => ?_) (by omega) (by omega)
    obtain ⟨j, rfl⟩ := hk0
    have h := hJc.qEmpty (electLead_of_self hse j) st
    change List.countP (commitsTo (FBar.loc L (ctaOf L y) _)) _ = _ at h
    rw [h] at hcnt
    simp only [Mma.cnt, Nat.zero_mul, Nat.zero_add, Nat.one_mul] at hcnt
    have hph : c.site.phase ≠ 2 := by
      intro h2
      have := mma_done hpre hJc hrank h2
      omega
    obtain ⟨h1, h2⟩ := mma_lt_item hinvc (i := p) (o := o) hph (fun _ => by omega)
    rw [hS]
    exact ⟨by omega, h2⟩
  · rw [hpb, hp] at hle
    rcases hcase with ⟨u, o, hu, hU, hiT, htime⟩ | ⟨k, hk6, hU, htime⟩
    · have hS := hW _ htime.symm
      have hU6 : 6 ≤ U := by
        simp only [Loader.slotCount] at hle; omega
      have hW0 : Time.base + 2 ≤ stateTime L g (.inr (.loader d)) := by
        rw [hS]
        have := le_slotTime_of (n := Work.n L) (i := d.i) (s := u / 2) (o := o) (x := Time.base)
          (by omega)
        by_cases hi0 : d.i = 0
        · subst hU
          rw [hi0] at hU6 ⊢
          simp only [Loader.uB, Nat.mul_zero, Nat.zero_add] at hU6
          unfold Time.slotTime Time.gslot
          simp only [Time.base, Time.span]
          omega
        · unfold Time.slotTime Time.gslot
          have : 1 ≤ d.i * (Work.n L + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
          simp only [Time.base, Time.span]
          omega
      refine lags_mma hpre hX ht hub hy hw
        (commitsTo ((FBar.kvEmpty ⟨U % 6, Nat.mod_lt _ (by decide)⟩).loc L (ctaOf L y)))
        (Loader.slotCount U (U % 6)) (stateTime L g (.inr (.loader d)) - 2) (by omega)
        (fun c es hk0 hJc hinvc hcnt => ?_) (by omega) (by omega)
      obtain ⟨j, rfl⟩ := hk0
      have h := hJc.kvEmpty (electLead_of_self hse j) ⟨U % 6, Nat.mod_lt _ (by decide)⟩
      change List.countP (commitsTo (FBar.loc L (ctaOf L y) _)) _ = _ at h
      rw [h] at hcnt
      have hR : Mma.cnt L Mma.relA 2 0 c + 6 ≤ Loader.uB L d.i + u := by
        simp only [Mma.slots, Loader.slotCount] at hcnt; omega
      obtain ⟨h1, h2⟩ := mma_kv_lt hpre hJc hinvc hrank (o := o) (by rw [hT]; exact hiT) hu hR
      rw [hS]
      exact ⟨by omega, h2⟩
    · have hS := hW _ htime.symm
      have hTp : 1 ≤ Work.T L g := by
        by_contra h0
        have : Work.T L g = 0 := by omega
        rw [this] at hU
        simp only [Loader.uB, Nat.mul_zero, Nat.zero_add] at hU
        simp only [Loader.slotCount] at hle
        omega
      have hW0 : Time.base + 2 ≤ stateTime L g (.inr (.loader d)) := by
        rw [hS]
        unfold Time.slotTime Time.gslot
        have : 1 ≤ Work.T L g * (Work.n L + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
        simp only [Time.base, Time.span]
        omega
      refine lags_mma hpre hX ht hub hy hw
        (commitsTo ((FBar.kvEmpty ⟨U % 6, Nat.mod_lt _ (by decide)⟩).loc L (ctaOf L y)))
        (Loader.slotCount U (U % 6)) (stateTime L g (.inr (.loader d)) - 2) (by omega)
        (fun c es hk0 hJc hinvc hcnt => ?_) (by omega) (by omega)
      obtain ⟨j, rfl⟩ := hk0
      have h := hJc.kvEmpty (electLead_of_self hse j) ⟨U % 6, Nat.mod_lt _ (by decide)⟩
      change List.countP (commitsTo (FBar.loc L (ctaOf L y) _)) _ = _ at h
      rw [h, rel_eq] at hcnt
      have hph : c.site.phase ≠ 2 := by
        intro h2
        have hd := mma_done hpre hJc hrank h2
        have h0 := ord_of_phase c.site (by omega)
        simp only [Mma.slots, Loader.slotCount, Mma.relA, Mma.Site.after, Mma.Site.inTrip,
          Mma.Site.loop, h0, Nat.not_lt_zero, false_and, ↓reduceIte] at hcnt
        rcases Nat.lt_or_ge (Work.T L g) c.i with hlt | hge
        · have := uB_step (L := L) hlt; omega
        · rw [show c.i = Work.T L g by omega] at hcnt; omega
      have hci : c.site.phase = 1 → c.i < Work.T L g := fun h1 => by
        have := (Work.mma_work_lt (g := y) hpre).mp (hinvc.i (itemSite_of_phase _ h1)).1
        omega
      obtain ⟨h1, h2⟩ := mma_lt_item hinvc (i := Work.T L g) (o := 2 * k) hph hci
      rw [hS]
      exact ⟨by omega, h2⟩

end
end PTX.Kernels.FlashAttn4Fwd.Proof
