-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashAttn4Fwd.Proof.Thread.FactsLags
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.Staged
public import Kernels.FlashAttn4Fwd.Proof.Interface.ProgressPolls.Free

@[expose] public section

/-! # Producer lag at the output polls (`StagedPollFacts.lag`, `FreePollFacts.lag`)

**Staged.** A store lane at `wait st` of item `i` has made `i` successful polls of the staged
barrier (`Store.Counts.staged`). A correction thread of its CTA with at most `i` staged arrivals
of the stage (`Correction.Counts.staged`: `i' + stagedPos`) is in an item before `i`, or in item
`i` no later than its `staged st` site (`corr_staged_le`, offset `+176` of band C `st` in slot
`n`); the store lane's poll is in band ST of that slot.

**Free.** A correction thread at `fWait st` of item `i` has made `i` successful polls of the
free barrier, at the tail's `tailWait` `T` (`Correction.Counts.oFree`). A store lane of its CTA
with fewer free arrivals of the stage (`Store.Counts.freed`: `done + before`) is no later than
its `free st` site of item `i - 1` (`store_free_le`), in slot `n` of an earlier item than the
poll. Neither producer is at its exit, which comes after all its arrivals. -/

namespace PTX.Kernels.FlashAttn4Fwd.Proof
open PTX PTX.Proof PTX.Flow Progress

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

namespace Lag

/-- Two threads of one CTA have the cluster's items. -/
theorem T_eq_of_cta {y g : Nat} (h : ctaOf L y = ctaOf L g) : Work.T L y = Work.T L g := by
  simp only [Work.T, Work.cid, clusterOf]
  rw [h]

/-- **A store state with fewer free arrivals of stage `st` than `i ≤ T`** is no later than its
`free st` site of item `i - 1`, and not at its exit. -/
theorem store_free_le {y : Nat} {d : Store.D} {st : Fin 2} {i : Nat} (hi : i ≤ Work.T L y)
    (hc : Store.done L y d + Store.before (.free st) d < i) :
    Time.store (Work.n L) (Work.T L y) d ≤
      Time.storeAt (Work.n L) (i - 1) (18 + 4 * st.val) ∧ d.site ≠ .exit := by
  obtain ⟨site, di⟩ := d
  rcases site with _ | st' | ⟨st', hh⟩ | st' | st' | st' | _
  all_goals (try rcases Store.fin2_cases st' with rfl | rfl)
  all_goals (try rcases Store.fin2_cases hh with rfl | rfl)
  all_goals rcases Store.fin2_cases st with rfl | rfl
  all_goals first
    | (exfalso
       simp [Store.done, Store.before, Store.Site.pos] at hc
       omega)
    | (refine ⟨?_, by simp⟩
       simp only [Store.done, Store.before, Store.Site.pos, Time.store, Time.storeAt,
        Fin.val_zero, Fin.val_one, Fin.isValue, reduceCtorEq, Nat.reduceLT, ite_true,
        ite_false] at hc ⊢
       refine slotTime_le le_rfl ?_ ?_ <;>
         (try simp only [Time.bandST, Time.span, true_and]) <;> omega)
    | (refine ⟨fixed_le_slotTime ?_, ?_⟩ <;> simp [Time.store, Time.regT, Time.base])

/-- **A correction state with at most `i` staged arrivals of stage `st`**, `i` an item of the
cluster, is no later than its `staged st` site of item `i`, and not at its exit. -/
theorem corr_staged_le {y : Nat} {c : Correction.D} (hinv : Correction.Inv L y c) {st : Fin 2}
    {i : Nat} (hi : i < Correction.items L y) (hn1 : 1 ≤ Work.n L)
    (hc : c.i + Correction.stagedPos st.val c < i + 1) :
    Time.correction (Work.n L) (Work.T L y) c ≤
      Time.slotTime (Work.n L) i (Work.n L) (Time.bandC st.val + 176) ∧ c.site ≠ .exit := by
  have hn : Correction.trips L = Work.n L := rfl
  obtain ⟨site, ci, ct, aw, a⟩ := c
  have htrip := hinv.trip
  have htail := hinv.tail
  simp only at htrip htail hc ⊢
  rw [hn] at htrip
  rcases site with _ | _ | st' | ⟨st', gen⟩ | a | st' | st' | ⟨st', j⟩ | ⟨st', j⟩ | ⟨st', j⟩ |
    st' | ⟨st', fin⟩ | st' | st' | st' | ⟨st', j⟩ | ⟨st', j⟩ | ⟨st', j, hh, el⟩ | st' | st' | _ |
    _ | _
  all_goals (try rcases Store.fin2_cases st' with rfl | rfl)
  all_goals rcases Store.fin2_cases st with rfl | rfl
  all_goals (try cases gen)
  all_goals (try cases fin)
  all_goals (try rcases fin6_cases a with rfl | rfl | rfl | rfl | rfl | rfl)
  all_goals (try have := j.isLt)
  all_goals (try have := hh.isLt)
  all_goals (try have := el.isLt)
  all_goals first
    | (simp [Correction.Site.inItem] at htail
       simp only [Correction.stagedPos] at hc
       omega)
    | (refine ⟨?_, by simp⟩
       simp only [Correction.Site.inTrip, Correction.stagedPos, Time.correction, Fin.val_zero,
         Fin.val_one, Fin.isValue, Bool.false_eq_true, ↓reduceIte,
         forall_const] at htrip hc ⊢
       refine slotTime_le ?_ ?_ ?_ <;>
         (try simp only [Time.bandC, Time.span, true_and]) <;> omega)
    | (refine ⟨fixed_le_slotTime ?_, ?_⟩ <;>
        simp [Time.correction, Time.base, Time.regT, Time.bar0T, Time.freeT])

/-- The KV tiles of an item: at least one. -/
theorem n_pos {P : Params} {mem0 : Mem0} (hpre : Pre P L mem0) : 1 ≤ Work.n L :=
  trips_pos hpre

end Lag

variable (hpre : Pre P L mem0) (hX : Consistent L kernel asms mem0 X)
  (ht : Frame.Tracked (code L) X)
include hpre hX ht

open Lag in
/-- **The field `StagedPollFacts.lag`**. -/
theorem StagedPollFacts_lag :
    ∀ {g y : Nat} {d : Store.D} {st : Fin 2}, g < L.threads → y < L.threads →
    ctaOf L y = ctaOf L g → 8 ≤ warpOf L y → warpOf L y < 12 →
    St L X g (X.tr g).length = some (some (.inr (.store d))) → d.site = .wait st →
    arrivals (stagedBar L (ctaOf L g) st) (X.tr y) ≤ okPolls (stagedBar L (ctaOf L g) st) (X.tr g) →
      Lags L X y g (.inr (.store d)) := by
  intro g y d st hg hy hcta hw1 hw2 hσ hs hle hub
  obtain ⟨hJ, hinv⟩ := end_state hpre hX ht hub hg hσ
  change Store.Counts L g d (X.tr g) at hJ
  change d.site = .setMaxReg ∨ Store.Inv L g d at hinv
  have hi : d.i < Work.T L g :=
    (hinv.resolve_left (by rw [hs]; simp)) (by rw [hs]; simp)
  have hp := hJ.staged st
  have hloc : stagedBar L (ctaOf L g) st = Store.stagedAt L g st := by
    simp [stagedBar, Store.stagedAt, ctaOf, Nat.add_assoc]
  have hdone : Store.done L g d + Store.before (.wait st) d = d.i := by
    obtain ⟨site, i⟩ := d
    simp only at hs
    subst hs
    rcases Store.fin2_cases st with rfl | rfl <;> simp [Store.done, Store.before, Store.Site.pos]
  rw [← hloc, hdone] at hp
  have hT := T_eq_of_cta hcta
  refine lags_corr hpre hX ht hub hy ⟨hw1, hw2⟩ (arrivesOn (stagedBar L (ctaOf L g) st))
    (d.i + 1) (Time.slotTime (Work.n L) d.i (Work.n L) (Time.bandC st.val + 176))
    (fixed_le_slotTime (by decide)) (fun c es _ hJc hinvc hcnt => ?_) ?_ ?_
  · have h := hJc.staged st.val st.isLt
    have hl : Correction.ownLoc L y (256 + 8 * st.val) = stagedBar L (ctaOf L g) st := by
      simp [Correction.ownLoc, stagedBar, hcta, Correction.sb]
    rw [hl] at h
    change (es.countP (arrivesOn _)) = _ at h
    exact corr_staged_le hinvc (by rw [Correction.items_eq, hT]; exact hi) (n_pos hpre)
      (by omega)
  · change arrivals _ _ ≤ _ at hle
    unfold arrivals at hle
    omega
  · show _ < Time.store (Work.n L) (Work.T L g) d
    obtain ⟨site, i⟩ := d
    simp only at hs hi ⊢
    subst hs
    refine slotTime_lt le_rfl ?_ ?_ <;> rcases Store.fin2_cases st with rfl | rfl <;>
      simp [Time.bandC, Time.span, Time.bandST]

open Lag in
/-- **The field `FreePollFacts.lag`**. -/
theorem FreePollFacts_lag :
    ∀ {g y : Nat} {d : Correction.D} {st : Fin 2}, g < L.threads → y < L.threads →
    ctaOf L y = ctaOf L g → warpOf L y = 13 →
    St L X g (X.tr g).length = some (some (.inr (.corr d))) → FreeSite d.site st →
    arrivals (freeBar L (ctaOf L g) st) (X.tr y) + 1 ≤ okPolls (freeBar L (ctaOf L g) st) (X.tr g) →
      Lags L X y g (.inr (.corr d)) := by
  intro g y d st hg hy hcta hw hσ hs hle hub
  obtain ⟨hJ, hinv⟩ := end_state hpre hX ht hub hg hσ
  change Correction.Counts L g d (X.tr g) at hJ
  change Correction.Inv L g d at hinv
  have hp := hJ.oFree st.val st.isLt
  have hloc : Correction.ownLoc L g (272 + 8 * st.val) = freeBar L (ctaOf L g) st := by
    simp [Correction.ownLoc, freeBar, Correction.sb]
  rw [hloc] at hp
  have hT := T_eq_of_cta hcta
  -- the waiter's item: `i < T` at `fWait`, `T` at the tail; its successful polls are `i`
  have hfp : Correction.fPos st.val d = 0 := by
    rcases hs with hs | ⟨hs, rfl⟩ <;> rw [Correction.fPos, hs]
    rcases Store.fin2_cases st with rfl | rfl <;> rfl
  have hiT : d.i ≤ Work.T L g := by
    rcases hs with hs | ⟨hs, -⟩
    · exact (hinv.item (by rw [hs]; rfl)).le
    · exact (hinv.tail (by rw [hs]; rfl) (by rw [hs]; simp) (by rw [hs]; simp)
        (fun _ => by rw [hs]; simp)).le
  rw [hfp, Nat.add_zero] at hp
  refine lags_store hpre hX ht hub hy hw (arrivesOn (freeBar L (ctaOf L g) st)) d.i
    (Time.storeAt (Work.n L) (d.i - 1) (18 + 4 * st.val)) (fixed_le_slotTime (by decide))
    (fun c es _ hJc _ hcnt => ?_) ?_ ?_
  · have h := hJc.freed st
    have hl : Store.freeAt L y st = freeBar L (ctaOf L g) st := by
      have hc' : y / L.block = ctaOf L g := hcta
      simp [Store.freeAt, freeBar, hc', Nat.add_assoc]
    rw [hl] at h
    change (es.countP (arrivesOn _)) = _ at h
    exact store_free_le (by rw [hT]; exact hiT) (by omega)
  · change arrivals _ _ + 1 ≤ _ at hle
    unfold arrivals at hle
    change okPolls _ _ = _ at hp
    omega
  · have h1 : 1 ≤ d.i := by
      change arrivals _ _ + 1 ≤ _ at hle
      omega
    show _ < Time.correction (Work.n L) (Work.T L g) d
    unfold Time.storeAt
    obtain ⟨site, i, t, aw, a⟩ := d
    simp only at hs h1 hiT ⊢
    rcases hs with hs | ⟨hs, rfl⟩ <;> subst hs
    · have hi : i < Work.T L g := hinv.item rfl
      refine slotTime_lt le_rfl ?_ (.inl (by dsimp only; omega))
      rcases Store.fin2_cases st with rfl | rfl <;> simp [Time.bandST, Time.span]
    · have hi : i = Work.T L g := hinv.tail rfl (by simp) (by simp) (fun _ => by simp)
      subst hi
      exact slotTime_lt le_rfl (by simp [Time.bandST, Time.span]) (.inl (by omega))

end
end PTX.Kernels.FlashAttn4Fwd.Proof
