-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderBatchSelect
public import Kernels.TmlFa4Fwd.Proof.LoaderIdle

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

/-- The fallback ends with a masked CTA or with the selected group's verified interval. -/
def FallbackResult (p : Params) (l : Launch) (X : Execution) (g warp votes : Nat) : Prop :=
  (tilePrefix p p.batch * p.heads ≤ g / l.block ∧
    ∃ shuffles, Nonempty (SchedulerWarpAt l X g 1862
      (fun _ => loaderIdleDrainFacts l warp) shuffles votes)) ∨
  ∃ first shuffles, first < p.batch ∧ tilePrefix p first * p.heads ≤ g / l.block ∧
    g / l.block < tilePrefix p (min p.batch (first + 31)) * p.heads ∧
    Nonempty (SchedulerWarpAt l X g 288 (loaderLaterChoiceFacts p l g warp first)
      shuffles votes)

/-- Each actual fallback iteration advances by 31 requests or clips to the sentinel.
The group cannot be revisited before the decoded scheduler selects work or takes the idle path. -/
theorem loaderFallbackSearch {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g warp first shuffles votes : Nat} (hg : g < l.threads) (hf : first < p.batch)
    (hPast : tilePrefix p (min p.batch (first + 31)) * p.heads ≤ g / l.block)
    (cur : SchedulerWarpAt l X g 234 (loaderFallbackFacts p l g warp first) shuffles votes)
    (hProtected : ∀ i ≤ p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * i)).at k)) :
    FallbackResult p l X g warp votes := by
  suffices all : ∀ fuel first shuffles, p.batch - first = fuel → first < p.batch →
      tilePrefix p (min p.batch (first + 31)) * p.heads ≤ g / l.block →
      SchedulerWarpAt l X g 234 (loaderFallbackFacts p l g warp first) shuffles votes →
      FallbackResult p l X g warp votes by
    exact all _ first shuffles rfl hf hPast cur
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro first shuffles hFuel hf hPast cur
    have hAdvance := loaderFallbackAdvance hp hf cur
    by_cases hClip : p.batch ≤ first + 31
    · rw [ite_eq_left hClip] at hAdvance
      obtain ⟨atEnd⟩ := hAdvance
      obtain ⟨idle⟩ := loaderFallbackExhausted hp hg hClip atEnd
      exact .inl ⟨by simpa only [Nat.min_eq_left hClip] using hPast, shuffles, loaderIdleWarp idle⟩
    · have hFirst : first + 31 < p.batch := Nat.lt_of_not_ge hClip
      rw [ite_eq_right hClip] at hAdvance
      obtain ⟨ready⟩ := hAdvance
      obtain ⟨down⟩ := loaderLaterWarpCuQ hp hX hg hFirst ready hProtected
      obtain ⟨scan⟩ := loaderLaterScan hp hX hg hFirst down
      rcases loaderLaterRoute hp hX hg hFirst scan with ⟨hNext, ⟨nextGroup⟩⟩ | ⟨hLimit, hFound⟩
      · exact ih (p.batch - (first + 31)) (by omega) (first + 31) (shuffles + 7)
          rfl hFirst hNext nextGroup
      · exact .inr ⟨first + 31, shuffles + 7, hFirst,
          by simpa only [Nat.min_eq_right (Nat.le_of_lt hFirst)] using hPast, hLimit, hFound⟩

/-- The loader's scheduler either enters its idle drain or computes the unique batch assigned
to this CTA and returns the actual post-ballot state. -/
def LoaderScheduleResult (p : Params) (l : Launch) (X : Execution) (g warp : Nat) : Prop :=
  (tilePrefix p p.batch * p.heads ≤ g / l.block ∧
    ∃ shuffles, Nonempty (SchedulerWarpAt l X g 1862
      (fun _ => loaderIdleDrainFacts l warp) shuffles 0)) ∨
  ∃ first batch shuffles, first ≤ batch ∧ batch < first + 31 ∧ batch < p.batch ∧
    tilePrefix p batch * p.heads ≤ g / l.block ∧
    g / l.block < tilePrefix p (batch + 1) * p.heads ∧
    Nonempty (SchedulerWarpAt l X g 302 (loaderChosenFacts p l g warp first batch) shuffles 1)

/-- From a consistent, completed execution the full loader group search follows the decoded
per-lane reads and collectives and reaches the idle drain or the selected batch. -/
theorem loaderSchedule {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hComplete : Complete l X)
    {g : Nat} (hg : g < l.threads) (hWarp : 14 ≤ Prologue.warpIndex l g)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc) :
    LoaderScheduleResult p l X g (Prologue.warpIndex l g) := by
  let cta := g / l.block
  let bound := tilePrefix p (min p.batch 31) * p.heads
  have hStart := loaderStartupSchedule hp hX hComplete hg hWarp writes
  by_cases hFirst : cta < bound
  · have hBranch : g / l.block < tilePrefix p (min p.batch 31) * p.heads := hFirst
    rw [ite_eq_left hBranch] at hStart
    obtain ⟨cur⟩ := hStart
    obtain ⟨batch, hIn, hLo, hHi, hReady⟩ := loaderFirstBatch hp hX hg hBranch cur
    exact .inr ⟨0, batch, 10, by omega, hIn.trans_le (Nat.min_le_right ..),
      hIn.trans_le (Nat.min_le_left ..), hLo, hHi, hReady⟩
  · have hBranch : ¬g / l.block < tilePrefix p (min p.batch 31) * p.heads := hFirst
    rw [ite_eq_right hBranch] at hStart
    obtain ⟨cur⟩ := hStart
    obtain ⟨fallback⟩ := loaderFallbackStart hp hg cur
    have hPast : tilePrefix p (min p.batch (0 + 31)) * p.heads ≤ g / l.block :=
      Nat.le_of_not_gt hFirst
    rcases loaderFallbackSearch hp hX hg hp.shape.1 hPast fallback (hp.cuQ_protected writes) with
      hIdle | ⟨first, shuffles, hf, hStart, hStop, ⟨found⟩⟩
    · exact .inl hIdle
    · have hAll := Nat.mul_le_mul_right p.heads
        (tilePrefix_mono p (Nat.min_le_left p.batch (first + 31)))
      obtain ⟨batch, ⟨hb, hLo, hHi⟩, _⟩ := tileBatch_existsUnique p (hStop.trans_le hAll)
      have hGroupLo : first ≤ batch := by
        by_contra! h
        have hLe := Nat.mul_le_mul_right p.heads
          (tilePrefix_mono p (show batch + 1 ≤ first by omega))
        omega
      have hGroupHi : batch < first + 31 := by
        by_contra! h
        have hMin : min p.batch (first + 31) ≤ batch := (Nat.min_le_right ..).trans h
        have hLe := Nat.mul_le_mul_right p.heads (tilePrefix_mono p hMin)
        omega
      obtain ⟨ready⟩ := loaderGroupBallotReady hp hg hGroupLo hGroupHi hb hLo hHi found
      exact .inr ⟨first, batch, shuffles, hGroupLo, hGroupHi, hb, hLo, hHi,
        loaderSelectBatch hp hX hg hGroupLo hGroupHi hb ready⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
