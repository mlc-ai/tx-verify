-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderActualCacheUseBound
public import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderRoundReusePhase
import all Kernels.TmlFa4Fwd.Proof.Thread.LoaderCachePublicationRank
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingSources
import Lemmas.Flow.NthEv
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Epilogue Prologue
open PTX.Kernels.TmlFa4Fwd.Loader (reuseArrival loaderShuffleTail primingSearchShuffleCount)

noncomputable section

set_option maxRecDepth 100000 in
/-- In a scheduled CTA, every recurring publication of a loader lane follows exactly
`32 + 32 * use` warp shuffles after the priming search, where `use` is its ring position.
Each K/V packet performs 32 shuffles before its own publication. -/
theorem recurringPublicationShuffleRank {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X)
    {g lane index batch : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hl : lane < 32)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    {e : Event} (he : X.get (warpLane l g lane, index) = some e)
    (hMark : recurringPublicationMark e = true) :
    ((X.tr (warpLane l g lane)).take index).countP Execution.isShfl =
      primingSearchShuffleCount batch + 32 +
        32 * recurringUseBefore X (warpLane l g lane, index) := by
  let writes := fun w a data loc h => loaderOutputWrites hFrame (w := w) (a := a)
    (data := data) (loc := loc) h
  have hCTA : g/l.block < tilePrefix p p.batch*p.heads :=
    hHi.trans_le (Nat.mul_le_mul_right _ (tilePrefix_mono p (by omega)))
  obtain ⟨site, loc, rfl⟩ := (recurringPublicationMark_iff e).mp hMark
  have hSafe : ∀ f, Kind.asyncArrive loc true ≠ .ub f := fun _ h => by cases h
  obtain ⟨_, _, hUnique⟩ := tileBatch_existsUnique p hCTA
  by_cases hWarm : reuseArrival site < 1348
  · have hPc : 917 ≤ reuseArrival site := by fin_cases site <;> decide
    obtain ⟨b, hb', hLo', hHi', hObs⟩ := actualWarmCacheProjectionOrAfter hp hX hg hw hl
      writes hCTA he hPc (.inl (show reuseArrival site < 1353 by omega)) hSafe
    have hSame := (hUnique b ⟨hb', hLo', hHi'⟩).trans (hUnique batch ⟨hb, hLo, hHi⟩).symm
    subst b
    rcases hObs with ⟨_, round, _, hUse, hTotal⟩ | ⟨hAfter, _⟩
    · have hSite : site = 0 ∨ site = 1 := by
        fin_cases site
        · exact .inl rfl
        · exact .inr rfl
        · exact absurd hWarm (by decide)
        · exact absurd hWarm (by decide)
      rcases hSite with rfl | rfl
      · have hTail : loaderShuffleTail 1348 (reuseArrival 0) = 32 := by kernel_rfl
        have hRem : cacheRoundRemaining false (reuseArrival 0) = 2 := by kernel_rfl
        change _ + loaderShuffleTail 1348 (reuseArrival 0) = _ at hTotal
        change _ + cacheRoundRemaining false (reuseArrival 0) = _ at hUse
        rw [hTail] at hTotal
        rw [hRem] at hUse
        omega
      · have hTail : loaderShuffleTail 1348 (reuseArrival 1) = 0 := by kernel_rfl
        have hRem : cacheRoundRemaining false (reuseArrival 1) = 1 := by kernel_rfl
        change _ + loaderShuffleTail 1348 (reuseArrival 1) = _ at hTotal
        change _ + cacheRoundRemaining false (reuseArrival 1) = _ at hUse
        rw [hTail] at hTotal
        rw [hRem] at hUse
        omega
    · have h : 1353 ≤ reuseArrival site := hAfter
      omega
  · have hAll : ∀ s : Fin 4, ¬ reuseArrival s < 1348 → 1396 ≤ reuseArrival s := by decide
    have hPc : 1396 ≤ reuseArrival site := hAll site hWarm
    have hLate : reuseArrival site < 1744 := by fin_cases site <;> decide
    obtain ⟨b, hb', hLo', hHi', hObs⟩ := actualSteadyCacheProjectionOrAfter hp hX hg hw hl
      writes hCTA he hPc (.inl hLate) hSafe
    have hSame := (hUnique b ⟨hb', hLo', hHi'⟩).trans (hUnique batch ⟨hb, hLo, hHi⟩).symm
    subst b
    rcases hObs with ⟨_, round, hNine, _, hUse, hTotal⟩ | ⟨hAfter, _⟩
    · have hSite : site = 2 ∨ site = 3 := by
        fin_cases site
        · exact absurd (show reuseArrival 0 < 1348 by decide) hWarm
        · exact absurd (show reuseArrival 1 < 1348 by decide) hWarm
        · exact .inl rfl
        · exact .inr rfl
      rcases hSite with rfl | rfl
      · have hTail : loaderShuffleTail 1741 (reuseArrival 2) = 32 := by kernel_rfl
        have hRem : cacheRoundRemaining true (reuseArrival 2) = 2 := by kernel_rfl
        change _ + loaderShuffleTail 1741 (reuseArrival 2) = _ at hTotal
        change _ + cacheRoundRemaining true (reuseArrival 2) = _ at hUse
        rw [hTail] at hTotal
        rw [hRem] at hUse
        omega
      · have hTail : loaderShuffleTail 1741 (reuseArrival 3) = 0 := by kernel_rfl
        have hRem : cacheRoundRemaining true (reuseArrival 3) = 1 := by kernel_rfl
        change _ + loaderShuffleTail 1741 (reuseArrival 3) = _ at hTotal
        change _ + cacheRoundRemaining true (reuseArrival 3) = _ at hUse
        rw [hTail] at hTotal
        rw [hRem] at hUse
        omega
    · have h : 1744 ≤ reuseArrival site := hAfter
      omega

/-- A loader lane that has performed at most `32 * use` shuffles after the priming search
and publishes nothing from `pos` on has published only ring positions below `use`. -/
theorem recurringUsesBelowOfShuffleRank {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X)
    {g lane pos batch use : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hl : lane < 32)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hRank : ((X.tr (warpLane l g lane)).take pos).countP Execution.isShfl ≤
      primingSearchShuffleCount batch + 32 * use)
    (hQuiet : ∀ j ≥ pos, ∀ loc, ¬ X.AsyncArrive (warpLane l g lane,j) loc true) :
    Protocol.Loader.RecurringUsesBelow X (warpLane l g lane) use := by
  intro j e he hMark
  have hj : j < pos := by
    by_contra! h
    obtain ⟨site,loc,rfl⟩ := (recurringPublicationMark_iff e).mp hMark
    exact hQuiet j h loc ⟨_,he⟩
  have hShuffles := recurringPublicationShuffleRank hp hX hFrame hg hw hl hb hLo hHi he hMark
  have hMono := countP_take_mono Execution.isShfl (X.tr (warpLane l g lane)) hj.le
  omega

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
