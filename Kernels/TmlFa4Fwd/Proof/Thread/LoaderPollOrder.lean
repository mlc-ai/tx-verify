-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.OutputFrame
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPendingCursor
public import Lemmas.Flow.PollSynced
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderActualCacheUseBound
import Kernels.TmlFa4Fwd.Proof.Thread.MbarOperands
import Kernels.TmlFa4Fwd.Proof.Thread.PollShuffleOrder
import Kernels.TmlFa4Fwd.Proof.LoaderActivePrefixSelect

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Loader
  (recurringEmptyWait loaderOwnPrefixEventRequiresActiveTile loaderShuffleTail
    primingSearchShuffleCount)

private def beforeWarmEnd (pc : Nat) : Bool := decide (pc < 1348)

private theorem recurringLoaderUseOfPoll {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X)
    {g n pc phase : Nat} {loc : Loc} {ok acq : Bool} {scope : MbarScope}
    (he : X.get (g,n) = some ⟨pc,.wait loc phase ok acq scope⟩)
    (hSite : ∃ site : Fin 4, pc = (recurringEmptyWait site).pc) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ g/l.block ∧
      g/l.block < tilePrefix p (batch+1) * p.heads ∧
      ∃ round,
        recurringUseBefore X (g,n) + cacheRoundRemaining (!beforeWarmEnd pc) pc = 2*(round+2) ∧
        ((X.tr g).take n).countP Execution.isShfl +
          loaderShuffleTail (if beforeWarmEnd pc then 1348 else 1741) pc =
          primingSearchShuffleCount batch +
            (if beforeWarmEnd pc then 64+64*(round+1) else 640+64*(round-9+1)) ∧
        (beforeWarmEnd pc = false → 9 ≤ round) := by
  let e : Event := ⟨pc,.wait loc phase ok acq scope⟩
  have hRead : X.get (g,n) = some e := he
  have hRange : 917 ≤ pc ∧ pc < 1741 ∧ (pc < 1348 ∨ 1396 ≤ pc) ∧
      pc ∉ registerHintSites := by
    obtain ⟨r,rfl⟩ := hSite
    fin_cases r <;> decide
  have hg := event_thread_lt hX hRead
  have hRole := roleBodyPcOfEvent hp hX hRead (show 173 < pc by omega) hRange.2.2.2
  have hw : 14 ≤ warpIndex l g := by
    change roleBodyPc (warpIndex l g) pc at hRole
    unfold roleBodyPc at hRole
    rcases hRole with h | h
    · omega
    · split_ifs at h <;> omega
  let lane := laneOf l g
  have hl : lane < 32 := Nat.mod_lt _ (by decide)
  have hLane : warpLane l g lane = g :=
    Nat.sub_add_cancel ((Nat.mod_le ..).trans (Nat.mod_le ..))
  have hWrites : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc :=
    fun _ _ _ _ => loaderOutputWrites hFrame
  have hCuQ := hp.cuQ_protected hWrites
  have hWork := loaderOwnPrefixEventRequiresActiveTile hp hX hw hCuQ hRead
    (show 297 < pc by omega) (show pc < 1862 by omega)
  have hGet : X.get (warpLane l g lane,n) = some e := hLane.symm ▸ hRead
  have hSafe : ∀ fault, e.kind ≠ .ub fault := fun _ h => by cases h
  by_cases hWarm : pc < 1348
  · obtain ⟨batch,hb,hLo,hHi,hRound⟩ := actualWarmCacheProjectionOrAfter hp hX hg hw hl
      hWrites hWork hGet hRange.1 (.inl (show pc < 1353 by omega)) hSafe
    rcases hRound with ⟨_,round,_,hUse,hRank⟩ | ⟨hAfter,_⟩
    · rw [hLane] at hUse hRank
      refine ⟨batch,hb,hLo,hHi,round,?_,?_,?_⟩
      · simpa [e,beforeWarmEnd,hWarm] using hUse
      · simpa [e,beforeWarmEnd,hWarm,Nat.add_assoc] using hRank
      · simp [beforeWarmEnd,hWarm]
    · change 1353 ≤ pc at hAfter
      omega
  · obtain ⟨batch,hb,hLo,hHi,round,hLower,_,hUse,hRank⟩ := actualSteadyCacheProjection hp hX
      hg hw hl hWrites hWork hGet ⟨show 1396 ≤ pc by omega,hRange.2.1⟩ hSafe
    rw [hLane] at hUse hRank
    refine ⟨batch,hb,hLo,hHi,round,?_,?_,fun _ => hLower⟩
    · simpa [e,beforeWarmEnd,hWarm] using hUse
    · simpa [e,beforeWarmEnd,hWarm,Nat.add_assoc] using hRank

/-- At a shared recurring loader poll site, equal warp shuffle ranks fix the logical
use. Unequal ranks give an order through the first unshared returned shuffle. -/
theorem recurringPollObjectsAgreeOrOrdered {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X)
    {g h i j pc phase phase' : Nat} {loc loc' : Loc} {ok ok' acq acq' : Bool}
    {scope scope' : MbarScope} (hWarp : SameWarp l g h)
    (he : X.get (g,i) = some ⟨pc,.wait loc phase ok acq scope⟩)
    (hf : X.get (h,j) = some ⟨pc,.wait loc' phase' ok' acq' scope'⟩)
    (hSite : ∃ site : Fin 4, pc = (recurringEmptyWait site).pc) :
    loc = loc' ∨ PollBefore l kernel X (g,i) (h,j) ∨ PollBefore l kernel X (h,j) (g,i) := by
  have hCta := hWarp.1.2.2
  rcases lt_trichotomy (((X.tr g).take i).countP Execution.isShfl)
      (((X.tr h).take j).countP Execution.isShfl) with hLess | hEqual | hGreater
  · exact .inr (.inl (pollBeforeOfShuffleCount hX hWarp he hf hLess))
  · obtain ⟨ba,hba,hLoa,hHia,ra,hUsea,hRankA,hSteadyA⟩ :=
      recurringLoaderUseOfPoll hp hX hFrame he hSite
    obtain ⟨bb,hbb,hLob,hHib,rb,hUseb,hRankB,hSteadyB⟩ :=
      recurringLoaderUseOfPoll hp hX hFrame hf hSite
    rw [← hCta] at hLob hHib
    obtain ⟨_,_,hBatch⟩ := tileBatch_existsUnique p (item := g/l.block)
      (lt_of_lt_of_le hHia (Nat.mul_le_mul_right _ (tilePrefix_mono p (by omega))))
    have hBatchEq := (hBatch ba ⟨hba,hLoa,hHia⟩).trans (hBatch bb ⟨hbb,hLob,hHib⟩).symm
    subst bb
    have hRound : ra = rb := by
      cases hb : beforeWarmEnd pc <;> simp only [hb,Bool.false_eq_true,↓reduceIte] at hRankA hRankB
      · have ha := hSteadyA hb
        have hb' := hSteadyB hb
        omega
      · omega
    have hUse : recurringUseBefore X (g,i) = recurringUseBefore X (h,j) := by omega
    obtain ⟨site,hPc⟩ := hSite
    obtain ⟨_,_,hPoll⟩ :=
      recurringPollOfCursor hp hX he ⟨site,loc,phase,ok,acq,scope,by rw [hPc]⟩
    obtain ⟨_,_,hPoll'⟩ :=
      recurringPollOfCursor hp hX hf ⟨site,loc',phase',ok',acq',scope',by rw [hPc]⟩
    have ha := (Kind.wait.inj (congrArg Event.kind hPoll)).1
    have hb := (Kind.wait.inj (congrArg Event.kind hPoll')).1
    rw [hCta,hUse] at ha
    exact .inl (ha.trans hb.symm)
  · exact .inr (.inr (pollBeforeOfShuffleCount hX (sameWarp_symm hWarp) hf he hGreater))

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
