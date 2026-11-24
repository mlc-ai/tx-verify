-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderCachePublicationRank
public import Kernels.TmlFa4Fwd.Proof.LoaderSteadyRoundEntry
public import Kernels.TmlFa4Fwd.Proof.OutputFrame
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderCopyOverlap
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingSources
import Kernels.TmlFa4Fwd.Proof.LoaderActivePrefixSelect
import Kernels.TmlFa4Fwd.Proof.LoaderCopyPrefixGeometry
import Kernels.TmlFa4Fwd.Proof.LoaderWarmRoundEntry
import Kernels.TmlFa4Fwd.Proof.LoaderWarmIterationCursor
import Kernels.TmlFa4Fwd.Proof.LoaderSteadyIterationCursor
import Lemmas.Flow.NthEv
import Lemmas.Flow.CountTake

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Flow PTX.Proof Epilogue Prologue
open PTX.Kernels.TmlFa4Fwd.Loader
  (reuseArrival loaderShuffleTail primingSearchShuffleCount actualWarmEventRound
    actualSteadyEventRound warmFirstIterationOfEventRanked warmStartFrame
    loaderPipelineCutOp steadySeedOfEvent steadyCacheFrame observedSteadyTrips HasWarmTile
    warmProjectionsRoundOrExit steadyProjectionsRoundOrExit ringShapeOfAt
    actualCopyAtInLoader loaderCopyPcInPacket packetCopyCoordinates packetPlanePc
    recurringPacketSite kCopyPc vCopyPc loaderOwnPrefixEventRequiresActiveTile)

noncomputable section

set_option maxRecDepth 100000 in
private theorem recurringPublicationShuffleFloor {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g lane index batch : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hl : lane < 32)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    {e : Event} (he : X.get (warpLane l g lane, index) = some e)
    (hMark : recurringPublicationMark e = true) :
    (if e.pc < 1348 then primingSearchShuffleCount batch + 96
      else primingSearchShuffleCount batch + 672) ≤
      ((X.tr (warpLane l g lane)).take index).countP Execution.isShfl := by
  obtain ⟨site, loc, rfl⟩ := (recurringPublicationMark_iff e).mp hMark
  have hSafe : ∀ f, Kind.asyncArrive loc true ≠ .ub f := fun _ h => by cases h
  obtain ⟨_, _, hUnique⟩ := tileBatch_existsUnique p hCTA
  by_cases hWarm : (⟨reuseArrival site, .asyncArrive loc true⟩ : Event).pc < 1348
  · have hPc : 917 ≤ reuseArrival site := by fin_cases site <;> decide
    obtain ⟨b, hb', hLo', hHi', iteration, _, hCount⟩ :=
      actualWarmEventRound hp hX hg hw hl writes hCTA he ⟨hPc, hWarm⟩ hSafe
    have hSame := (hUnique b ⟨hb', hLo', hHi'⟩).trans
      (hUnique batch ⟨hb, hLo, hHi⟩).symm
    subst b
    have hRemaining : loaderShuffleTail 1348 (reuseArrival site) ≤ 32 := by
      fin_cases site <;> set_option maxRecDepth 100000 in decide +kernel
    rw [ite_eq_left hWarm]
    change _ + loaderShuffleTail 1348 (reuseArrival site) = _ at hCount
    omega
  · have hPc : 1396 ≤ reuseArrival site ∧ reuseArrival site < 1741 := by
      change ¬ reuseArrival site < 1348 at hWarm
      fin_cases site <;> first | contradiction | decide
    obtain ⟨b, hb', hLo', hHi', _, iteration, hIter, _, hCount⟩ :=
      actualSteadyEventRound hp hX hg hw hl writes hCTA he hPc hSafe
    have hSame := (hUnique b ⟨hb', hLo', hHi'⟩).trans
      (hUnique batch ⟨hb, hLo, hHi⟩).symm
    subst b
    have hRemaining : loaderShuffleTail 1741 (reuseArrival site) ≤ 32 := by
      change ¬ reuseArrival site < 1348 at hWarm
      fin_cases site <;> first | contradiction | set_option maxRecDepth 100000 in decide +kernel
    rw [ite_eq_right hWarm]
    change _ + loaderShuffleTail 1741 (reuseArrival site) = _ at hCount
    omega

/-- An issuing lane before its first warm traversal has crossed only the
priming K/V pair. This follows from the actual recurring publication ranks. -/
theorem firstWarmUseOfShuffleRank {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g lane pos batch : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hl : lane < 32)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hRank : ((X.tr (warpLane l g lane)).take pos).countP Execution.isShfl =
      primingSearchShuffleCount batch + 64) :
    recurringUseBefore X (warpLane l g lane, pos) = 2 := by
  dsimp only [recurringUseBefore]
  have hNo : ((X.tr (warpLane l g lane)).take pos).countP recurringPublicationMark = 0 := by
    by_contra! hPositive
    obtain ⟨j, e, hj, he, hMark, _⟩ :=
      exists_nthEv (X := X) (p := recurringPublicationMark) (g := warpLane l g lane)
        (k := pos) (n := 0) (by omega)
    have hFloor := recurringPublicationShuffleFloor hp hX hg hw hl writes hCTA hb hLo hHi he hMark
    have hEarlier := countP_take_mono Execution.isShfl (X.tr (warpLane l g lane)) hj.le
    rw [hRank] at hEarlier
    split at hFloor <;> omega
  rw [hNo]

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g lane index : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hl : lane < 32)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads) {e : Event}
include hp hX hg hw hl writes hCTA

set_option maxRecDepth 100000 in
/-- Recover the exact cache publication and warp shuffle ranks of the observed warm
round or the complete warm prefix. Both ranks come from a single recorded replay. -/
theorem actualWarmCacheProjectionOrAfter (he : X.get (warpLane l g lane, index) = some e)
    (hPc : 917 ≤ e.pc) (hMustWarm : e.pc < 1353 ∨ HasWarmTile p l g) (hSafe : ∀ f, e.kind ≠ .ub f) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch+1) * p.heads ∧
      let trips := Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1
      let thread := warpLane l g lane
      ((917 ≤ e.pc ∧ e.pc < 1348) ∧ ∃ round < min (trips-1) 9,
        recurringUseBefore X (thread,index) + cacheRoundRemaining false e.pc = 2*(round+2) ∧
        ((X.tr thread).take index).countP Execution.isShfl + loaderShuffleTail 1348 e.pc =
          primingSearchShuffleCount batch + 64 + 64*(round+1)) ∨
      (1353 ≤ e.pc ∧ ∃ pos ≤ index,
        recurringUseBefore X (thread,pos) = 2*(min (trips-1) 9+1) ∧
        ((X.tr thread).take pos).countP Execution.isShfl =
          primingSearchShuffleCount batch + 64 + 64*min (trips-1) 9) := by
  obtain ⟨batch, hb, hLo, hHi, hTwo, pos, hStart, s, ending, hs, hRun, hRank⟩ :=
    warmFirstIterationOfEventRanked hp hX hg hw hl writes hCTA he hPc hMustWarm hSafe
  have hUse := firstWarmUseOfShuffleRank hp hX hg hw hl writes hCTA hb hLo hHi hRank
  let co := assignedCoordinates p batch (g / l.block)
  let thread := warpLane l g lane
  let trips := Mma.trips p batch co.1
  let F := (1116, b32 (trips - 2)) :: warmStartFrame p l batch (co.2 / 6) trips
    (warpIndex l g) (thread % l.block)
  let warp : Fin 2 := ⟨warpIndex l g - 14, by have := warpIndex_lt hp g; omega⟩
  have hWarp : 14 + warp.val = warpIndex l g := Nat.add_sub_of_le hw
  have hShared : (2535, b32 l.sharedBase) ∈ F := by simp [F, warmStartFrame]
  have hRole : (1062, b32 (14 + warp.val)) ∈ F := by simp [F, warmStartFrame, hWarp]
  obtain ⟨hTile, _⟩ := assignedCoordinates_valid hp hLo hHi
  have hTrips := (Mma.trips_bounds hp hb hTile).2.1
  change trips ≤ (p.kLength batch + 127) / 128 at hTrips
  have hKeyLen := (hp.lengths batch hb).2.2
  have hBound : trips - 1 < 2 ^ 31 := by omega
  have hFirst : 0 < min (trips - 1) 9 := by change 2 ≤ trips at hTwo; omega
  have hAt : At s 917 ([(7174, b32 0), (1091, b32 (trips - 1))] ++ F) :=
    hs.mono ⟨hs.2.2.2.2.1, holds_lookup hs.2.2.2.2 rfl, hs.2.2.2.2.2⟩
  have hBody (n : Nat) : ((kernel.code.drop 917).take (1348 - 917)).all
      (fun ins => loaderPipelineCutOp 917 1348 n ([7174, 1091] ++ F.map Prod.fst) ins.op) =
        true := by set_option maxRecDepth 100000 in kernel_rfl
  have hTail : ((kernel.code.drop 1348).take 4).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  refine ⟨batch,hb,hLo,hHi,?_⟩
  change 2+((X.tr thread).take pos).countP recurringPublicationMark = 2 at hUse
  change ((X.tr thread).take pos).countP Execution.isShfl = _ at hRank
  have hZero (shuffles : Bool) : cacheRoundProjection false shuffles 1348 = 0 :=
    cacheRoundProjectionStop false shuffles
  have hStep {t u evt} (hLo : 917 ≤ TState.pc t) (hHi : t.pc < 1348)
      (h : WStep kernel Assumptions.all l thread t evt u) (shuffles : Bool) :=
    cacheRoundProjectionStep false hLo hHi h shuffles
  rcases warmProjectionsRoundOrExit warp hBound hFirst hShared hRole hBody hTail
    (cacheRoundProjection false) cacheRoundMark hZero hStep hAt hRun he hStart hSafe with
    ⟨hWindow,round,_,hRound,hProjection⟩ | ⟨last,hLast,u,_,hu,huRun,hProjection⟩
  · have hPub := hProjection false
    have hShfl := hProjection true
    rw [show cacheRoundProjection false false 917 = 2 from cacheRoundProjectionStart false false]
      at hPub
    rw [show cacheRoundProjection false true 917 = 64 from cacheRoundProjectionStart false true]
      at hShfl
    change _ + cacheRoundRemaining false e.pc = _ at hPub
    change _ + loaderShuffleTail 1348 e.pc = _ at hShfl
    simp only [cacheRoundMark, Bool.false_eq_true, ↓reduceIte, Nat.sub_zero] at hPub hShfl
    refine .inl ⟨hWindow,round,hRound,?_,?_⟩
    · change 2+((X.tr thread).take index).countP recurringPublicationMark+
        cacheRoundRemaining false e.pc = 2*(round+2)
      omega
    · change ((X.tr thread).take index).countP Execution.isShfl+loaderShuffleTail 1348 e.pc =
        primingSearchShuffleCount batch+64+64*(round+1)
      omega
  · have hPub := hProjection false
    have hShfl := hProjection true
    rw [show cacheRoundProjection false false 917 = 2 from cacheRoundProjectionStart false false]
      at hPub
    rw [show cacheRoundProjection false true 917 = 64 from cacheRoundProjectionStart false true]
      at hShfl
    simp only [cacheRoundMark, Bool.false_eq_true, ↓reduceIte, Nat.sub_zero] at hPub hShfl
    have hMem : e ∈ (X.tr thread).drop last := by
      apply List.mem_of_getElem? (i := index-last)
      rw [List.getElem?_drop,Nat.add_sub_of_le hLast]
      exact he
    obtain ⟨v,hWalk⟩ := Mma.walkFromRun huRun
    have hFloor := (Epilogue.loaderWalkEventRange warp (by decide : 174 ≤ 1353)
      (by rw [hu.1]; decide) (ringShapeOfAt hu) hu.2.2.2.2
      (fun _ => by kernel_rfl) hWalk e hMem).1
    refine .inr ⟨hFloor,last,hLast,?_,?_⟩
    · change 2+((X.tr thread).take last).countP recurringPublicationMark =
        2*(min (trips-1) 9+1)
      omega
    · change ((X.tr thread).take last).countP Execution.isShfl =
        primingSearchShuffleCount batch+64+64*min (trips-1) 9
      omega

/-- Recover the cache publication and shuffle ranks of a warm round or the
complete warm prefix. -/
theorem actualWarmCacheProjection (he : X.get (warpLane l g lane, index) = some e)
    (hPc : 917 ≤ e.pc) (hMustWarm : e.pc < 1353 ∨ HasWarmTile p l g) (hSafe : ∀ f, e.kind ≠ .ub f) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch+1) * p.heads ∧
      let trips := Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1
      let thread := warpLane l g lane
      ((917 ≤ e.pc ∧ e.pc < 1348) ∧ ∃ round < min (trips-1) 9,
        recurringUseBefore X (thread,index) + cacheRoundRemaining false e.pc = 2*(round+2) ∧
        ((X.tr thread).take index).countP Execution.isShfl + loaderShuffleTail 1348 e.pc =
          primingSearchShuffleCount batch + 64 + 64*(round+1)) ∨
      (∃ pos ≤ index,
        recurringUseBefore X (thread,pos) = 2*(min (trips-1) 9+1) ∧
        ((X.tr thread).take pos).countP Execution.isShfl =
          primingSearchShuffleCount batch + 64 + 64*min (trips-1) 9) := by
  obtain ⟨batch,hb,hLo,hHi,hRank⟩ :=
    actualWarmCacheProjectionOrAfter hp hX hg hw hl writes hCTA he hPc hMustWarm hSafe
  exact ⟨batch,hb,hLo,hHi,hRank.imp id And.right⟩

/-- An issued warm cache vector or publication uses one of the selected
request's initial nine recurring pairs. -/
theorem actualWarmCacheUseBound (he : X.get (warpLane l g lane, index) = some e)
    (hEvent : recurringVectorEvent e ∨ recurringPublicationMark e = true)
    (hPc : 917 ≤ e.pc ∧ e.pc < 1348) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      recurringUseBefore X (warpLane l g lane, index) <
        2 * (min (Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1 - 1) 9 + 1) := by
  have hSafe : ∀ fault, e.kind ≠ .ub fault := by
    rcases hEvent with ⟨_, _, _, _, rfl⟩ | hMark
    · exact fun _ h => by cases h
    · obtain ⟨_, _, rfl⟩ := (recurringPublicationMark_iff e).mp hMark
      exact fun _ h => by cases h
  obtain ⟨batch, hb, hLo, hHi, hTwo, pos, hStart, s, ending, hs, hRun, hRank⟩ :=
    warmFirstIterationOfEventRanked hp hX hg hw hl writes hCTA he hPc.1 (.inl (by omega)) hSafe
  have hUse := firstWarmUseOfShuffleRank hp hX hg hw hl writes hCTA hb hLo hHi hRank
  let co := assignedCoordinates p batch (g / l.block)
  let thread := warpLane l g lane
  let trips := Mma.trips p batch co.1
  let F := (1116, b32 (trips - 2)) :: warmStartFrame p l batch (co.2 / 6) trips
    (warpIndex l g) (thread % l.block)
  let warp : Fin 2 := ⟨warpIndex l g - 14, by have := warpIndex_lt hp g; omega⟩
  have hWarp : 14 + warp.val = warpIndex l g := Nat.add_sub_of_le hw
  have hShared : (2535, b32 l.sharedBase) ∈ F := by simp [F, warmStartFrame]
  have hRole : (1062, b32 (14 + warp.val)) ∈ F := by simp [F, warmStartFrame, hWarp]
  obtain ⟨hTile, _⟩ := assignedCoordinates_valid hp hLo hHi
  have hTrips := (Mma.trips_bounds hp hb hTile).2.1
  change trips ≤ (p.kLength batch + 127) / 128 at hTrips
  have hKeyLen := (hp.lengths batch hb).2.2
  have hBound : trips - 1 < 2 ^ 31 := by omega
  have hFirst : 0 < min (trips - 1) 9 := by change 2 ≤ trips at hTwo; omega
  have hAt : At s 917 ([(7174, b32 0), (1091, b32 (trips - 1))] ++ F) :=
    hs.mono ⟨hs.2.2.2.2.1, holds_lookup hs.2.2.2.2 rfl, hs.2.2.2.2.2⟩
  have hBody (n : Nat) : ((kernel.code.drop 917).take (1348 - 917)).all
      (fun ins => loaderPipelineCutOp 917 1348 n ([7174, 1091] ++ F.map Prod.fst) ins.op) =
        true := by set_option maxRecDepth 100000 in kernel_rfl
  have hTail : ((kernel.code.drop 1348).take 4).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hCap := warmCacheUseBoundOfEntry warp hBound hFirst hShared hRole hBody hTail hAt hRun
    hUse he hStart hEvent hPc.1 hPc.2
  exact ⟨batch, hb, hLo, hHi, hCap⟩

omit hp hX hg hw hl writes hCTA in
/-- The steady counter starts after at most nine warm pairs and the two
opening packets. No steady publication precedes its first traversal. -/
theorem firstSteadyUseBoundOfShuffleRank {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g lane pos batch : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hl : lane < 32)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hRank : ((X.tr (warpLane l g lane)).take pos).countP Execution.isShfl =
      primingSearchShuffleCount batch + 640) :
    recurringUseBefore X (warpLane l g lane, pos) ≤ 20 := by
  by_contra! hLarge
  dsimp only [recurringUseBefore] at hLarge
  obtain ⟨j, e, hj, he, hMark, hCount⟩ :=
    exists_nthEv (X := X) (p := recurringPublicationMark) (g := warpLane l g lane)
      (k := pos) (n := 18) (by omega)
  by_cases hWarm : e.pc < 1348
  · have hPc : 917 ≤ e.pc := by
      obtain ⟨site, loc, rfl⟩ := (recurringPublicationMark_iff e).mp hMark
      change 917 ≤ reuseArrival site
      fin_cases site <;> decide
    obtain ⟨b, hB, hBefore, hAfter, hBound⟩ :=
      actualWarmCacheUseBound hp hX hg hw hl writes hCTA he (.inr hMark) ⟨hPc, hWarm⟩
    dsimp only [recurringUseBefore] at hBound
    have hMin := Nat.min_le_right (Mma.trips p b (assignedCoordinates p b (g / l.block)).1 - 1) 9
    omega
  · have hFloor := recurringPublicationShuffleFloor hp hX hg hw hl writes hCTA hb hLo hHi
      he hMark
    have hBefore := countP_take_mono Execution.isShfl (X.tr (warpLane l g lane)) hj.le
    rw [ite_eq_right hWarm] at hFloor
    omega

/-- A steady ordinary copy is issued within the actual scheduled request's
K/V extent, including before its own packet has published. -/
theorem actualSteadyCopyUseBound (he : X.get (warpLane l g lane, index) = some e)
    (hCopy : recurringVectorEvent e) (hPc : 1396 ≤ e.pc ∧ e.pc < 1741) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      recurringUseBefore X (warpLane l g lane, index) <
        2 * Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1 := by
  have hSafe : ∀ fault, e.kind ≠ .ub fault := by
    obtain ⟨_, _, _, _, rfl⟩ := hCopy
    exact fun _ h => by cases h
  obtain ⟨batch, hb, hLo, hHi, hMany⟩ :=
    observedSteadyTrips hp hX hg hw hl writes hCTA he
      ⟨by have := hPc.1; omega, by have := hPc.2; omega⟩ hSafe
  obtain ⟨hBound, pos, hOrder, s, ending, hs, hRun, hRank⟩ :=
    steadySeedOfEvent hp hX hg hw hl writes hCTA hb hLo hHi hMany he hPc.1 hSafe
  have hUse := firstSteadyUseBoundOfShuffleRank hp hX hg hw hl writes hCTA hb hLo hHi hRank
  let co := assignedCoordinates p batch (g / l.block)
  let thread := warpLane l g lane
  let trips := Mma.trips p batch co.1
  let F := steadyCacheFrame p l batch (co.2 / 6) trips (warpIndex l g) (thread % l.block)
  let warp : Fin 2 := ⟨warpIndex l g - 14, by have := warpIndex_lt hp g; omega⟩
  have hWarp : 14 + warp.val = warpIndex l g := Nat.add_sub_of_le hw
  have hShared : (2535, b32 l.sharedBase) ∈ F := by simp [F, steadyCacheFrame, warmStartFrame]
  have hRole : (1062, b32 (14 + warp.val)) ∈ F := by
    simp [F, steadyCacheFrame, warmStartFrame, hWarp]
  change 11 ≤ trips at hMany
  change 128 * (trips - 2) + 127 < 2 ^ 31 at hBound
  have hFit : trips - 1 < 2 ^ 31 := by omega
  have hInit : 9 < trips - 1 := by omega
  have hBody (n : Nat) : ((kernel.code.drop 1396).take (1741 - 1396)).all
      (fun ins => loaderPipelineCutOp 1396 1741 n ([7181, 1091] ++ F.map Prod.fst) ins.op) =
        true := by set_option maxRecDepth 100000 in kernel_rfl
  have hTail : ((kernel.code.drop 1741).take 2).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hCap := steadyCopyUseBoundOfEntry warp hFit hInit hShared hRole hBody hTail hs hRun
    hUse he hOrder hCopy hPc.1 hPc.2
  refine ⟨batch, hb, hLo, hHi, ?_⟩
  simpa only [Nat.sub_add_cancel (show 1 ≤ trips by omega)] using hCap

omit hp hX hg hw hl writes hCTA in
set_option maxRecDepth 100000 in
/-- The same actual steady prefix has completed exactly nine warm K/V pairs. -/
theorem firstSteadyUseExact {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g lane pos index batch : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hl : lane < 32)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch+1)*p.heads)
    (hMany : 11 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    {e : Event} (he : X.get (warpLane l g lane,index) = some e)
    (hPc : 1396 ≤ e.pc) (hSafe : ∀ f, e.kind ≠ .ub f)
    {s : TState} {ending : Option TState}
    (hs : At s 1396 [(2535,b32 l.sharedBase),(1062,b32 (warpIndex l g))])
    (hRun : Run kernel Assumptions.all l (warpLane l g lane) s
      ((X.tr (warpLane l g lane)).drop pos) ending)
    (hRank : ((X.tr (warpLane l g lane)).take pos).countP Execution.isShfl =
      primingSearchShuffleCount batch+640) :
    recurringUseBefore X (warpLane l g lane,pos) = 20 := by
  let thread := warpLane l g lane
  have hUpper := firstSteadyUseBoundOfShuffleRank hp hX hg hw hl writes hCTA hb hLo hHi hRank
  obtain ⟨b,hb',hLo',hHi',hWarm⟩ := actualWarmCacheProjection hp hX hg hw hl writes hCTA
    he (by omega) (.inr ⟨batch,hb,hLo,hHi,by omega⟩) hSafe
  obtain ⟨_,_,hUnique⟩ := tileBatch_existsUnique p hCTA
  have hBatch := (hUnique b ⟨hb',hLo',hHi'⟩).trans (hUnique batch ⟨hb,hLo,hHi⟩).symm
  subst b
  rcases hWarm with hHere | ⟨finish,_,hUse,hShfl⟩
  · exact (show False by have := hHere.1.2; omega).elim
  have hMin : min (Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1-1) 9 = 9 :=
    Nat.min_eq_right (by omega)
  rw [hMin] at hUse hShfl
  let warp : Fin 2 := ⟨warpIndex l g-14,by have := warpIndex_lt hp g; omega⟩
  have hWarp : 14+warp.val = warpIndex l g := Nat.add_sub_of_le hw
  obtain ⟨v,hWalk⟩ := Mma.walkFromRun hRun
  have hFloor {i : Nat} {ev : Event} (hAfter : pos ≤ i)
      (hGet : X.get (thread,i) = some ev) : 1396 ≤ ev.pc := by
    have hMem : ev ∈ (X.tr thread).drop pos := by
      apply List.mem_of_getElem? (i := i-pos)
      rw [List.getElem?_drop,Nat.add_sub_of_le hAfter]
      exact hGet
    exact (Epilogue.loaderWalkEventRange warp (by decide : 174 ≤ 1396)
      (by rw [hs.1]; decide) (ringShapeOfAt hs) (by rw [hWarp]; exact hs.2.2.2.2)
      (fun _ => by kernel_rfl) hWalk ev hMem).1
  have hLower : 20 ≤ recurringUseBefore X (thread,pos) := by
    have hCount : 17 < ((X.tr thread).take finish).countP recurringPublicationMark := by
      change 2+((X.tr thread).take finish).countP recurringPublicationMark = 2*(9+1) at hUse
      omega
    obtain ⟨i,ev,hEarlier,hGet,hMark,hOrd⟩ :=
      exists_nthEv (X := X) (p := recurringPublicationMark) (g := thread)
        (k := finish) (n := 17) hCount
    have hBefore : i < pos := by
      by_contra! hAfter
      have hPc' := hFloor hAfter hGet
      have hShflFloor := recurringPublicationShuffleFloor hp hX hg hw hl writes hCTA hb hLo hHi
        hGet hMark
      rw [ite_eq_right (show ¬ ev.pc < 1348 by omega)] at hShflFloor
      change primingSearchShuffleCount batch+672 ≤
        ((X.tr thread).take i).countP Execution.isShfl at hShflFloor
      change ((X.tr thread).take finish).countP Execution.isShfl =
        primingSearchShuffleCount batch+64+64*9 at hShfl
      have hLe := countP_take_mono Execution.isShfl (X.tr thread) hEarlier.le
      omega
    have hGrow := countP_take_succ (p := recurringPublicationMark) hGet hMark
    have hLe := countP_take_mono recurringPublicationMark (X.tr thread)
      (show i+1 ≤ pos by omega)
    change ((X.tr thread).take (i+1)).countP recurringPublicationMark =
      ((X.tr thread).take i).countP recurringPublicationMark+1 at hGrow
    change ((X.tr thread).take i).countP recurringPublicationMark = 17 at hOrd
    change 20 ≤ 2+((X.tr thread).take pos).countP recurringPublicationMark
    omega
  exact Nat.le_antisymm hUpper hLower

set_option maxRecDepth 100000 in
/-- The actual steady loop ties the published ring use to the source's shuffle iteration. -/
theorem actualSteadyCacheProjectionOrAfter (he : X.get (warpLane l g lane, index) = some e)
    (hPc : 1396 ≤ e.pc)
    (hMustSteady : e.pc < 1744 ∨ ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ g/l.block ∧
      g/l.block < tilePrefix p (batch+1) * p.heads ∧
      11 ≤ Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1)
    (hSafe : ∀ f, e.kind ≠ .ub f) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ g/l.block ∧
      g/l.block < tilePrefix p (batch+1)*p.heads ∧
      let trips := Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1
      let thread := warpLane l g lane
      ((1396 ≤ e.pc ∧ e.pc < 1741) ∧ ∃ round, 9 ≤ round ∧ round < trips-1 ∧
        recurringUseBefore X (thread,index) + cacheRoundRemaining true e.pc = 2*(round+2) ∧
        ((X.tr thread).take index).countP Execution.isShfl + loaderShuffleTail 1741 e.pc =
          primingSearchShuffleCount batch+640+64*(round-9+1)) ∨
      (1744 ≤ e.pc ∧ ∃ pos ≤ index, ∃ s ending,
        s.pc = 1744 ∧ Run kernel Assumptions.all l thread s ((X.tr thread).drop pos) ending ∧
        recurringUseBefore X (thread,pos) = 2*trips) := by
  have hSelected := hMustSteady.elim
    (fun h => observedSteadyTrips hp hX hg hw hl writes hCTA he ⟨by omega,h⟩ hSafe) id
  obtain ⟨batch,hb,hLo,hHi,hMany⟩ := hSelected
  obtain ⟨hBound, pos, hOrder, s, ending, hs, hRun, hRank⟩ :=
    steadySeedOfEvent hp hX hg hw hl writes hCTA hb hLo hHi hMany he hPc hSafe
  let co := assignedCoordinates p batch (g / l.block)
  let thread := warpLane l g lane
  let trips := Mma.trips p batch co.1
  let F := steadyCacheFrame p l batch (co.2 / 6) trips (warpIndex l g) (thread % l.block)
  let warp : Fin 2 := ⟨warpIndex l g - 14, by have := warpIndex_lt hp g; omega⟩
  have hWarp : 14 + warp.val = warpIndex l g := Nat.add_sub_of_le hw
  have hShared : (2535, b32 l.sharedBase) ∈ F := by simp [F, steadyCacheFrame, warmStartFrame]
  have hRole : (1062, b32 (14 + warp.val)) ∈ F := by
    simp [F, steadyCacheFrame, warmStartFrame, hWarp]
  change 11 ≤ trips at hMany
  change 128 * (trips - 2) + 127 < 2 ^ 31 at hBound
  have hFit : trips - 1 < 2 ^ 31 := by omega
  have hInit : 9 < trips - 1 := by omega
  have hBody (n : Nat) : ((kernel.code.drop 1396).take (1741 - 1396)).all
      (fun ins => loaderPipelineCutOp 1396 1741 n ([7181, 1091] ++ F.map Prod.fst) ins.op) =
        true := by set_option maxRecDepth 100000 in kernel_rfl
  have hTail : ((kernel.code.drop 1741).take 2).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hState := hs.mono (G := [(2535,b32 l.sharedBase),(1062,b32 (warpIndex l g))])
    ⟨holds_mem hs.2.2.2.2.2.2 hShared,by
       rw [← hWarp]
       exact holds_mem hs.2.2.2.2.2.2 hRole,trivial⟩
  have hUse := firstSteadyUseExact hp hX hg hw hl writes hCTA hb hLo hHi hMany
    he hPc hSafe hState hRun hRank
  have hZero (shuffles : Bool) : cacheRoundProjection true shuffles 1741 = 0 :=
    cacheRoundProjectionStop true shuffles
  have hStep {t u evt} (hLo : 1396 ≤ TState.pc t) (hHi : t.pc < 1741)
      (h : WStep kernel Assumptions.all l thread t evt u) (shuffles : Bool) :=
    cacheRoundProjectionStep true hLo hHi h shuffles
  rcases steadyProjectionsRoundOrExit warp hFit hInit hShared hRole hBody hTail
    (cacheRoundProjection true) cacheRoundMark hZero hStep hs hRun he hOrder hSafe with
    ⟨hWindow,round,hRound,hRange,hProjection⟩ | ⟨last,hLast,u,stop,hu,huRun,hProjection⟩
  · have hPub := hProjection false
    have hShfl := hProjection true
    rw [show cacheRoundProjection true false 1396 = 2 from cacheRoundProjectionStart true false]
      at hPub
    rw [show cacheRoundProjection true true 1396 = 64 from cacheRoundProjectionStart true true]
      at hShfl
    change _ + cacheRoundRemaining true e.pc = _ at hPub
    change _ + loaderShuffleTail 1741 e.pc = _ at hShfl
    simp only [cacheRoundMark, Bool.false_eq_true, ↓reduceIte] at hPub hShfl
    change 2+((X.tr thread).take pos).countP recurringPublicationMark = 20 at hUse
    change ((X.tr thread).take pos).countP Execution.isShfl = _ at hRank
    refine ⟨batch,hb,hLo,hHi,.inl ⟨hWindow,round,hRound,hRange,?_,?_⟩⟩
    · change 2+((X.tr thread).take index).countP recurringPublicationMark+
        cacheRoundRemaining true e.pc = 2*(round+2)
      omega
    · change ((X.tr thread).take index).countP Execution.isShfl+loaderShuffleTail 1741 e.pc =
        primingSearchShuffleCount batch+640+64*(round-9+1)
      omega
  · have hMem : e ∈ (X.tr thread).drop last := by
      apply List.mem_of_getElem? (i := index-last)
      rw [List.getElem?_drop,Nat.add_sub_of_le hLast]
      exact he
    obtain ⟨v,hWalk⟩ := Mma.walkFromRun huRun
    have hFloor := (Epilogue.loaderWalkEventRange warp (by decide : 174 ≤ 1744)
      (by rw [hu.1]; decide) (ringShapeOfAt hu) hu.2.2.2.2
      (fun _ => by kernel_rfl) hWalk e hMem).1
    have hPub := hProjection false
    rw [show cacheRoundProjection true false 1396 = 2 from cacheRoundProjectionStart true false]
      at hPub
    simp only [cacheRoundMark, Bool.false_eq_true, ↓reduceIte] at hPub
    change 2+((X.tr thread).take pos).countP recurringPublicationMark = 20 at hUse
    refine ⟨batch,hb,hLo,hHi,.inr ⟨hFloor,last,hLast,u,stop,hu.1,huRun,?_⟩⟩
    change 2+((X.tr thread).take last).countP recurringPublicationMark = 2*trips
    omega

set_option maxRecDepth 100000 in
/-- Recover the publication and shuffle ranks of an actual event in the steady loop. -/
theorem actualSteadyCacheProjection (he : X.get (warpLane l g lane, index) = some e)
    (hPc : 1396 ≤ e.pc ∧ e.pc < 1741) (hSafe : ∀ f, e.kind ≠ .ub f) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ g/l.block ∧
      g/l.block < tilePrefix p (batch+1)*p.heads ∧
      let trips := Mma.trips p batch (assignedCoordinates p batch (g/l.block)).1
      let thread := warpLane l g lane
      ∃ round, 9 ≤ round ∧ round < trips-1 ∧
        recurringUseBefore X (thread,index) + cacheRoundRemaining true e.pc = 2*(round+2) ∧
        ((X.tr thread).take index).countP Execution.isShfl + loaderShuffleTail 1741 e.pc =
          primingSearchShuffleCount batch+640+64*(round-9+1) := by
  obtain ⟨batch,hb,hLo,hHi,hRank⟩ :=
    actualSteadyCacheProjectionOrAfter hp hX hg hw hl writes hCTA he
      hPc.1 (.inl (by have := hPc.2; omega)) hSafe
  rcases hRank with hRound | ⟨hAfter,_⟩
  · exact ⟨batch,hb,hLo,hHi,hRound.2⟩
  · have := hPc.2
    omega
end

set_option maxRecDepth 100000 in
/-- Every actual nonpriming cache copy uses a generation in its CTA's
selected launch request, with no requirement that the copy has completed. -/
theorem recurringCopyUseBound {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hFrame : OutputFootprint p X) {copy : EvId} {s : AsyncCopy.Spec}
    (hCopy : X.Copy copy s)
    (hKey : ∀ pair upper, ¬ PrimingKeyVector X copy pair upper s)
    (hValue : ∀ pair upper, ¬ PrimingValueVector X copy pair upper s) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ copy.1 / l.block ∧
      copy.1 / l.block < tilePrefix p (batch + 1) * p.heads ∧
      recurringUseBefore X copy <
        2 * Mma.trips p batch (assignedCoordinates p batch (copy.1 / l.block)).1 := by
  have hWarp := copyLoaderWarp hp hX hCopy
  obtain ⟨g, index⟩ := copy
  obtain ⟨pc, he⟩ := hCopy
  obtain ⟨hLo, hHi, hAt⟩ := actualCopyAtInLoader hX he
  obtain ⟨site, hBegin, hEnd⟩ := loaderCopyPcInPacket hLo hHi hAt
  obtain ⟨pair, upper, rfl⟩ := packetCopyCoordinates site hBegin hEnd hAt
  have hg : g < l.threads := event_thread_lt hX he
  let lane := laneOf l g
  have hLane : lane < 32 := Nat.mod_lt _ (by decide)
  have hSelf : warpLane l g lane = g := by
    unfold warpLane lane laneOf
    have hCta := Nat.mod_le g l.block
    have hWarp := Nat.mod_le (g % l.block) 32
    omega
  have warm (phase : Fin 4) (hSite : site = recurringPacketSite phase)
      (hWarm : phase.val < 2) :
      ∃ batch < p.batch, tilePrefix p batch * p.heads ≤ g / l.block ∧
        g / l.block < tilePrefix p (batch + 1) * p.heads ∧
        recurringUseBefore X (g, index) <
          2 * Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1 := by
    subst site
    have hPc : 917 ≤ packetPlanePc (recurringPacketSite phase) pair upper ∧
        packetPlanePc (recurringPacketSite phase) pair upper < 1348 := by
      have hAudit : ∀ (phase : Fin 4) (pair : Fin 16) (upper : Bool), phase.val < 2 →
          917 ≤ packetPlanePc (recurringPacketSite phase) pair upper ∧
          packetPlanePc (recurringPacketSite phase) pair upper < 1348 := by decide +kernel
      exact hAudit phase pair upper hWarm
    have hCTA : g / l.block < tilePrefix p p.batch * p.heads :=
      loaderOwnPrefixEventRequiresActiveTile hp hX hWarp
        (hp.cuQ_protected (fun _ _ _ _ => loaderOutputWrites hFrame)) he
        (show 297 < packetPlanePc (recurringPacketSite phase) pair upper by omega)
        (show packetPlanePc (recurringPacketSite phase) pair upper < 1862 by omega)
    have hEvent : X.get (warpLane l g lane, index) = _ := hSelf.symm ▸ he
    obtain ⟨batch, hb, hBegin, hEnd, hBound⟩ :=
      actualWarmCacheUseBound hp hX hg hWarp hLane
        (fun _ _ _ _ => loaderOutputWrites hFrame) hCTA hEvent
        (.inl ⟨phase, pair, upper, s, rfl⟩) hPc
    rw [hSelf] at hBound
    have hMin := Nat.min_le_left
      (Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1 - 1) 9
    have hTile := (assignedCoordinates_valid hp hBegin hEnd).1
    have hPositive := (Mma.trips_bounds hp hb hTile).1
    exact ⟨batch, hb, hBegin, hEnd, by omega⟩
  have steady (phase : Fin 4) (hSite : site = recurringPacketSite phase)
      (hSteady : 2 ≤ phase.val) :
      ∃ batch < p.batch, tilePrefix p batch * p.heads ≤ g / l.block ∧
        g / l.block < tilePrefix p (batch + 1) * p.heads ∧
        recurringUseBefore X (g, index) <
          2 * Mma.trips p batch (assignedCoordinates p batch (g / l.block)).1 := by
    subst site
    have hPc : 1396 ≤ packetPlanePc (recurringPacketSite phase) pair upper ∧
        packetPlanePc (recurringPacketSite phase) pair upper < 1741 := by
      have hAudit : ∀ (phase : Fin 4) (pair : Fin 16) (upper : Bool), 2 ≤ phase.val →
          1396 ≤ packetPlanePc (recurringPacketSite phase) pair upper ∧
          packetPlanePc (recurringPacketSite phase) pair upper < 1741 := by decide +kernel
      exact hAudit phase pair upper hSteady
    have hCTA : g / l.block < tilePrefix p p.batch * p.heads :=
      loaderOwnPrefixEventRequiresActiveTile hp hX hWarp
        (hp.cuQ_protected (fun _ _ _ _ => loaderOutputWrites hFrame)) he
        (show 297 < packetPlanePc (recurringPacketSite phase) pair upper by omega)
        (show packetPlanePc (recurringPacketSite phase) pair upper < 1862 by omega)
    have hEvent : X.get (warpLane l g lane, index) = _ := hSelf.symm ▸ he
    simpa only [hSelf] using actualSteadyCopyUseBound hp hX hg hWarp hLane
      (fun _ _ _ _ => loaderOutputWrites hFrame) hCTA hEvent ⟨phase, pair, upper, s, rfl⟩ hPc
  fin_cases site
  · apply (hKey pair upper ?_).elim
    have hPc : packetPlanePc 0 pair upper = kCopyPc pair + if upper then 1 else 0 := by
      fin_cases pair <;> cases upper <;> decide
    change X.get (g, index) = some ⟨kCopyPc pair + (if upper then 1 else 0), .copy s⟩
    rw [← hPc]
    exact he
  · apply (hValue pair upper ?_).elim
    have hPc : packetPlanePc 1 pair upper = vCopyPc pair + if upper then 1 else 0 := by
      fin_cases pair <;> cases upper <;> decide
    change X.get (g, index) = some ⟨vCopyPc pair + (if upper then 1 else 0), .copy s⟩
    rw [← hPc]
    exact he
  · exact warm 0 rfl (by decide)
  · exact warm 1 rfl (by decide)
  · exact steady 2 rfl (by decide)
  · exact steady 3 rfl (by decide)

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
