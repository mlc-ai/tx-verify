-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderActivePrefixSelect
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKActive
import Kernels.TmlFa4Fwd.Flow.Code.Part008

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

private theorem ordinalAfterOrdinary {X : Execution} {g pos : Nat} {ordinary : List Event}
    (hTrace : (X.tr g).drop pos = ordinary ++ (X.tr g).drop (pos + ordinary.length))
    (hNoShuffle : ordinary.countP Execution.isShfl = 0) :
    ((X.tr g).take (pos + ordinary.length)).countP Execution.isShfl =
      ((X.tr g).take pos).countP Execution.isShfl := by
  rw [List.take_add, hTrace, List.take_append_length, List.countP_append, hNoShuffle, Nat.add_zero]

/-- The search consumes seven shuffles per later group, an optional selected
prefix, and the selected batch's tile-count shuffle. -/
def primingSearchShuffleCount (batch : Nat) : Nat :=
  (10 + 7 * (batch / 31) + if 31 * (batch / 31) < batch then 1 else 0) + 1

/-- Any active loader group admits its selected batch and KV geometry up to the
actual metadata reads, while retaining an observed downstream event. -/
private theorem loaderPrimingEntryOfActiveEventWithRoots {p : Params} {l : Launch}
    {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g src j : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hSrc : src < 32)
    (hProtected : ∀ i ≤ p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * i)).at k))
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    {target : Event} (he : X.get (warpLane l g src, j) = some target) (hPc : 308 < target.pc) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      ∃ ending, ∃ cur : SchedulerWarpAt l X g 381 (fun lane =>
        loaderActiveLaneFacts p l g batch lane ++ (primingKActiveAbi p l (warpIndex l g) ++
          warmLaneRoots l (warpLane l g lane % l.block)))
        (primingSearchShuffleCount batch) 1 ending,
        WarpFollowsEvent l X g cur.pos src j target := by
  obtain ⟨first, batch, hFirst, hLower, hGroup, hb, hLo, hHi, ending, chosen, hFollows⟩ :=
    loaderActiveBatchOfEvent hp hX hg hw hSrc hProtected hCTA he (by omega)
  subst first
  obtain ⟨pre, hPre⟩ :=
    loaderSelectedPrefixTo hp hX hg hLower hGroup hb chosen (.inr hFollows) (by omega)
  obtain ⟨coords, hCoords⟩ :=
    loaderSelectedCoordinatesTo hp hX hg hLower hGroup hb hLo hHi pre (.inr (hPre hFollows)) hPc
  obtain ⟨entry, hPosition⟩ :=
    primingKActiveEntryFromCoordinatesWithLaneRootsAt hp hb hLo hHi coords
  exact ⟨batch, hb, hLo, hHi, ending, entry, hPosition.symm ▸ hCoords (hPre hFollows)⟩

/-- Any active loader group admits its selected batch and KV geometry up to the
actual metadata reads, while retaining an observed downstream event. -/
theorem loaderPrimingEntryOfActiveEvent {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g src j : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hSrc : src < 32)
    (hProtected : ∀ i ≤ p.batch, ∀ k < 4, ∀ w a bs, X.MemWrites w a bs →
      ¬ a.Covers ((globalLoc (p.cuQBase + 4 * i)).at k))
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    {target : Event} (he : X.get (warpLane l g src, j) = some target) (hPc : 308 < target.pc) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      ∃ ending, ∃ cur : SchedulerWarpAt l X g 381 (fun lane =>
        loaderActiveLaneFacts p l g batch lane ++ primingKActiveAbi p l (warpIndex l g))
        (primingSearchShuffleCount batch) 1 ending,
        WarpFollowsEvent l X g cur.pos src j target := by
  obtain ⟨batch, hb, hLo, hHi, ending, cur, hFollows⟩ :=
    loaderPrimingEntryOfActiveEventWithRoots hp hX hg hw hSrc hProtected hCTA he hPc
  obtain ⟨out, hPos⟩ := cur.advanceLocalAt (pc' := 381)
    (G := fun lane => loaderActiveLaneFacts p l g batch lane ++
      primingKActiveAbi p l (warpIndex l g)) (fun lane hl =>
    let hAt := cur.checkpoint lane hl
    ⟨_, .refl, hAt.mono (by
      rw [← List.append_assoc] at hAt
      exact ((holds_append ..).mp hAt.2.2.2.2).1)⟩)
  exact ⟨batch, hb, hLo, hHi, ending, out, hPos.symm ▸ hFollows⟩

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g src j : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hSrc : src < 32)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads) {target : Event}
    (he : X.get (warpLane l g src, j) = some target)
include hp hX hg hw hSrc writes hCTA he

/-- The active source lane reads its exact CuQ and UsedK from the launch before an
observed copy; the actual suffix and selected arithmetic frame continue to the copy. -/
theorem loaderPrimingMetadataOfActiveEventWithRoots (hPc : 385 < target.pc) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      let co := assignedCoordinates p batch (g / l.block)
      ∃ pos ≤ j, ∃ t ending,
        At t 386 (primingKActiveFacts p l batch co.2 co.1 (warpIndex l g) src ++
          ((7170, b32 batch) :: warmLaneRoots l (warpLane l g src % l.block))) ∧
        Run kernel Assumptions.all l (warpLane l g src) t
          ((X.tr (warpLane l g src)).drop pos) ending ∧
        ((X.tr (warpLane l g src)).take pos).countP Execution.isShfl =
          primingSearchShuffleCount batch := by
  obtain ⟨batch, hIn, hLo, hHi, _, cur, hFollows⟩ :=
    loaderPrimingEntryOfActiveEventWithRoots hp hX hg hw hSrc (hp.cuQ_protected writes)
      hCTA he (by omega)
  have hb := hIn
  have hTile := (assignedCoordinates_valid hp hLo hHi).1
  have hExtra : ActiveReadExtra (primingKActiveAbi p l (warpIndex l g) ++
      warmLaneRoots l (warpLane l g src % l.block)) := by
    constructor
    · simp [primingKActiveAbi, warmLaneRoots, addressCacheInputs]
    · simp [primingKActiveAbi, warmLaneRoots, addressCacheInputs]
    · simp [primingKActiveAbi, warmLaneRoots, addressCacheInputs]
    · set_option maxRecDepth 100000 in kernel_rfl
  obtain ⟨t, hEvents, hRun, hAt⟩ :=
    primingKActiveLaneMetadataWithExtra hp hX hg hb hSrc hTile writes hExtra cur
      (.inr ⟨j, target, hFollows.before, hPc, he⟩)
  have hOrd := (ordinalAfterOrdinary hEvents rfl).trans (cur.ordinals.shfl src hSrc)
  refine ⟨batch, hIn, hLo, hHi, cur.pos src + 3, ?_, t, _, hAt, hRun, hOrd⟩
  by_contra hAfter
  let offset := j - cur.pos src
  have hSize : offset < (activeMetadataEvents p batch).length := by
    change offset < 3
    have := hFollows.before
    dsimp [offset]
    omega
  have hAbsolute : cur.pos src + offset = j := Nat.add_sub_of_le hFollows.before
  have hGet : ((X.tr (warpLane l g src)).drop (cur.pos src))[offset]? = some target := by
    rw [List.getElem?_drop, hAbsolute]
    exact he
  rw [hEvents, List.getElem?_append_left hSize] at hGet
  have hLt : offset < 3 := hSize
  interval_cases offset <;> simp [activeMetadataEvents] at hGet <;> subst target
  · change 385 < 381 at hPc; omega
  · change 385 < 382 at hPc; omega
  · change 385 < 385 at hPc; omega

/-- The active source lane reads its exact CuQ and UsedK from the launch before an
observed copy; the actual suffix and selected arithmetic frame continue to the copy. -/
theorem loaderPrimingMetadataOfActiveEvent (hPc : 385 < target.pc) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      let co := assignedCoordinates p batch (g / l.block)
      ∃ pos ≤ j, ∃ t ending,
        At t 386 (primingKActiveFacts p l batch co.2 co.1 (warpIndex l g) src) ∧
        Run kernel Assumptions.all l (warpLane l g src) t
          ((X.tr (warpLane l g src)).drop pos) ending ∧
        ((X.tr (warpLane l g src)).take pos).countP Execution.isShfl =
          primingSearchShuffleCount batch := by
  obtain ⟨batch, hb, hLo, hHi, pos, hBefore, t, ending, hT, hRun, hOrd⟩ :=
    loaderPrimingMetadataOfActiveEventWithRoots hp hX hg hw hSrc writes hCTA he hPc
  exact ⟨batch, hb, hLo, hHi, pos, hBefore, t, ending,
    hT.mono ((holds_append ..).mp hT.2.2.2.2).1, hRun, hOrd⟩

/-- An observed priming vector fixes the first scratch row of the issuing lane. -/
theorem loaderPrimingScratchOfActiveEvent (hPc : 385 < target.pc) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      let co := assignedCoordinates p batch (g / l.block)
      let tile := Mma.trips p batch co.1 - 1
      128 * tile + 127 < 2 ^ 31 ∧
      ∃ pos ≤ j, ∃ t ending,
        At t 488 (primingKInitialScratchFacts p l batch (co.2 / 6) tile (warpIndex l g) src) ∧
        Run kernel Assumptions.all l (warpLane l g src) t
          ((X.tr (warpLane l g src)).drop pos) ending ∧
        ((X.tr (warpLane l g src)).take pos).countP Execution.isShfl =
          primingSearchShuffleCount batch := by
  obtain ⟨batch, hIn, hLo, hHi, pos, hPos, t, ending, hAt, hRun, hOrd⟩ :=
    loaderPrimingMetadataOfActiveEvent hp hX hg hw hSrc writes hCTA he hPc
  obtain ⟨hTile, hHead⟩ := assignedCoordinates_valid hp hLo hHi
  have hb := hIn
  obtain ⟨a, hA, ha⟩ := primingKActiveToAddressLane hp hb hTile hAt
  obtain ⟨b, hB, hb'⟩ := primingKAddressToVisibleLane hp hb (hHead.trans hp.heads_signed) hTile ha
  obtain ⟨c, hC, hc⟩ := primingKTripSeedLane hp hb hTile hb'
  obtain ⟨hLast, d, hD, hd⟩ := primingKEnterScratchLane hp hb hTile hc
  have hMore : (X.tr (warpLane l g src)).drop pos ≠ [] := by
    intro hEmpty
    exact Nat.not_le_of_lt (List.getElem?_eq_some_iff.mp he).1
      ((List.drop_eq_nil_iff.mp hEmpty).trans hPos)
  exact ⟨batch, hIn, hLo, hHi, hLast, pos, hPos, d, ending, hd,
    hRun.after_local_nonempty (hA.trans (hB.trans (hC.trans hD))) hMore, hOrd⟩
end

/-- The active priming issuer initializes both saved scratch rows and returns
from the actual parity-one K wait before a witnessed downstream event. -/
theorem loaderPrimingPreparedOfActiveEvent {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g src j bound : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hSrc : src < 32)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    {target : Event} (he : X.get (warpLane l g src, j) = some target)
    (hBound : 517 ≤ bound) (hPc : bound < target.pc) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      let co := assignedCoordinates p batch (g / l.block)
      let tile := Mma.trips p batch co.1 - 1
      let warp := warpIndex l g
      let thread := warpLane l g src
      let row := primingLaneRow tile (32 * warp + src)
      128 * tile + 127 < 2 ^ 31 ∧
      ∃ pos t ending,
        At t 520 (primingKPackFrame p l batch (co.2 / 6) tile warp src) ∧
        Run kernel Assumptions.all l thread t ((X.tr thread).drop pos) ending ∧
        PrefixDemand X thread pos bound ending ∧
        ((X.tr thread).take pos).countP Execution.isShfl =
          primingSearchShuffleCount batch ∧
        ∀ slot : Fin 2, PrimingMetadataAt p l X thread pos batch (row + 64 * slot.val) slot := by
  obtain ⟨batch, hIn, hLo, hHi, hTile, pos, hBefore, t, ending, hAt, hRun, hOrd⟩ :=
    loaderPrimingScratchOfActiveEvent hp hX hg hw hSrc writes hCTA he (by omega)
  have hb := hIn
  obtain ⟨n, u, hFront, hu, hRest, hDemand, hMetadata⟩ :=
    primingKPreparedLaneFromScratch hp hX hb hTile writes hAt hRun hBound
      (.inr ⟨j, target, hBefore, hPc, he⟩)
  have hNext := (ordinalAfterOrdinary hFront (primingKPrepEvents_noShuffle ..)).trans hOrd
  exact ⟨batch, hIn, hLo, hHi, hTile, _, u, ending, hu, hRest, hDemand, hNext, hMetadata⟩

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g batch head tile warp lane index bound : Nat}
    (hb : batch < p.batch) (hh : head < p.kvHeads) (hTile : 128 * tile + 127 < 2 ^ 31)
    (hBound : 543 ≤ bound) {s : TState} {ending : Option TState}
    (hs : At s 538 (primingKMaskInputs p l batch tile warp lane))
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    (hDemand : PrefixDemand X g index bound ending)
    (hStored : PrimingCellValue X g index 534 (sourceScratchAccess l g 0)
      (b64 (primingKRowPointer p batch head (primingLaneRow tile (32 * warp + lane)))).toBytes)
include hp hX hb hh hTile hBound hs hr hDemand hStored

/-- Decode the first K pointer from its latest saved row and retain both actual words. -/
theorem primingKLoadedLaneInPrefixObserved :
    let bases := fun lane =>
      primingKRowPointer p batch head (primingLaneRow tile (32 * warp + lane))
    ∃ u, At u 544 (primingKSourceInputs p l batch tile warp bases lane) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (index + 2)) ending ∧
      PrefixDemand X g (index + 2) bound ending ∧
      ((X.tr g).take (index + 2)).countP Execution.isShfl =
        ((X.tr g).take index).countP Execution.isShfl ∧
      ∃ a bytes, X.get (g, index) = some ⟨543, .rd a bytes⟩ := by
  dsimp only
  let tid := 32 * warp + lane
  let row := primingLaneRow tile tid
  let base := primingKRowPointer p batch head row
  let F := primingKSourceFrame p l batch tile warp lane
  have hLength := (hp.lengths batch hb).2.2
  have hRow : kvCopyRow tile tid 0 < 2 ^ 31 := by
    have ht := Nat.mod_lt (tid / 8) (by decide : 0 < 8)
    simp only [kvCopyRow, Nat.mul_zero, Nat.add_zero]
    omega
  obtain ⟨u, hu, hU⟩ := primingKFirstMaskResidual l g (tid := tid)
    (by omega) hRow s (hs.mono ⟨hs.2.2.2.2.1, hs.2.2.2.2.2.1, hs.2.2.2.2.2.2.1,
      hs.2.2.2.2.2.2.2.1, hs.2.2.2.2.2.2.2.2.1, trivial⟩)
  obtain ⟨huA, hFrame⟩ := loaderLinear (regs := [7292, 1082, 1083, 1084]) (by decide) (by decide)
    hs.1 (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hu
  have huAt : At u 543 F := hU.mono
    ⟨(hFrame 1082 (by simp)).trans hs.2.2.2.2.2.2.2.2.2.2.1, hU.2.2.2.2.1,
     (hFrame 1083 (by simp)).trans hs.2.2.2.2.2.2.2.2.2.2.2.1,
     (hFrame 1084 (by simp)).trans hs.2.2.2.2.2.2.2.2.2.2.2.2.1,
     hU.2.2.2.2.2.1, (hFrame 7292 (by simp)).trans hs.2.2.2.2.2.2.2.2.2.1, trivial⟩
  obtain ⟨w, hBefore, hStore, hLast⟩ := hStored
  have hPage : primingScratchPage p batch row < p.pages := primingScratchPageBound hp hb
  obtain ⟨hEq, hFit, _⟩ := sourceScratchPayload_live hp 0 hPage (Nat.mod_lt row (by decide)) hh
  have hBase : base < 2 ^ 64 := by rw [hEq] at hFit; exact hFit
  have hLocal := hp.localMemory.2.1
  have hAlign := hp.localMemory.1
  obtain ⟨v, hv, hHeld, hRun, hLow, hHigh⟩ :=
    primingKPointerReload.observedInPrefix hX (by decide) Flow.code_543
      (by change l.localBase + 0 < 2 ^ 64; omega)
      (by change (l.localBase + 0) % 8 = 0; omega) (by decide) hBase hBefore
      (F := F) (huAt.mono ⟨holds_lookup huAt.2.2.2.2 rfl, huAt.2.2.2.2⟩)
      (by simp [F, primingKSourceFrame, primingKPointerReload]) hBound
      (hr.after_local_nonempty (run_rtg huA) (hDemand.nonempty hr)) hDemand
      ⟨534, hStore⟩ hLast
  refine ⟨v, hv.mono ((holds_append ..).mpr ⟨hv.2.2.2.2, hHeld⟩), hRun, ?_, ?_, ⟨_, _, hLow⟩⟩
  · simpa only [Nat.add_assoc] using (hDemand.advance hLow hBound).advance hHigh hBound
  · have noShuffle {i : Nat} {e : Event} (he : X.get (g, i) = some e)
        (hKind : Execution.isShfl e = false) :
        ((X.tr g).take (i + 1)).countP Execution.isShfl =
          ((X.tr g).take i).countP Execution.isShfl := by
      rw [List.take_add_one, show (X.tr g)[i]? = _ from he]
      simp [hKind]
    exact (noShuffle hHigh rfl).trans (noShuffle hLow rfl)

end

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g src j bound : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hSrc : src < 32)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads) {target : Event}
    (he : X.get (warpLane l g src, j) = some target) (hBound : 543 ≤ bound)
include hp hX hg hw hSrc writes hCTA he hBound

/-- The observed issuing lane reaches the first K pointer broadcast with the two
launch pointer words loaded from its actual saved scratch cells. -/
theorem loaderPrimingKPointerAndSavedOfActiveEvent (hPc : bound < target.pc) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      let co := assignedCoordinates p batch (g / l.block)
      let head := co.2 / 6
      let tile := Mma.trips p batch co.1 - 1
      let warp := warpIndex l g
      let thread := warpLane l g src
      let bases := fun lane =>
        primingKRowPointer p batch head (primingLaneRow tile (32 * warp + lane))
      128 * tile + 127 < 2 ^ 31 ∧
      ∃ pos t ending,
        At t 544 (primingKSourceInputs p l batch tile warp bases src) ∧
        Run kernel Assumptions.all l thread t ((X.tr thread).drop pos) ending ∧
        PrefixDemand X thread pos bound ending ∧
        ((X.tr thread).take pos).countP Execution.isShfl =
          primingSearchShuffleCount batch ∧
        ∃ read a bytes, pos = read + 2 ∧ X.get (thread, read) = some ⟨543, .rd a bytes⟩ ∧
          PrimingCellValue X thread read 534 (sourceScratchAccess l thread 1)
            (b64 (primingKRowPointer p batch head
              (primingLaneRow tile (32 * warp + src) + 64))).toBytes := by
  obtain ⟨batch, hIn, hLo, hHi, hTile, pos, t, ending, hAt, hRun, hDemand, hOrd, hMeta⟩ :=
    loaderPrimingPreparedOfActiveEvent hp hX hg hw hSrc writes hCTA he (by omega) hPc
  have hb := hIn
  have hh := (assignedCoordinates_valid hp hLo hHi).2
  have hHead : (assignedCoordinates p batch (g / l.block)).2 / 6 < p.kvHeads := by
    unfold Params.heads at hh
    omega
  obtain ⟨u, hu, hRest, hReady, hSaved, pre, hLen, hEvents, hNoShuffle, _⟩ :=
    primingKPackSavedCellsInPrefix hp hX hb hHead hAt (by omega) hRun hDemand hMeta
  have hFirst := hSaved (0 : Fin 2)
  simp only [Fin.val_zero, Nat.mul_zero, Nat.add_zero] at hFirst
  have hNext : ((X.tr (warpLane l g src)).take (pos + 6)).countP Execution.isShfl =
      primingSearchShuffleCount batch := by
    rw [← hLen]
    exact (ordinalAfterOrdinary (by rw [hLen]; exact hEvents) hNoShuffle).trans hOrd
  obtain ⟨v, hv, hTail, hLater, hLoaded, a, bytes, hRead⟩ :=
    primingKLoadedLaneInPrefixObserved hp hX hb hHead hTile hBound hu hRest hReady hFirst
  have hSecond := hSaved (1 : Fin 2)
  simp only [Fin.val_one, Nat.mul_one] at hSecond
  exact ⟨batch, hIn, hLo, hHi, hTile, _, v, ending, hv, hTail, hLater, hLoaded.trans hNext,
    _, a, bytes, rfl, hRead, hSecond⟩

/-- The observed lane has the first packed pointer at its first broadcast. -/
theorem loaderPrimingKPointerOfActiveEvent (hPc : bound < target.pc) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      let co := assignedCoordinates p batch (g / l.block)
      let head := co.2 / 6
      let tile := Mma.trips p batch co.1 - 1
      let warp := warpIndex l g
      let thread := warpLane l g src
      let bases := fun lane =>
        primingKRowPointer p batch head (primingLaneRow tile (32 * warp + lane))
      128 * tile + 127 < 2 ^ 31 ∧
      ∃ pos t ending,
        At t 544 (primingKSourceInputs p l batch tile warp bases src) ∧
        Run kernel Assumptions.all l thread t ((X.tr thread).drop pos) ending ∧
        PrefixDemand X thread pos bound ending ∧
        ((X.tr thread).take pos).countP Execution.isShfl =
          primingSearchShuffleCount batch := by
  obtain ⟨batch, hIn, hLo, hHi, hTile, pos, state, ending, hAt, hRun, hDemand, hRank, _⟩ :=
    loaderPrimingKPointerAndSavedOfActiveEvent hp hX hg hw hSrc writes hCTA he hBound hPc
  exact ⟨batch, hIn, hLo, hHi, hTile, pos, state, ending, hAt, hRun, hDemand, hRank⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
