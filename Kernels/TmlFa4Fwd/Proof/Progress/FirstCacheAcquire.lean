-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderQueryStartProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderQueryBoxProgress
import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderReady
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPacketFacts
import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderFirstCachePhase
import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderFirstQueryPhase
import Kernels.TmlFa4Fwd.Proof.Protocol.OpeningBiasGuard
import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderPrimingPublication
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingSources
import Kernels.TmlFa4Fwd.Proof.LoaderPrimingPrefixCoordinates

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Progress
open PTX PTX.Flow PTX.Proof Prologue Epilogue

private theorem firstCacheStalledPhase {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) :
    ∀ lane < 32, (∀ (i : Nat) (loc : Loc), ¬ X.AsyncArrive (warpLane l g lane,i) loc true) →
      let log := X.objects (Thread.Mma.Observation.emptyObject l g 0)
      ∃ s, MBarrier.stateBefore log log.length = some s ∧ s.phase = 0 := by
  intro lane hl hQuiet
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hSame := (Step.sameWarp_lane hBlock hg hl).1
  have hLaneWarp : 14 ≤ warpIndex l (warpLane l g lane) := by
    rw [show warpIndex l (warpLane l g lane) = warpIndex l g from hSame.2.symm]
    exact hw
  have hCTA : g/l.block = (warpLane l g lane)/l.block := hSame.1.2.2
  have hPhase := Protocol.Loader.cacheEmptyPhaseBeforePublication hp hMax
    hSame.1.2.1 hLaneWarp hQuiet 0
  unfold Thread.Mma.Observation.emptyObject at hPhase ⊢
  rw [hCTA]
  exact hPhase

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
include hp hMax writes

/-- Both first K row pointers are assembled before the actual K byte-mask instructions. -/
theorem selectedCacheKeyMaskEntryOfMaximal {g batch : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hBatch : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads) :
    let co := assignedCoordinates p batch (g/l.block)
    let tile := Mma.trips p batch co.1-1
    let warp := warpIndex l g
    let shuffles := 10 + 7 * (batch / 31) + (if 31 * (batch / 31) < batch then 1 else 0) + 1
    128*tile+127 < 2^31 ∧ ∃ ends,
      ∃ cur : SchedulerWarpReached l X g 538
        (Loader.primingKMaskInputs p l batch tile warp) shuffles 1 ends,
      ∀ lane < 32, ∀ slot : Fin 2,
        let thread := warpLane l g lane
        let row := Loader.primingLaneRow tile (32*warp+lane)+64*slot.val
        Loader.PrimingCellValue X thread (cur.pos lane) 534
          (Loader.sourceScratchAccess l thread slot)
          (b64 (Loader.primingKRowPointer p batch (co.2/6) row)).toBytes := by
  obtain ⟨hTile,ends,⟨cur⟩⟩ :=
    Loader.selectedPrimingScratchOfMaximal hp hMax writes hg hw hBatch hLo hHi
  obtain ⟨done,hMeta⟩ := Loader.primingKeyMetadataOfMaximal hp hMax writes hg hw hBatch hTile cur
    (firstCacheStalledPhase hp hMax hg hw)
  let coords := assignedCoordinates p batch (g/l.block)
  let head := coords.2/6
  have hh := (assignedCoordinates_valid hp hLo hHi).2
  have hHead : head < p.kvHeads := by
    unfold Params.heads at hh
    change (assignedCoordinates p batch (g/l.block)).2/6 < p.kvHeads
    omega
  obtain ⟨packed,hPacked⟩ := Loader.primingKeyPointersReadyOfMaximal hp hMax hg hw hBatch hHead
    done hMeta
  exact ⟨hTile,ends,packed,hPacked⟩

/-- A loader assigned any active request reaches the first key packet's actual commit. -/
theorem selectedCacheKeyCommitWithRankOfMaximal {g batch : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hBatch : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads) :
    ∃ votes ends, Loader.PrimingKeyCommitReached l X g
      (Loader.primingSearchShuffleCount batch+32) votes ends := by
  obtain ⟨hTile,ends,packed,hPacked⟩ :=
    selectedCacheKeyMaskEntryOfMaximal hp hMax writes hg hw hBatch hLo hHi
  let co := assignedCoordinates p batch (g/l.block)
  let key := Mma.trips p batch co.1-1
  have hh := (assignedCoordinates_valid hp hLo hHi).2
  have hHead : co.2/6 < p.kvHeads := by
    unfold Params.heads at hh
    change co.2 < 6*p.kvHeads at hh
    omega
  have hRow : 128*key+7 < 2^31 := by change 128*key+127 < 2^31 at hTile; omega
  obtain ⟨commit⟩ := Loader.primingKeyPacketBoundaryOfMaximal hp hMax hg hw hBatch hHead hRow
    packed hPacked
  exact ⟨1,ends,_,⟨commit⟩⟩

/-- The exact selected K rank also supplies the older minimum-rank interface. -/
theorem selectedCacheKeyCommitOfMaximal {g batch : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hBatch : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads) :
    ∃ shuffles votes ends,
      10 + 7 * (batch / 31) + (if 31 * (batch / 31) < batch then 1 else 0) + 1 + 32 ≤ shuffles ∧
      Loader.PrimingKeyCommitReached l X g shuffles votes ends := by
  obtain ⟨votes,ends,commit⟩ := selectedCacheKeyCommitWithRankOfMaximal hp hMax writes
    hg hw hBatch hLo hHi
  exact ⟨_,votes,ends,le_rfl,commit⟩

end

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
include hp hMax hFrame

/-- The active loader reaches its input boxes after acquiring the initial query guard. -/
theorem selectedQueryBoxesReachedWithRankOfMaximal {g batch : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 14) (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads) :
    ∃ votes ends, Loader.PrimingQueryBoxesReached l X g
      (Loader.primingSearchShuffleCount batch+32) votes ends ∧
      ∃ credit, X.Arrive credit (Thread.Output.queryObject l (g/l.block) 0) 32768 1 true .cta := by
  obtain ⟨_,_,_,⟨commit⟩⟩ :=
    selectedCacheKeyCommitWithRankOfMaximal hp hMax
      (fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame) hg (by omega) hb hLo hHi
  have hReached := Loader.primingQueryEmptyCursorOfMaximal hp hMax hg hw
    (by unfold Loader.primingSearchShuffleCount; omega) commit
  have hBlock : l.block%32 = 0 := by rw [hp.block]
  have hConsumed := Loader.primingQueryEmptyAcquiredOfBlockedPhase hp hMax hg hReached
    (fun lane hl {_ _} hRun hLocal hPc => by
      have hSame := (Step.sameWarp_lane hBlock hg hl).1
      have hWarp : warpIndex l (warpLane l g lane) = 14 := hSame.2.symm.trans hw
      rw [hSame.1.2.2]
      exact Protocol.Loader.openingFirstQueryEmptyPhase hp hMax hSame.1.2.1 hWarp
        ⟨_,_,hRun,hLocal,hPc⟩)
  obtain ⟨hEntry,hCredit⟩ := Loader.primingQueryBoxEntryOfMaximal hp hMax hg hConsumed
  exact ⟨_,_,hEntry,hCredit⟩

/-- Every loader lane assigned a selected request delivers its first K packet. -/
theorem selectedCacheKeyPacketDeliveredOfMaximal {g batch : Nat} (hg : g < l.threads)
    (hw : 14 ≤ warpIndex l g) (hBatch : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads) :
    ∀ lane < 32, ∃ i,
      let thread := warpLane l g lane
      X.AsyncArrive (thread,i) (Thread.Loader.readyObject l thread 0) true ∧
        X.async.arrived (thread,i) = true ∧
        Nonempty (Thread.Loader.PublishedCopyGroup l X (thread,i)) := by
  obtain ⟨_,_,_,hSh,_,⟨commit⟩⟩ := selectedCacheKeyCommitOfMaximal hp hMax
    (fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame) hg hw hBatch hLo hHi
  intro lane hl
  obtain ⟨i,he⟩ := Loader.primingKeyArriveOfMaximal hp hMax hg hw (by omega) commit lane hl
  exact ⟨i,he.arrive,Protocol.LoaderReady.drainedPrimingPublication hp hMax hFrame he,
    Thread.Loader.publishedCopyGroup hp hMax.1 he.arrive⟩

/-- The loader delivers both Q0 boxes for any selected request before its first MMA acquire. -/
theorem selectedQueryPacketDeliveredOfMaximal {g batch : Nat} (hg : g < l.threads)
    (hw : warpIndex l g = 14) (hb : batch < p.batch)
    (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (hBefore : ¬ ∃ r ∈ X.objects (Thread.Output.queryObject l (g/l.block) 0),
      r.reply.waited = some true) :
    (∃ credit, X.Arrive credit (Thread.Output.queryObject l (g/l.block) 0) 32768 1 true .cta) ∧
    let coords := assignedCoordinates p batch (g/l.block)
    ∀ plane : Fin 2, ∃ issue spec,
      issue.1/l.block = g/l.block ∧ Thread.Loader.QuerySubbox p l X issue 0 plane spec ∧
      spec = qInputSpec p (64*plane.val) (p.qOffset batch+256*coords.1) coords.2
        ⟨.shared, g/l.block, Mma.qStart l 0+16384*plane.val⟩
        (Thread.Output.queryObject l (g/l.block) 0) false ∧
      (X.tensor issue).any (fun o => o.effects.notified) = true := by
  have writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc :=
    fun _ _ _ _ => Thread.Loader.loaderOutputWrites hFrame
  obtain ⟨_,_,_,hSh,_,⟨commit⟩⟩ :=
    selectedCacheKeyCommitOfMaximal hp hMax writes hg (by omega) hb hLo hHi
  have hReached := Loader.primingQueryEmptyCursorOfMaximal hp hMax hg hw (by omega) commit
  have hPhase := Protocol.Loader.firstQueryEmptyBeforeAcquire hp hMax
    (NamedBar.cta_lt hg) hBefore
  have hConsumed := Loader.primingQueryEmptyAcquiredOfMaximal hp hMax hg hReached hPhase
  obtain ⟨hEntry,hCredit⟩ := Loader.primingQueryBoxEntryOfMaximal hp hMax hg hConsumed
  have hBoxes := Loader.selectedQueryBoxesOfMaximal hp hMax writes hg hw hb hLo hHi
    (by omega) hEntry
  refine ⟨hCredit,fun plane => ?_⟩
  obtain ⟨issue,spec,hOwner,hBox,hSpec⟩ := hBoxes plane
  refine ⟨issue,spec,hOwner,hBox,hSpec,?_⟩
  by_contra! hPending
  have hFalse : (X.tensor issue).any (fun o => o.effects.notified) = false := by
    cases h : (X.tensor issue).any (fun o => o.effects.notified) <;> simp_all
  exact hMax.not_grows (Protocol.LoaderReady.pendingTensorInput hp hMax.1 hFrame hBox.1 hFalse)

end PTX.Kernels.TmlFa4Fwd.Progress
