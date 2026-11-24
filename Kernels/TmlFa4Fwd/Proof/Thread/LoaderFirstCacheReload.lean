-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderFirstCacheMetadata
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderScratchReadProgress
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderStoreProgress
import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue

/-- The live two-iteration K pointer-preparation frame. -/
def primingKPackIterationFrame (p : Params) (l : Launch) (batch head tile warp : Nat)
    (slot : Fin 2) (lane : Nat) : List (Nat × Value) :=
  (9535,b64 slot.val) :: (773,.pred (slot.val == 0)) ::
    primingKPackFrame p l batch head tile warp lane

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g batch head tile shuffles votes : Nat}
    (hg : g < l.threads)
include hp hMax hg

/-- Both concrete K scratch reads retain the live frame for the paged row-pointer save. -/
theorem primingKeyScratchReadFrameAtSlot (hb : batch < p.batch) {ends : Nat → Option TState}
    (slot : Fin 2)
    (cur : SchedulerWarpReached l X g 522
      (primingKPackIterationFrame p l batch head tile (warpIndex l g) slot) shuffles votes ends)
    {lane : Nat} (hl : lane < 32)
    (hMeta : PrimingMetadataAt p l X (warpLane l g lane) (cur.pos lane) batch
      (primingLaneRow tile (32*warpIndex l g+lane)+64*slot.val) slot) :
    let thread := warpLane l g lane
    let row := primingLaneRow tile (32*warpIndex l g+lane)+64*slot.val
    X.get (thread,cur.pos lane) = some ⟨525,.rd (scratchWordAccess l thread 0 slot)
      ((b32 (primingScratchPage p batch row)).toBytes.map some)⟩ ∧
    X.get (thread,cur.pos lane+1) = some ⟨527,.rd (scratchWordAccess l thread 1 slot)
      ((b32 (row%16)).toBytes.map some)⟩ ∧
    ∃ t : TState,
      At t 528 (sourceScratchInputs l 0 slot (primingScratchPage p batch row) (row%16)
        p.kLayout.pageStride p.kLayout.rowStride
        (p.kLayout.base+2*(head*p.kLayout.headStride)) ++
        (5,.pred (slot.val == 0)) :: primingKPackFrame p l batch head tile (warpIndex l g) lane) ∧
      Run kernel Assumptions.all l thread {} ((X.tr thread).take (cur.pos lane+2)) (some t) ∧
      Run kernel Assumptions.all l thread t ((X.tr thread).drop (cur.pos lane+2)) (ends lane) := by
  let thread := warpLane l g lane
  let row := primingLaneRow tile (32*warpIndex l g+lane)+64*slot.val
  let G := primingKPackFrame p l batch head tile (warpIndex l g) lane
  let v := cur.state lane
  have hV := cur.checkpoint lane hl
  obtain ⟨u,hu,hU⟩ := primingKPackAddress l thread slot hp.localMemory.2.1 v
    (hV.mono ⟨hV.2.2.2.2.1,hV.2.2.2.2.2.1,hV.2.2.2.2.2.2.2.1,trivial⟩)
  let carried := (9535,b64 slot.val) :: G
  obtain ⟨huA,huFrame⟩ := loaderLinear (regs := carried.map Prod.fst)
    (by decide) (by decide) hV.1 (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) hu
  have hUHold : Holds u.regs carried :=
    holdsSchedulerFrame ⟨hV.2.2.2.2.1,hV.2.2.2.2.2.2⟩ huFrame (fun _ hm => List.mem_map_of_mem hm)
  have hAt : At u 525 [(7536,b64 (l.localBase+kvLocalOffset 3 slot))] :=
    hU.mono ⟨hU.2.2.2.2.2.2.1,trivial⟩
  let post := afterAccessLoad u (.sign 64) 32 [7537]
  have hNext : Next kernel Assumptions.all l thread (cur.before lane) u
      (.read (scratchWordAccess l thread 0 slot) post) := by
    refine ⟨(cur.localSteps lane hl).trans (run_rtg huA),?_⟩
    exact scratchReloadTemplate hp (scratchReloadSite 0) Flow.code_525
      (by decide) (by decide) slot hAt
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hThread : thread < l.threads := (Step.sameWarp_lane hBlock hg hl).1.1.2.1
  have hCell : PrimingCellValue X thread (cur.pos lane) 506 (scratchWordAccess l thread 0 slot)
      (b32 (primingScratchPage p batch row)).toBytes := hMeta .page
  obtain ⟨he,hPast,hRest⟩ := scratchCellReadOfMaximal hMax hThread rfl rfl
    (by simp [scratchWordAccess,scratchReloadAccess,Value.toBytes,Value.bytes,b32]) hCell
    hNext (cur.recorded lane hl) (cur.continuation lane hl) (cur.bounded lane hl)
    (cur.released lane hl)
  have hPageRead : X.get (thread,cur.pos lane) = some ⟨525,.rd (scratchWordAccess l thread 0 slot)
      ((b32 (primingScratchPage p batch row)).toBytes.map some)⟩ := hAt.1 ▸ he
  let page := primingScratchPage p batch row
  have hPage : page < 2^31 := by
    unfold page primingScratchPage
    split
    · exact ((hp.pageTable batch hb).2 (row/16) (by omega)).2
    · decide
  let returned := next (setReg u 7537 (b64 page))
  have hReturn : post ((b32 page).toBytes.map some) = returned :=
    scratchReloadReturn hPage (scratchReloadSite 0) hAt
  rw [hReturn] at hPast hRest
  let guard : Nat × Value := (5,.pred (slot.val == 0))
  let pageFrame := (7535,b64 (4*slot.val)) :: guard :: carried
  have hUFrame : At u 525 pageFrame := hAt.mono ⟨hU.2.2.2.2.2.1,hU.2.2.2.2.1,hUHold⟩
  have hPageFrame : At returned 526 ((7537,b64 page) :: pageFrame) :=
    hUFrame.set (by simp [pageFrame,guard,carried,G,primingKPackFrame,primingKMaskInputs])
  have hAfter : At returned 526 [(7294,b64 (l.localBase+64)),(7535,b64 (4*slot.val))] := by
    at_select hPageFrame
  obtain ⟨v,hv,hV⟩ := primingKRowAddress l thread slot hp.localMemory.2.1 returned hAfter
  let keep := (7537,b64 page) :: guard :: carried
  obtain ⟨hvA,hKeep⟩ := loaderLinear (regs := keep.map Prod.fst) (by decide) (by decide) hAfter.1
    (by set_option maxRecDepth 100000 in kernel_rfl) (by decide) hv
  have hVKeep : At v 527 keep := hV.mono
    (holdsSchedulerFrame ⟨hPageFrame.2.2.2.2.1,hPageFrame.2.2.2.2.2.2⟩ hKeep
      (fun _ hm => List.mem_map_of_mem hm))
  let rowPost := afterAccessLoad v (.sign 64) 32 [7539]
  have hRowNext : Next kernel Assumptions.all l thread returned v
      (.read (scratchWordAccess l thread 1 slot) rowPost) :=
    ⟨run_rtg hvA,scratchReloadTemplate hp (scratchReloadSite 1) Flow.code_527
      (by decide) (by decide) slot hV⟩
  have hRowCell : PrimingCellValue X thread (cur.pos lane+1) 511
      (scratchWordAccess l thread 1 slot) (b32 (row%16)).toBytes :=
    (hMeta .row).step hMax.1 hPageRead (by intro _ _ h; cases h)
  obtain ⟨hReadRow,hPastRow,hRestRow⟩ := scratchCellReadOfMaximal hMax hThread rfl rfl
    (by simp [scratchWordAccess,scratchReloadAccess,Value.toBytes,Value.bytes,b32]) hRowCell
    hRowNext hPast hRest (len_of_get hPageRead) (releasedIfLast hPageRead (by intro h; cases h))
  let rowReturned := next (setReg v 7539 (b64 (row%16)))
  have hRowReturn : rowPost ((b32 (row%16)).toBytes.map some) = rowReturned :=
    scratchReloadReturn (by omega) (scratchReloadSite 1) hV
  rw [hRowReturn] at hPastRow hRestRow
  have hAfterRow : At rowReturned 528 ((7539,b64 (row%16)) :: keep) :=
    hVKeep.set (by simp [keep,guard,carried,G,primingKPackFrame,primingKMaskInputs])
  have hInput : At rowReturned 528 (sourceScratchInputs l 0 slot page (row%16)
      p.kLayout.pageStride p.kLayout.rowStride
      (p.kLayout.base+2*(head*p.kLayout.headStride)) ++ guard :: G) := by
    apply hAfterRow.mono
    apply (holds_append ..).2
    constructor
    · exact ⟨holds_lookup hAfterRow.2.2.2.2 rfl,holds_lookup hAfterRow.2.2.2.2 rfl,
        holds_lookup hAfterRow.2.2.2.2 rfl,holds_lookup hAfterRow.2.2.2.2 rfl,
        holds_lookup hAfterRow.2.2.2.2 rfl,holds_lookup hAfterRow.2.2.2.2 rfl,
        holds_lookup hAfterRow.2.2.2.2 rfl,trivial⟩
    · exact ⟨holds_lookup hAfterRow.2.2.2.2 rfl,hAfterRow.2.2.2.2.2.2.2.2⟩
  exact ⟨hPageRead,hV.1 ▸ hReadRow,rowReturned,hInput,hPastRow,hRestRow⟩

omit hp hMax hg in
/-- Reach the first selected iteration of pointer scratch repacking. -/
theorem seedPrimingKeyPack {p : Params} {l : Launch} {X : Execution}
    {g batch head tile shuffles votes : Nat} {ends : Nat → Option TState}
    (cur : PrimingKeyEmptyReady p l X g batch head tile shuffles votes ends) :
    ∃ seeded : SchedulerWarpReached l X g 522
      (primingKPackIterationFrame p l batch head tile (warpIndex l g) 0) shuffles votes ends,
      seeded.pos = cur.pos := by
  obtain ⟨start,hPos,hBefore⟩ := cur.toSchedulerWarpAt.advanceLocalPreserving (pc' := 522)
    (G := primingKPackIterationFrame p l batch head tile (warpIndex l g) 0) (by
      intro lane hl
      let F := primingKPackFrame p l batch head tile (warpIndex l g) lane
      let s := cur.state lane
      have hs : At s 520 F := (cur.checkpoint lane hl).mono
        ((holds_append ..).mp (cur.checkpoint lane hl).2.2.2.2).2
      obtain ⟨v,hv,hV⟩ := primingKPackSeed l (warpLane l g lane) s (hs.mono trivial)
      obtain ⟨hvA,hFrame⟩ := loaderLinear (regs := F.map Prod.fst) (by decide) (by decide) hs.1
        (by set_option maxRecDepth 100000 in kernel_rfl)
        (by set_option maxRecDepth 100000 in kernel_rfl) hv
      exact ⟨v,run_rtg hvA,hV.mono ⟨hV.2.2.2.2.1,hV.2.2.2.2.2.1,
        holdsSchedulerFrame hs.2.2.2.2 hFrame (fun _ hm => List.mem_map_of_mem hm)⟩⟩)
  exact ⟨cur.reframe start hPos hBefore,hPos⟩

/-- The maximal loader trace saves the first exact paged K pointer in its local slot. -/
theorem primingKeyPointerStoredAtSlot (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch)
    (hh : head < p.kvHeads) {ends : Nat → Option TState} (slot : Fin 2)
    (cur : SchedulerWarpReached l X g 522
      (primingKPackIterationFrame p l batch head tile (warpIndex l g) slot) shuffles votes ends)
    {lane : Nat} (hl : lane < 32)
    (hMeta : PrimingMetadataAt p l X (warpLane l g lane) (cur.pos lane) batch
      (primingLaneRow tile (32*warpIndex l g+lane)+64*slot.val) slot) :
    let thread := warpLane l g lane
    let row := primingLaneRow tile (32*warpIndex l g+lane)+64*slot.val
    let word := b64 (primingKRowPointer p batch head row)
    X.get (thread,cur.pos lane) = some ⟨525,.rd (scratchWordAccess l thread 0 slot)
      ((b32 (primingScratchPage p batch row)).toBytes.map some)⟩ ∧
    X.get (thread,cur.pos lane+1) = some ⟨527,.rd (scratchWordAccess l thread 1 slot)
      ((b32 (row%16)).toBytes.map some)⟩ ∧
    X.get (thread,cur.pos lane+2) =
      some ⟨534,.wr (sourceScratchAccess l thread slot) word.toBytes⟩ ∧
    ∃ u : TState,
      At u 535 ((7543,word) :: (5,.pred (slot.val == 0)) ::
        primingKPackFrame p l batch head tile (warpIndex l g) lane) ∧
      Run kernel Assumptions.all l thread {} ((X.tr thread).take (cur.pos lane+3)) (some u) ∧
      Run kernel Assumptions.all l thread u ((X.tr thread).drop (cur.pos lane+3)) (ends lane) := by
  dsimp only
  obtain ⟨hPageRead,hRowRead,t,hAt,hPrior,hTail⟩ :=
    primingKeyScratchReadFrameAtSlot hp hMax hg hb slot cur hl hMeta
  obtain ⟨v,hPc,hV,hNext⟩ := primingKRowPointerStoreNext hp hb hh slot
    (by set_option maxRecDepth 100000 in kernel_rfl) hAt
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hSame := (Step.sameWarp_lane hBlock hg hl).1
  have hLaneWarp : 14 ≤ warpIndex l (warpLane l g lane) := by
    rw [show warpIndex l (warpLane l g lane) = warpIndex l g from hSame.2.symm]
    exact hw
  obtain ⟨he,hPrefix,hRest⟩ := plainLoaderStoreOfMaximal hp hMax hSame.1.2.1 hLaneWarp rfl
    hNext hPrior hTail (by omega) (len_of_get hRowRead)
    (releasedIfLast hRowRead (by intro h; cases h))
  exact ⟨hPageRead,hRowRead,hPc ▸ he,_,hV,hPrefix,hRest⟩

end PTX.Kernels.TmlFa4Fwd.Loader
