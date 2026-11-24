-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderOpeningValueProgress
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingVRestoreProgress
import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVScratch

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Prologue Epilogue
open Thread.Loader.LocalAccessCode

/-- The opening V packet's first page read of the lane's saved metadata. -/
def OpeningValuePageReadAt (p : Params) (l : Launch) (X : Execution)
    (g j batch row : Nat) : Prop :=
  X.get (g,j) = some ⟨790,.rd (scratchWordAccess l g 2 0)
    ((b32 (primingScratchPage p batch row)).toBytes.map some)⟩

/-- The opening V packet's first row read of the lane's saved metadata. -/
def OpeningValueRowReadAt (l : Launch) (X : Execution) (g j row : Nat) : Prop :=
  X.get (g,j) = some ⟨792,.rd (scratchWordAccess l g 3 0)
    ((b32 (row % 16)).toBytes.map some)⟩

/-- The actual read prefix and live operands for a V lane's first pointer assembly. -/
structure OpeningValueMetadataLane (p : Params) (l : Launch) (X : Execution)
    (g i batch row : Nat) (F : List (Nat × Value)) (endState : Option TState) : Prop where
  page : OpeningValuePageReadAt p l X g i batch row
  rowWord : OpeningValueRowReadAt l X g (i+1) row
  second : PrimingMetadataAt p l X g i batch (row+64) 1
  continuation : ∃ t,
    At t 793 ([(7601,b64 (primingScratchPage p batch row)),(7603,b64 (row%16)),
      (9536,b64 0),(6,.pred true)] ++ F) ∧
    Run kernel Assumptions.all l g {} ((X.tr g).take (i+2)) (some t) ∧
    Run kernel Assumptions.all l g t ((X.tr g).drop (i+2)) endState

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc) {g batch shuffles votes : Nat}
    (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) {ends : Nat → Option TState}
include hp hMax writes hg hw hb hLo hHi

/-- Recover the saved K metadata at the actual first V poll and read its page and row words. -/
theorem openingValueMetadataReadWithFrameOfMaximal
    (cur : OpeningValueAcquired l X g shuffles votes ends) {F : List (Nat × Value)}
    (hF : ∀ lane < 32, Holds (cur.state lane).regs F)
    (hKeep : ((kernel.code.drop 785).take 5).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hRowKeep : ((kernel.code.drop 791).take 1).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hFresh : ∀ pair ∈ F, pair.1 ≠ 7601 ∧ pair.1 ≠ 7603)
    (hWait : ∀ lane < 32, ∃ j, j+1 = cur.pos lane ∧ OpeningValueWaitAt l X (warpLane l g lane) j) :
    ∀ lane < 32,
      let co := assignedCoordinates p batch (g/l.block)
      let tile := Mma.trips p batch co.1 - 1
      let row := primingLaneRow tile (32*warpIndex l g+lane)
      OpeningValueMetadataLane p l X (warpLane l g lane) (cur.pos lane) batch row F
        (ends lane) := by
  intro lane hl
  obtain ⟨ready,hPos⟩ := openingValueMetadataReachedWithFrame hp cur hF hKeep
  obtain ⟨j,hj,hWait⟩ := hWait lane hl
  have hCTA : g/l.block < tilePrefix p p.batch*p.heads :=
    hHi.trans_le (Nat.mul_le_mul_right p.heads (tilePrefix_mono p (Nat.succ_le_of_lt hb)))
  have hGet : X.get (warpLane l g lane,j) = some (primingVWaitEvent l (warpLane l g lane) true) :=
    hWait
  obtain ⟨b,hb',hLo',hHi',_,_,hOrder,_,_,_,_,_,hCommit,hMeta⟩ :=
    loaderPrimingVCommitOfActiveEvent hp hMax.1 hg hw hl writes hCTA hGet (show 672 < 782 by decide)
      (by intro f hf; cases hf)
  obtain ⟨selected,_,only⟩ := tileBatch_existsUnique p hCTA
  have hBatch := (only b ⟨hb',hLo',hHi'⟩).trans (only batch ⟨hb,hLo,hHi⟩).symm
  subst b
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hSame := (Step.sameWarp_lane hBlock hg hl).1
  have hw' : 14 ≤ warpIndex l (warpLane l g lane) := by
    rw [show warpIndex l (warpLane l g lane) = warpIndex l g from hSame.2.symm]
    exact hw
  have hMeta' := metadataAtVFirstScratch hp hMax.1 hw' hOrder hCommit hGet (hMeta 0)
  let thread := warpLane l g lane
  let co := assignedCoordinates p batch (g/l.block)
  let tile := Mma.trips p batch co.1 - 1
  let row := primingLaneRow tile (32*warpIndex l g+lane)
  let G := [(6,.pred true),(7294,b64 (l.localBase+64))] ++ F
  have hOld : PrimingMetadataAt p l X thread (ready.pos lane) batch row 0 := by
    rw [hPos,← hj]
    simpa only [thread,row,tile,co,Fin.val_zero,Nat.mul_zero,Nat.add_zero] using hMeta'
  have hs := ready.checkpoint lane hl
  have hAt : At (ready.state lane) 790 (primingVScratchSlotFacts l 0 ++ G) := by
    apply hs.mono
    have hFrame : Holds (ready.state lane).regs
        (primingVFirstScratchFacts l ++ (openingValueBase l ++ F)) :=
      (List.append_assoc ..) ▸ hs.2.2.2.2
    have hTail := (holds_append ..).mp ((holds_append ..).mp hFrame).2
    have hPred : (ready.state lane).regs 6 = some (.pred true) := hFrame.2.2.2.2.1
    have hBase : (ready.state lane).regs 7294 = some (b64 (l.localBase+64)) :=
      holds_mem hTail.1 (by simp [openingValueBase])
    exact (holds_append ..).mpr
      ⟨⟨hFrame.1,hFrame.2.1,hFrame.2.2.1,trivial⟩,hPred,hBase,hTail.2⟩
  have hGFresh : ∀ pair ∈ G, pair.1 ≠ 7601 ∧ pair.1 ≠ 7603 := by
    intro pair hm
    rcases List.mem_append.mp hm with hm | hm
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl | rfl <;> simp
    · exact hFresh pair hm
  have hGKeep : ((kernel.code.drop 791).take 1).all
      (fun ins => (G.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true :=
    primingKeepAppend (F := [(6,.pred true),(7294,b64 (l.localBase+64))])
      (by set_option maxRecDepth 100000 in kernel_rfl) hRowKeep
  have hActor : thread < l.threads := hSame.1.2.1
  obtain ⟨hPage,hRow,t,ht,hPast,hRest⟩ := primingVRestoreSlotOfMaximal hp hMax hActor hb 0
    (F := G) (by simp [G]) hGFresh hGKeep hOld hAt (ready.localSteps lane hl)
    (ready.recorded lane hl) (ready.continuation lane hl) (ready.bounded lane hl)
    (ready.released lane hl)
  have hSecond := metadataAtVFirstScratch hp hMax.1 hw' hOrder hCommit hGet (hMeta 1)
  have hRetain : PrimingMetadataAt p l X thread (cur.pos lane) batch (row+64) 1 := by
    rw [← hj]
    simpa only [thread,row,tile,co,Fin.val_one,Nat.mul_one] using hSecond
  have hResume : At t 793 ([(7601,b64 (primingScratchPage p batch row)),(7603,b64 (row%16)),
      (9536,b64 0),(6,.pred true)] ++ F) :=
    ht.mono ⟨ht.2.2.2.2.1,ht.2.2.2.2.2.1,ht.2.2.2.2.2.2.1,ht.2.2.2.2.2.2.2.1,
      ht.2.2.2.2.2.2.2.2.2⟩
  rw [hPos] at hPage hRow hPast hRest
  exact ⟨hPage,hRow,hRetain,t,hResume,hPast,hRest⟩

end PTX.Kernels.TmlFa4Fwd.Loader
