-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderOpeningValuePage
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderOpeningValueAbi
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVPack
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingVRestoreProgress
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Prologue Epilogue

/-- The exact first V row pointer is stored to the first lane-private pointer slot. -/
def OpeningValuePointerSavedAt (p : Params) (l : Launch) (X : Execution)
    (g index batch head row : Nat) : Prop :=
  X.get (g,index) = some ⟨799,.wr (sourceScratchAccess l g 0)
    (b64 (primingVRowPointer p batch head row)).toBytes⟩

/-- Three indexed observations give the exact three-event trace prefix. -/
theorem recordedThreeEvents {X : Execution} {g i : Nat} {a b c : Event}
    (ha : X.get (g,i) = some a) (hb : X.get (g,i+1) = some b)
    (hc : X.get (g,i+2) = some c) :
    (X.tr g).drop i = [a,b,c] ++ (X.tr g).drop (i+3) := by
  have h0 := List.getElem?_eq_some_iff.mp ha
  have h1 := List.getElem?_eq_some_iff.mp hb
  have h2 := List.getElem?_eq_some_iff.mp hc
  rw [List.drop_eq_getElem_cons h0.1,h0.2,List.drop_eq_getElem_cons h1.1,h1.2,
    List.drop_eq_getElem_cons h2.1,h2.2]
  rfl

/-- The first pointer save preserves the actual second metadata and its entry operands. -/
structure OpeningValueFirstPointerLane (p : Params) (l : Launch) (X : Execution)
    (g i batch head row : Nat) (F : List (Nat × Value)) (endState : Option TState) : Prop where
  saved : OpeningValuePointerSavedAt p l X g (i+2) batch head row
  second : PrimingMetadataAt p l X g (i+3) batch (row+64) 1
  recorded : (X.tr g).drop i =
    primingVPackEvents p l g batch head row 0 ++ (X.tr g).drop (i+3)
  continuation : ∃ t, At t 800 ((6,.pred true)::F) ∧
    Run kernel Assumptions.all l g {} ((X.tr g).take (i+3)) (some t) ∧
    Run kernel Assumptions.all l g t ((X.tr g).drop (i+3)) endState

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc) {g batch shuffles votes : Nat}
    (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) {ends : Nat → Option TState}
    (cur : OpeningValueAcquired l X g shuffles votes ends)
    (hAbi : ∀ lane < 32,
      let co := assignedCoordinates p batch (g/l.block)
      Holds (cur.state lane).regs (primingVAdmissionCarry p l batch co.2 co.1))
    (hWait : ∀ lane < 32, ∃ j, j+1 = cur.pos lane ∧ OpeningValueWaitAt l X (warpLane l g lane) j)
include hp hMax writes hg hw hb hLo hHi cur hAbi hWait

/-- Execute the V pointer store after reading the saved page and row words. -/
theorem openingValueFirstPointerWithFrameOfMaximal :
    ∀ lane < 32,
      let co := assignedCoordinates p batch (g/l.block)
      let tile := Mma.trips p batch co.1 - 1
      let row := primingLaneRow tile (32*warpIndex l g+lane)
      OpeningValueFirstPointerLane p l X (warpLane l g lane) (cur.pos lane) batch (co.2/6) row
        (primingVAdmissionCarry p l batch co.2 co.1) (ends lane) := by
  intro lane hl
  let thread := warpLane l g lane
  let co := assignedCoordinates p batch (g/l.block)
  let head := co.2/6
  let tile := Mma.trips p batch co.1 - 1
  let row := primingLaneRow tile (32*warpIndex l g+lane)
  let page := primingScratchPage p batch row
  let F := primingVAdmissionCarry p l batch co.2 co.1
  have hKeep : ((kernel.code.drop 785).take 5).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hRowKeep : ((kernel.code.drop 791).take 1).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true := by
    set_option maxRecDepth 100000 in kernel_rfl
  have hFresh : ∀ pair ∈ F, pair.1 ≠ 7601 ∧ pair.1 ≠ 7603 := by
    intro pair hm
    have hCheck : (F.map Prod.fst).all (fun r => decide (r ≠ 7601 ∧ r ≠ 7603)) = true := by
      kernel_rfl
    exact of_decide_eq_true (List.all_eq_true.mp hCheck _ (List.mem_map_of_mem hm))
  have hRead := openingValueMetadataReadWithFrameOfMaximal hp hMax writes hg hw hb hLo hHi cur
    (F := F) hAbi hKeep hRowKeep hFresh hWait lane hl
  obtain ⟨t,ht,hPast,hTail⟩ := hRead.continuation
  let G := (6,.pred true)::F
  have hAfterRead : At t 793
      ([(7601,b64 page),(7603,b64 (row%16)),(9536,b64 0)] ++ G) := ht
  have hHead := (assignedCoordinates_valid hp hLo hHi).2
  have hh : head < p.kvHeads := by
    unfold Params.heads at hHead
    change co.2 < 6*p.kvHeads at hHead
    unfold head
    omega
  have hAbi' : primingVScratchAbi p l head ⊆ G :=
    fun _ hr => List.mem_cons_of_mem _ (List.mem_append_right _ hr)
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hSame := (Step.sameWarp_lane hBlock hg hl).1
  have hActor : thread < l.threads := hSame.1.2.1
  have hw' : 14 ≤ warpIndex l thread := by
    have h : warpIndex l thread = warpIndex l g := hSame.2.symm
    rwa [h]
  have hRowEvent : X.get (thread,cur.pos lane+1) =
      some ⟨792,.rd (scratchWordAccess l thread 3 0) ((b32 (row%16)).toBytes.map some)⟩ :=
    hRead.rowWord
  have hIndex : cur.pos lane+2 = (cur.pos lane+1)+1 := by omega
  obtain ⟨he,v,hAfter,hAfterPrefix,hAfterTail⟩ := primingVStoreSlotOfMaximal hp hMax hActor hw'
    hb hh 0 (F := G) hAbi' (by set_option maxRecDepth 100000 in kernel_rfl) hAfterRead
    hPast hTail (by omega) (by rw [hIndex]; exact len_of_get hRowEvent)
    (by rw [hIndex]; exact releasedIfLast hRowEvent (by intro h; cases h))
  have hPageRead : X.get (thread,cur.pos lane) =
      some ⟨790,.rd (scratchWordAccess l thread 2 0) ((b32 page).toBytes.map some)⟩ :=
    hRead.page
  have hSecond := primingVSecondMetadata hMax.1 hRead.second hPageRead hRowEvent he
  exact ⟨he,hSecond,recordedThreeEvents hPageRead hRowEvent he,v,hAfter,hAfterPrefix,hAfterTail⟩

end PTX.Kernels.TmlFa4Fwd.Loader
