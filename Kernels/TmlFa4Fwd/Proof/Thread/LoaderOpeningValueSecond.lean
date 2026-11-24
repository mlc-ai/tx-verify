-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderOpeningValuePointer
import Kernels.TmlFa4Fwd.Flow.Code.Part012
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPrimingVRestoreProgress
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Prologue Epilogue
open Thread.Loader.LocalAccessCode

private theorem primingVSecondScratchFromFirst {l : Launch} {g : Nat}
    (hStack : l.localBase + 128 ≤ 2^32) {F : List (Nat × Value)}
    (hBase : (7295,b64 (l.localBase+96)) ∈ F)
    (hKeep₀ : ((kernel.code.drop 800).take 2).all
      (fun ins => (((6,.pred true)::F).map Prod.fst).all
        (fun r => !(writesRegs ins.op).contains r)) = true)
    (hKeep₁ : ((kernel.code.drop 787).take 3).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    {s : TState} (hs : At s 800 ((6,.pred true)::F)) :
    ∃ u, Relation.ReflTransGen (Tau kernel Assumptions.all l g) s u ∧
      At u 790 (primingVScratchSlotFacts l 1 ++ (6,.pred false)::F) := by
  let G := (6,.pred true)::F
  obtain ⟨t,ht,hT⟩ := primingVLoopSeed l g s (hs.mono trivial)
  obtain ⟨htA,hStable⟩ := loaderLinear (regs := G.map Prod.fst) (by decide) (by decide) hs.1
    hKeep₀ (by set_option maxRecDepth 100000 in kernel_rfl) ht
  have hGT := holdsSchedulerFrame hs.2.2.2.2 hStable (fun _ hm => List.mem_map_of_mem hm)
  have hAt : At t 802 ([(9536,b64 1),(774,.pred false)] ++ G) :=
    hT.mono ((holds_append ..).mpr ⟨hT.2.2.2.2,hGT⟩)
  obtain ⟨w,hw,hW⟩ := run_bra (K := kernel) (A := []) (L := l) (g := g) Flow.code_802
    true hAt hGT.1 (by simp)
  have hwA := (loaderLinear (regs := []) (by decide) (by decide) hAt.1
    (by simp) (by decide) hw).1
  have hHeld := ((holds_append ..).mp hW.2.2.2.2).2.2
  have hStart : At w 787 [(9536,b64 1),(774,.pred false),(7295,b64 (l.localBase+96))] :=
    hW.mono ⟨hW.2.2.2.2.1,hW.2.2.2.2.2.1,holds_mem hHeld hBase,trivial⟩
  obtain ⟨u,hu,hU⟩ := primingVSecondAddress (g := g) hStack w hStart
  obtain ⟨huA,hRemain⟩ := loaderLinear (regs := F.map Prod.fst) (by decide) (by decide) hStart.1
    hKeep₁ (by set_option maxRecDepth 100000 in kernel_rfl) hu
  exact ⟨u,run_rtg (run_comp (run_comp htA hwA) huA),hU.mono ((holds_append ..).mpr
    ⟨((holds_append ..).mp hU.2.2.2.2).1,
      ((holds_append ..).mp hU.2.2.2.2).2.1,
      holdsSchedulerFrame hHeld hRemain (fun _ hm => List.mem_map_of_mem hm)⟩)⟩

/-- The second V scratch iteration starts in the lane's actual trace and keeps both
lane-private metadata words saved before the opening K packet. -/
theorem openingValueSecondScratchOfMaximal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m)
    {g shuffles votes batch head row : Nat} {ends : Nat → Option TState}
    (cur : OpeningValueAcquired l X g shuffles votes ends)
    {lane : Nat}
    (hFirst : OpeningValueFirstPointerLane p l X (warpLane l g lane) (cur.pos lane)
      batch head row (primingVAdmissionCarry p l batch
        (assignedCoordinates p batch (g/l.block)).2 (assignedCoordinates p batch (g/l.block)).1)
      (ends lane)) :
    let F := primingVAdmissionCarry p l batch
      (assignedCoordinates p batch (g/l.block)).2 (assignedCoordinates p batch (g/l.block)).1
    let thread := warpLane l g lane
    let index := cur.pos lane+3
    ∃ before ready, At ready 790 (primingVScratchSlotFacts l 1 ++ (6,.pred false)::F) ∧
      Run kernel Assumptions.all l thread {} ((X.tr thread).take index) (some before) ∧
      Relation.ReflTransGen (Tau kernel Assumptions.all l thread) before ready ∧
      Run kernel Assumptions.all l thread before ((X.tr thread).drop index) (ends lane) ∧
      PrimingMetadataAt p l X thread index batch (row+64) 1 := by
  dsimp only
  let F := primingVAdmissionCarry p l batch
    (assignedCoordinates p batch (g/l.block)).2 (assignedCoordinates p batch (g/l.block)).1
  obtain ⟨t,ht,hPast,hTail⟩ := hFirst.continuation
  obtain ⟨u,hu,hU⟩ := primingVSecondScratchFromFirst hp.localMemory.2.1
    (F := F) (by simp [F,primingVAdmissionCarry])
    (by set_option maxRecDepth 100000 in kernel_rfl)
    (by set_option maxRecDepth 100000 in kernel_rfl) ht
  exact ⟨t,u,hU,hPast,hu,hTail,hFirst.second⟩

/-- The second V address is stored in the lane's second pointer slot. -/
def OpeningValueSecondPointerSavedAt (p : Params) (l : Launch) (X : Execution)
    (g index batch head row : Nat) : Prop :=
  X.get (g,index) = some ⟨799,.wr (sourceScratchAccess l g 1)
    (b64 (primingVRowPointer p batch head row)).toBytes⟩

/-- Both pointer cells hold the addresses saved by the two V scratch iterations. -/
structure OpeningValuePointersStoredLane (p : Params) (l : Launch) (X : Execution)
    (g i batch head row : Nat) (F : List (Nat × Value)) (endState : Option TState) : Prop where
  saved : OpeningValueSecondPointerSavedAt p l X g (i+5) batch head (row+64)
  recorded : (X.tr g).drop i =
    primingVPackEvents p l g batch head row 0 ++ primingVPackEvents p l g batch head (row+64) 1 ++
      (X.tr g).drop (i+6)
  latest : ∀ slot : Fin 2, PrimingCellValue X g (i+6) 799 (sourceScratchAccess l g slot)
    (b64 (primingVRowPointer p batch head (row+64*slot.val))).toBytes
  continuation : ∃ t, At t 800 ((6,.pred false)::F) ∧
    Run kernel Assumptions.all l g {} ((X.tr g).take (i+6)) (some t) ∧
    Run kernel Assumptions.all l g t ((X.tr g).drop (i+6)) endState

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hMax : Maximal l kernel Assumptions.all m X) {g shuffles votes batch row : Nat}
    (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hb : batch < p.batch)
    (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) {ends : Nat → Option TState}
    (cur : OpeningValueAcquired l X g shuffles votes ends) {lane : Nat} (hl : lane < 32)
    (hFirst : let co := assignedCoordinates p batch (g/l.block)
      OpeningValueFirstPointerLane p l X (warpLane l g lane) (cur.pos lane) batch (co.2/6)
        row (primingVAdmissionCarry p l batch co.2 co.1) (ends lane))
include hp hMax hg hw hb hLo hHi cur hl hFirst

/-- The recorded first pointer store forces both second metadata reads and the exact second save. -/
theorem openingValueSecondPointerWithFrameOfMaximal :
    let co := assignedCoordinates p batch (g/l.block)
    OpeningValuePointersStoredLane p l X (warpLane l g lane) (cur.pos lane)
      batch (co.2/6) row (primingVAdmissionCarry p l batch co.2 co.1) (ends lane) := by
  let co := assignedCoordinates p batch (g/l.block)
  let F := (6,.pred false)::primingVAdmissionCarry p l batch co.2 co.1
  let thread := warpLane l g lane
  have hBlock : l.block % 32 = 0 := by rw [hp.block]
  have hSame := (Step.sameWarp_lane hBlock hg hl).1
  have hThread : thread < l.threads := hSame.1.2.1
  have hw' : 14 ≤ warpIndex l thread := by
    have hh : warpIndex l thread = warpIndex l g := hSame.2.symm
    rwa [hh]
  have hHead := (assignedCoordinates_valid hp hLo hHi).2
  have hh : co.2/6 < p.kvHeads := by
    unfold Params.heads at hHead
    change co.2 < 6*p.kvHeads at hHead
    omega
  obtain ⟨before,ready,ht,hPast,hLocal,hTail,hMeta⟩ :=
    openingValueSecondScratchOfMaximal hp cur hFirst
  have hOld : X.get (thread,cur.pos lane+2) = some
      ⟨799,.wr (sourceScratchAccess l thread 0)
        (b64 (primingVRowPointer p batch (co.2/6) row)).toBytes⟩ :=
    hFirst.saved
  have hIndex : cur.pos lane+3 = (cur.pos lane+2)+1 := by omega
  have hFresh : ∀ pair ∈ F, pair.1 ≠ 7601 ∧ pair.1 ≠ 7603 := by
    intro pair hm
    have hCheck : (F.map Prod.fst).all (fun r => decide (r ≠ 7601 ∧ r ≠ 7603)) = true := by
      kernel_rfl
    exact of_decide_eq_true (List.all_eq_true.mp hCheck _ (List.mem_map_of_mem hm))
  obtain ⟨hPage,hRow,u,hU,hReadPrefix,hReadTail⟩ := primingVRestoreSlotOfMaximal hp hMax
    hThread hb 1 (F := F) (by simp [F,primingVAdmissionCarry,primingVScratchAbi])
    hFresh (by set_option maxRecDepth 100000 in kernel_rfl) hMeta ht hLocal hPast hTail
    (by rw [hIndex]; exact len_of_get hOld)
    (by rw [hIndex]; exact releasedIfLast hOld (by intro h; cases h))
  have hAbi : primingVScratchAbi p l (co.2/6) ⊆ F := by
    intro reg hr
    exact List.mem_cons_of_mem _ (List.mem_append_right _ hr)
  have hBefore : (cur.pos lane+3)+2 = ((cur.pos lane+3)+1)+1 := by omega
  obtain ⟨hStore,t,hT,hStoredPrefix,hStoredTail⟩ :=
    primingVStoreSlotOfMaximal hp hMax hThread hw' hb hh 1 hAbi
    (by set_option maxRecDepth 100000 in kernel_rfl) hU hReadPrefix hReadTail
    (by omega) (by rw [hBefore]; exact len_of_get hRow)
    (by rw [hBefore]; exact releasedIfLast hRow (by intro h; cases h))
  have hSecondTrace : (X.tr thread).drop (cur.pos lane+3) =
      primingVPackEvents p l thread batch (co.2/6) (row+64) 1 ++
        (X.tr thread).drop (cur.pos lane+6) := by
    simpa only [Nat.add_assoc,Nat.reduceAdd,primingVPackEvents] using
      recordedThreeEvents hPage hRow hStore
  have hTrace := hFirst.recorded.trans (congrArg (_ ++ ·) hSecondTrace)
  refine ⟨hStore,by simpa only [List.append_assoc] using hTrace,?_,t,hT,
    by simpa only [Nat.add_assoc] using hStoredPrefix,
    by simpa only [Nat.add_assoc] using hStoredTail⟩
  intro slot
  have only : slot = 0 ∨ slot = 1 := by fin_cases slot <;> simp
  rcases only with rfl | rfl
  · have h0 := primingCellValue_write hOld
    rw [← hIndex] at h0
    have h1 := h0.step hMax.1 hPage (by intro _ _ h; cases h)
    have h2 := h1.step hMax.1 hRow (by intro _ _ h; cases h)
    rw [← hBefore] at h2
    have h3 := h2.step hMax.1 hStore (by
      intro dst data h
      obtain ⟨rfl,_⟩ := Kind.wr.inj h
      exact Thread.Loader.LocalAccessCode.cellsApart (p := pointerPacket 0) (by decide))
    simpa only [Nat.add_assoc,Fin.val_zero,Nat.mul_zero,Nat.add_zero] using h3
  · simpa only [Nat.add_assoc,Fin.val_one,Nat.mul_one] using primingCellValue_write hStore

end PTX.Kernels.TmlFa4Fwd.Loader
