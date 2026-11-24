-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVScratch
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderScratchReadProgress
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderStoreProgress
import Kernels.TmlFa4Fwd.Proof.PrologueInitRecords
import Kernels.TmlFa4Fwd.Flow.Code.Part012

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Prologue Epilogue
open Thread.Loader.LocalAccessCode

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- The same decoded loop rereads each of the two lane-private page and row slots. -/
theorem primingVRestoreSlotOfMaximal (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch row index : Nat} (hg : g < l.threads) (hb : batch < p.batch) (slot : Fin 2)
    {F : List (Nat × Value)} (hLocalBase : (7294,b64 (l.localBase+64)) ∈ F)
    (hFresh : ∀ pair ∈ F, pair.1 ≠ 7601 ∧ pair.1 ≠ 7603)
    (hKeep : ((kernel.code.drop 791).take 1).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hMeta : PrimingMetadataAt p l X g index batch row slot) {s t : TState} {ending : Option TState}
    (ht : At t 790 (primingVScratchSlotFacts l slot ++ F))
    (hLocal : Relation.ReflTransGen (Tau kernel Assumptions.all l g) s t)
    (hPast : Run kernel Assumptions.all l g {} ((X.tr g).take index) (some s))
    (hTail : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    (hBound : index ≤ (X.tr g).length) (hReleased : index = (X.tr g).length → Step.Released l X g) :
    let page := primingScratchPage p batch row
    X.get (g,index) = some ⟨790,.rd (scratchWordAccess l g 2 slot) ((b32 page).toBytes.map some)⟩ ∧
    X.get (g,index+1) = some ⟨792,.rd (scratchWordAccess l g 3 slot)
      ((b32 (row%16)).toBytes.map some)⟩ ∧
    ∃ v, At v 793 ([(7601,b64 page),(7603,b64 (row%16)),(9536,b64 slot.val)] ++ F) ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (index+2)) (some v) ∧
      Run kernel Assumptions.all l g v ((X.tr g).drop (index+2)) ending := by
  dsimp only
  let page := primingScratchPage p batch row
  let pageSite := scratchReloadSite 2
  let rowSite := scratchReloadSite 3
  let pageCell := scratchWordAccess l g 2 slot
  let rowCell := scratchWordAccess l g 3 slot
  have hSavedPage : PrimingCellValue X g index 506 pageCell (b32 page).toBytes := hMeta .page
  have hFrame := (holds_append ..).mp ht.2.2.2.2
  have hPageAt : At t pageSite.pc
      [(pageSite.base,b64 (l.localBase+kvLocalOffset pageSite.array slot))] :=
    ht.mono ⟨hFrame.1.1,trivial⟩
  have hPageNext : Next kernel Assumptions.all l g s t
      (.read pageCell (afterAccessLoad t (.sign 64) 32 [7601])) :=
    ⟨hLocal,scratchReloadTemplate hp pageSite Flow.code_790 (by decide) (by decide) slot hPageAt⟩
  obtain ⟨hpRead,hPagePast,hPageTail⟩ := scratchCellReadOfMaximal hMax hg rfl rfl rfl
    hSavedPage hPageNext hPast hTail hBound hReleased
  have hpGet : X.get (g,index) = some ⟨790,.rd pageCell ((b32 page).toBytes.map some)⟩ :=
    ht.1 ▸ hpRead
  have hPageWidth : page < 2^31 := by
    unfold page primingScratchPage
    split
    · exact ((hp.pageTable batch hb).2 (row / 16) (by omega)).2
    · decide
  have hPageReturn : afterAccessLoad t (.sign 64) 32 [7601] ((b32 page).toBytes.map some) =
      next (setReg t 7601 (b64 page)) := scratchReloadReturn hPageWidth pageSite hPageAt
  rw [hPageReturn] at hPagePast hPageTail
  let afterPage := next (setReg t 7601 (b64 page))
  have hAddress : At t 790 [(7294,b64 (l.localBase+64)),(7599,b64 (4*slot.val))] :=
    ht.mono ⟨holds_mem hFrame.2 hLocalBase,hFrame.1.2.1,trivial⟩
  have hAddress' := hAddress.set (r := 7601) (v := b64 page) (by simp)
  have hAfter : At afterPage 791 [(7294,b64 (l.localBase+64)),(7599,b64 (4*slot.val))] :=
    hAddress'.mono hAddress'.2.2.2.2.2
  let C := [(7601,b64 page),(9536,b64 slot.val)] ++ F
  have hCarried : Holds afterPage.regs C := by
    refine ⟨by simp [afterPage,next,setReg],?_,?_⟩
    · have hSlot : t.regs 9536 = some (b64 slot.val) := hFrame.1.2.2.1
      simpa [afterPage,next,setReg] using hSlot
    · exact holds_update (x := some (b64 page)) hFrame.2 (fun _ hm => (hFresh _ hm).1)
  obtain ⟨u,hu,hU⟩ := primingVRowAddress l g slot hp.localMemory.2.1 afterPage hAfter
  have hCode : ((kernel.code.drop 791).take 1).all
      (fun ins => (C.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true :=
    primingKeepAppend (F := [(7601,b64 page),(9536,b64 slot.val)])
      (by set_option maxRecDepth 100000 in kernel_rfl) hKeep
  obtain ⟨huA,hStable⟩ := loaderLinear (regs := C.map Prod.fst) (by decide) (by decide) hAfter.1
    hCode (by set_option maxRecDepth 100000 in kernel_rfl) hu
  have hURegs := holdsSchedulerFrame hCarried hStable (fun _ hm => List.mem_map_of_mem hm)
  have hOld : PrimingCellValue X g index 511 rowCell (b32 (row%16)).toBytes := hMeta .row
  have hSavedRow := hOld.step hMax.1 hpGet (by intro _ _ h; cases h)
  have hRowNext : Next kernel Assumptions.all l g afterPage u
      (.read rowCell (afterAccessLoad u (.sign 64) 32 [7603])) :=
    ⟨run_rtg huA,scratchReloadTemplate hp rowSite Flow.code_792 (by decide) (by decide) slot hU⟩
  obtain ⟨hrGet,hRowPast,hRowTail⟩ := scratchCellReadOfMaximal hMax hg rfl rfl rfl
    hSavedRow hRowNext hPagePast hPageTail (len_of_get hpGet)
    (releasedIfLast hpGet (by intro h; cases h))
  have hRowReturn : afterAccessLoad u (.sign 64) 32 [7603] ((b32 (row%16)).toBytes.map some) =
      next (setReg u 7603 (b64 (row%16))) :=
    scratchReloadReturn (by omega : row%16 < 2^31) rowSite hU
  rw [hRowReturn] at hRowPast hRowTail
  let target := next (setReg u 7603 (b64 (row%16)))
  have hAt : At target 793
      ([(7601,b64 page),(7603,b64 (row%16)),(9536,b64 slot.val)] ++ F) := by
    have hNext := hU.set (r := 7603) (v := b64 (row%16)) (by simp)
    refine hNext.mono ⟨?_,hNext.2.2.2.2.1,?_,?_⟩
    · simpa [target,next,setReg,Holds] using hURegs.1
    · simpa [target,next,setReg,Holds] using hURegs.2.1
    · exact holds_update (x := some (b64 (row%16))) hURegs.2.2 (fun _ hm => (hFresh _ hm).2)
  refine ⟨hpGet,hU.1 ▸ hrGet,target,hAt,?_,?_⟩
  · simpa only [Nat.add_assoc] using hRowPast
  · simpa only [Nat.add_assoc] using hRowTail

/-- The restored metadata and V ABI issue the corresponding lane-private pointer save. -/
theorem primingVStoreSlotOfMaximal (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g batch head row index : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g)
    (hb : batch < p.batch) (hh : head < p.kvHeads) (slot : Fin 2) {F : List (Nat × Value)}
    (hAbi : primingVScratchAbi p l head ⊆ F)
    (hSave : ((kernel.code.drop 793).take 6).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    {s : TState} {ending : Option TState}
    (hs : At s 793 ([(7601,b64 (primingScratchPage p batch row)),(7603,b64 (row%16)),
      (9536,b64 slot.val)] ++ F))
    (hPast : Run kernel Assumptions.all l g {} ((X.tr g).take index) (some s))
    (hTail : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending) (hPos : 0 < index)
    (hBound : index ≤ (X.tr g).length) (hReleased : index = (X.tr g).length → Step.Released l X g) :
    X.get (g,index) = some ⟨799,.wr (sourceScratchAccess l g slot)
      (b64 (primingVRowPointer p batch head row)).toBytes⟩ ∧
    ∃ t, At t 800 F ∧
      Run kernel Assumptions.all l g {} ((X.tr g).take (index+1)) (some t) ∧
      Run kernel Assumptions.all l g t ((X.tr g).drop (index+1)) ending := by
  let page := primingScratchPage p batch row
  let base := p.vLayout.base+2*(head*p.vLayout.headStride)
  have hFields := (holds_append ..).mp hs.2.2.2.2
  have hOperand : At s 793 (sourceScratchInputs l 1 slot page (row%16)
      p.vLayout.pageStride p.vLayout.rowStride base ++ F) := by
    apply hs.mono
    apply (holds_append ..).mpr
    refine ⟨?_,hFields.2⟩
    refine ⟨hFields.1.1,hFields.1.2.1,holds_mem hFields.2 (hAbi ?_),
      holds_mem hFields.2 (hAbi ?_),holds_mem hFields.2 (hAbi ?_),hFields.1.2.2.1,
      holds_mem hFields.2 (hAbi ?_),trivial⟩
    all_goals simp [primingVScratchAbi,sourceScratchSite,base]
  have hPage := primingScratchPageBound hp (row := row) hb
  obtain ⟨hAddress,hFit,_⟩ := sourceScratchPayload_live hp 1 hPage (Nat.mod_lt row (by decide)) hh
  change sourceScratchPayload page (row%16) p.vLayout.pageStride p.vLayout.rowStride base =
    primingVRowPointer p batch head row at hAddress
  change sourceScratchPayload page (row%16) p.vLayout.pageStride p.vLayout.rowStride base <
    2^64 at hFit
  have hPW : page < 2^64 := by
    unfold page primingScratchPage
    split
    · have h := ((hp.pageTable batch hb).2 (row / 16) (by omega)).2
      omega
    · decide
  have hPS := (hp.objectBytes 2 40 8 p.vLayout.pageStride (by simp [Params.objectWords])).1
  have hRS := (hp.objectBytes 2 24 8 p.vLayout.rowStride (by simp [Params.objectWords])).1
  obtain ⟨v,hPC,hAfter,hNext⟩ := sourceScratchStoreNext hp (g := g) 1 slot
    hPW (by omega) hPS hRS hFit (F := F) hSave hOperand
  obtain ⟨he,hPrefix,hRest⟩ := plainLoaderStoreOfMaximal hp hMax hg hw rfl hNext
    hPast hTail hPos hBound hReleased
  have hWhere : v.pc = 799 := hPC
  rw [hWhere,hAddress] at he
  exact ⟨he,next v,hAfter.mono hAfter.2.2.2.2.2,hPrefix,hRest⟩

end PTX.Kernels.TmlFa4Fwd.Loader
