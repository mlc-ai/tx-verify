-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKPack
import Kernels.TmlFa4Fwd.Flow.Code.Part012

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue

noncomputable section

/-- The V row base represented by the page and row words prepared for the first K/V packet. -/
def primingVRowPointer (p : Params) (batch head row : Nat) : Nat :=
  (p.vLayout.loc (primingScratchPage p batch row) head (row % 16) 0).addr

/-- ABI values used by both V scratch iterations. -/
def primingVScratchAbi (p : Params) (l : Launch) (head : Nat) : List (Nat × Value) :=
  [(7292, b64 l.localBase), (7294, b64 (l.localBase + 64)),
   (7499, b64 p.vLayout.pageStride), (7497, b64 p.vLayout.rowStride),
   (7301, b64 (p.vLayout.base + 2 * (head * p.vLayout.headStride)))]

/-- A V metadata iteration has already prepared its page-word address. -/
def primingVScratchSlotFacts (l : Launch) (slot : Fin 2) : List (Nat × Value) :=
  [(7600, b64 (l.localBase + kvLocalOffset 3 slot)), (7599, b64 (4 * slot.val)),
   (9536, b64 slot.val)]

/-- Compute the row-word address from the second local array and the slot offset. -/
theorem primingVRowAddress (l : Launch) (g : Nat) (slot : Fin 2)
    (hStack : l.localBase + 128 ≤ 2 ^ 32) :
    Seg kernel [] l g 1 791
      [(7294, b64 (l.localBase + 64)), (7599, b64 (4 * slot.val))] 792
      [(7602, b64 (l.localBase + kvLocalOffset 2 slot))] := by
  have hIdx := slot.isLt
  have hBase : l.localBase + 64 < 2 ^ 64 := by omega
  have hOff : 4 * slot.val < 2 ^ 64 := by omega
  have hOut : l.localBase + 64 + 4 * slot.val < 2 ^ 64 := by omega
  have hOffset : kvLocalOffset 2 slot = 64 + 4 * slot.val := by simp [kvLocalOffset]
  rw [hOffset, ← Nat.add_assoc]
  intro s hs
  seg_fp hs using
    norm_bits [Nat.mod_eq_of_lt hBase, Nat.mod_eq_of_lt hOff, Nat.mod_eq_of_lt hOut]

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g batch head row index : Nat}
    (hb : batch < p.batch) (hh : head < p.kvHeads) (slot : Fin 2) {s : TState}
    {F : List (Nat × Value)} (hAbi : primingVScratchAbi p l head ⊆ F)
    (hFresh : ∀ t ∈ F, t.1 ≠ 7601 ∧ t.1 ≠ 7603)
    (hStep : ((kernel.code.drop 791).take 1).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
    (hSave : ((kernel.code.drop 793).take 6).all
      (fun ins => (F.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true)
include hp hX hb hh slot hAbi hFresh hStep hSave

/-- The actual V iteration reads both previously prepared metadata words and packs the
physical V row base into the reused pointer slot, retaining the caller's frame. -/
theorem primingVScratchSavedInPrefix (hs : At s 790 (primingVScratchSlotFacts l slot ++ F))
    {ending : Option TState} (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    {bound : Nat} (hBound : 799 ≤ bound) (hDemand : PrefixDemand X g index bound ending)
    (hMeta : PrimingMetadataAt p l X g index batch row slot) :
    X.get (g, index) = some ⟨790, .rd (scratchWordAccess l g 2 slot)
      ((b32 (primingScratchPage p batch row)).toBytes.map some)⟩ ∧
    X.get (g, index + 1) = some ⟨792, .rd (scratchWordAccess l g 3 slot)
      ((b32 (row % 16)).toBytes.map some)⟩ ∧
    ∃ u, X.get (g, index + 2) = some ⟨799, .wr (sourceScratchAccess l g slot)
        (b64 (primingVRowPointer p batch head row)).toBytes⟩ ∧
      At u 800 ((7607, b64 (primingVRowPointer p batch head row)) :: F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (index + 3)) ending := by
  let page := primingScratchPage p batch row
  have hPage : page < 2 ^ 31 := by
    unfold page primingScratchPage
    split
    · exact ((hp.pageTable batch hb).2 (row / 16) (by omega)).2
    · decide
  obtain ⟨hSlot, hFrame⟩ := (holds_append ..).mp hs.2.2.2.2
  obtain ⟨wp, hWp, hPageWrite, hPageLast⟩ := hMeta .page
  obtain ⟨wr, hWr, hRowWrite, hRowLast⟩ := hMeta .row
  let afterPage := next (setReg s 7601 (b64 page))
  have hIn : At s 790 [(7600, b64 (l.localBase + kvLocalOffset 3 slot))] :=
    hs.mono ⟨hSlot.1, trivial⟩
  obtain ⟨_, hPageEvent⟩ :=
    scratchWordLoadPresentInPrefix hp 2 slot hIn hr (hDemand.nonempty hr)
  obtain ⟨hReadPage, hP, hRunPage⟩ :=
    scratchWordReloadObservedInPrefix hp hX hWp hPage 2 slot hIn hr
      (hDemand.nonempty hr) hPageWrite (by
      intro byte hb j dst hAccess hCover
      rcases lt_trichotomy j index with hEarlier | rfl | hLater
      · exact .inl (hPageLast byte hb j hEarlier dst hAccess hCover)
      · exact False.elim (writeAccessDoesNotCover hX hPageEvent (by intro _ _ h; cases h)
          hAccess hb hCover)
      · exact .inr hLater)
  let carried := (7601, b64 page) :: (9536, b64 slot.val) :: F
  have hAfter : Holds afterPage.regs carried := by
    refine ⟨hP.2.2.2.2.1, ?_, holds_update hFrame (fun r hm => (hFresh r hm).1)⟩
    simpa [afterPage, next, setReg, Holds] using hSlot.2.2.1
  have hOffset : afterPage.regs 7599 = some (b64 (4 * slot.val)) := by
    simpa [afterPage, next, setReg] using hSlot.2.1
  have hLocal : At afterPage 791 [(7294, b64 (l.localBase + 64)), (7599, b64 (4 * slot.val))] :=
    hP.mono ⟨holds_mem hAfter.2.2 (hAbi (by simp [primingVScratchAbi])), hOffset, trivial⟩
  obtain ⟨t, ht, hT⟩ := primingVRowAddress l g slot hp.localMemory.2.1 afterPage hLocal
  have hCode : ((kernel.code.drop 791).take 1).all
      (fun ins => (carried.map Prod.fst).all (fun r => !(writesRegs ins.op).contains r)) = true :=
    primingKeepAppend (F := [(7601, b64 page), (9536, b64 slot.val)])
      (by set_option maxRecDepth 100000 in kernel_rfl) hStep
  obtain ⟨htA, hKeep⟩ := loaderLinear (regs := carried.map Prod.fst) (by decide) (by decide)
    hLocal.1 hCode (by decide) ht
  have hTFrame := holdsSchedulerFrame hAfter hKeep (fun _ hm => List.mem_map_of_mem hm)
  have hDemand1 := hDemand.advance hReadPage ((show 790 ≤ 799 by decide).trans hBound)
  have hMore1 := hDemand1.nonempty hRunPage
  have hRunRow := hRunPage.after_local_nonempty (run_rtg htA) hMore1
  have hInRow : At t 792 [(7602, b64 (l.localBase + kvLocalOffset 2 slot))] := hT
  obtain ⟨_, hRowEvent⟩ := scratchWordLoadPresentInPrefix hp 3 slot hInRow hRunRow hMore1
  obtain ⟨hReadRow, hAfterRow, hTail⟩ := scratchWordReloadObservedInPrefix hp hX (by omega)
    (by omega : row % 16 < 2 ^ 31) 3 slot hInRow hRunRow hMore1 hRowWrite (by
      intro byte hb j dst hAccess hCover
      by_cases hEarlier : j < index
      · exact .inl (hRowLast byte hb j hEarlier dst hAccess hCover)
      by_cases hLater : index + 1 < j
      · exact .inr hLater
      have hWhich : j = index ∨ j = index + 1 := by omega
      rcases hWhich with rfl | rfl
      · exact False.elim (writeAccessDoesNotCover hX hReadPage (by intro _ _ h; cases h)
          hAccess hb hCover)
      · exact False.elim (writeAccessDoesNotCover hX hRowEvent (by intro _ _ h; cases h)
          hAccess hb hCover))
  change At (next (setReg t 7603 (b64 (row % 16)))) 793 [(7603, b64 (row % 16))]
    at hAfterRow
  change Run kernel Assumptions.all l g (next (setReg t 7603 (b64 (row % 16))))
    ((X.tr g).drop (index + 1 + 1)) ending at hTail
  let base := p.vLayout.base + 2 * (head * p.vLayout.headStride)
  have hFRow : Holds (next (setReg t 7603 (b64 (row % 16)))).regs F :=
    holds_update (x := some (b64 (row % 16))) hTFrame.2.2 (fun reg hm => (hFresh reg hm).2)
  have hPSReg := holds_mem hFRow (hAbi (show (7499, b64 p.vLayout.pageStride) ∈ _ by
    simp [primingVScratchAbi]))
  have hRSReg := holds_mem hFRow (hAbi (show (7497, b64 p.vLayout.rowStride) ∈ _ by
    simp [primingVScratchAbi]))
  have hBaseReg := holds_mem hFRow (hAbi (show (7301, b64 base) ∈ _ by
    simp [primingVScratchAbi, base]))
  have hLocalReg := holds_mem hFRow (hAbi (show (7292, b64 l.localBase) ∈ _ by
    simp [primingVScratchAbi]))
  have hRet : At (next (setReg t 7603 (b64 (row % 16)))) 793
      (sourceScratchInputs l 1 slot page (row % 16) p.vLayout.pageStride p.vLayout.rowStride
        base ++ F) := by
    apply hAfterRow.mono
    refine (holds_append ..).mpr ⟨?_, hFRow⟩
    change Holds (next (setReg t 7603 (b64 (row % 16)))).regs
      [(7601, b64 page), (7603, b64 (row % 16)), (7499, b64 p.vLayout.pageStride),
       (7497, b64 p.vLayout.rowStride), (7301, b64 base), (9536, b64 slot.val),
       (7292, b64 l.localBase)]
    refine ⟨?_, hAfterRow.2.2.2.2.1, hPSReg, hRSReg, hBaseReg, ?_, hLocalReg, trivial⟩
    · simpa [next, setReg, Holds] using hTFrame.1
    · simpa [next, setReg, Holds] using hTFrame.2.1
  have hPageFit := primingScratchPageBound hp (row := row) hb
  obtain ⟨hEq, hFit, _⟩ := sourceScratchPayload_live hp 1 hPageFit (Nat.mod_lt row (by decide)) hh
  change sourceScratchPayload page (row % 16) p.vLayout.pageStride p.vLayout.rowStride base =
    primingVRowPointer p batch head row at hEq
  change sourceScratchPayload page (row % 16) p.vLayout.pageStride p.vLayout.rowStride base <
    2 ^ 64 at hFit
  have hPS := (hp.objectBytes 2 40 8 p.vLayout.pageStride (by simp [Params.objectWords])).1
  have hRS := (hp.objectBytes 2 24 8 p.vLayout.rowStride (by simp [Params.objectWords])).1
  have hResume : Run kernel Assumptions.all l g (next (setReg t 7603 (b64 (row % 16))))
      ((X.tr g).drop (index + 2)) ending := by simpa only [Nat.add_assoc] using hTail
  have hDemand2 := hDemand1.advance hReadRow ((show 792 ≤ 799 by decide).trans hBound)
  have hMore2 : (X.tr g).drop (index + 2) ≠ [] := by
    simpa only [Nat.add_assoc] using hDemand2.nonempty hTail
  obtain ⟨u, hStored, hU, hRest⟩ := sourceScratchObservedFrameInPrefix (i := index + 2) hp 1 slot
    (by omega) (by omega) hPS hRS hFit hSave hRet hResume hMore2
  rw [hEq] at hStored hU
  exact ⟨hReadPage, hReadRow, u, hStored, hU, hRest⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
