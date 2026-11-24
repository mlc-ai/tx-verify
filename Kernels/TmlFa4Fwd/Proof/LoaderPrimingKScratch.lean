-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKSource
public import Kernels.TmlFa4Fwd.Proof.LoaderScratchRows
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderStackHistory
import Kernels.TmlFa4Fwd.Proof.GlobalWrites

public import Kernels.TmlFa4Fwd.Proof.LoaderPrefixDemand

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Epilogue
open Thread.Loader.LocalAccessCode (DoesNotClobber)

noncomputable section

/-- At the first local page reload of either K pointer-save iteration, the
decoded address and ABI frame identify the row to pack. -/
def primingKScratchInputs (p : Params) (l : Launch) (head : Nat) (slot : Fin 2) :
    List (Nat × Value) :=
  [(7536, b64 (l.localBase + kvLocalOffset 3 slot)), (7294, b64 (l.localBase + 64)),
   (7535, b64 (4 * slot.val)), (7495, b64 p.kLayout.pageStride),
   (7493, b64 p.kLayout.rowStride),
   (7300, b64 (p.kLayout.base + 2 * (head * p.kLayout.headStride))),
   (9535, b64 slot.val), (7292, b64 l.localBase)]

/-- Decode the row-in-page load address after the first metadata load. -/
theorem primingKRowAddress (l : Launch) (g : Nat) (slot : Fin 2)
    (hBase : l.localBase + 128 ≤ 2 ^ 32) :
    Seg kernel [] l g 1 526
      [(7294, b64 (l.localBase + 64)), (7535, b64 (4 * slot.val))] 527
      [(7538, b64 (l.localBase + kvLocalOffset 2 slot))] := by
  have hIdx := slot.isLt
  have hIn : l.localBase + 64 < 2 ^ 64 := by omega
  have hOff : 4 * slot.val < 2 ^ 64 := by omega
  have hOut : l.localBase + 64 + 4 * slot.val < 2 ^ 64 := by omega
  have hOffset : kvLocalOffset 2 slot = 64 + 4 * slot.val := by simp [kvLocalOffset]
  rw [hOffset, ← Nat.add_assoc]
  intro s hs
  seg_fp hs using
    norm_bits [Nat.mod_eq_of_lt hIn, Nat.mod_eq_of_lt hOff, Nat.mod_eq_of_lt hOut]

/-- An ordinary actual event that leaves a local cell untouched cannot
be an intervening write access to any of its bytes. -/
theorem writeAccessDoesNotCover {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g i : Nat} {e : Event} {cell dst : Acc}
    (he : X.get (g, i) = some e) (hNoClobber : DoesNotClobber cell e)
    (hAccess : X.Access (g, i) dst true) {byte : Nat} (hByte : byte < cell.size) :
    ¬ dst.Covers (cell.loc.at byte) := by
  intro hCover
  rcases hAccess with ⟨_, _, hBad⟩ | ⟨data, ⟨pc, he'⟩, _⟩ | ⟨old, new, hRmw⟩
  · cases hBad
  · cases Option.some.inj (he.symm.trans he')
    exact hNoClobber dst data rfl ⟨_, Acc.covers_at hByte, hCover⟩
  · exact noActualRmw hX hRmw

section
variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g batch head row index pageWrite rowWrite : Nat}
    (hb : batch < p.batch) (hh : head < p.kvHeads) (slot : Fin 2) {s : TState}
    {F : List (Nat × Value)} (hFresh : ∀ pair ∈ F, pair.1 ≠ 7537 ∧ pair.1 ≠ 7539)
    (hStep : ((kernel.code.drop 526).take 1).all
      (fun ins => (F.map Prod.fst).all (fun reg => !(writesRegs ins.op).contains reg)) = true)
    (hSave : ((kernel.code.drop 528).take 6).all
      (fun ins => (F.map Prod.fst).all (fun reg => !(writesRegs ins.op).contains reg)) = true)
    (hs : At s 525 (primingKScratchInputs p l head slot ++ F))
include hp hX hb hh slot hFresh hStep hSave hs

/-- The two actual scratch reloads and K pointer save use exactly the page
number and in-page row from the preceding page-table preparation. -/
theorem primingKScratchRowSavedFrameInPrefix {ending : Option TState} {bound : Nat}
    (hBound : 534 ≤ bound) (hr : Run kernel Assumptions.all l g s ((X.tr g).drop index) ending)
    (hDemand : PrefixDemand X g index bound ending) (hPageBefore : pageWrite < index)
    (hRowBefore : rowWrite < index + 1)
    (hPageWrite : X.get (g, pageWrite) = some ⟨506, .wr (scratchWordAccess l g 0 slot)
      (b32 (primingScratchPage p batch row)).toBytes⟩)
    (hRowWrite : X.get (g, rowWrite) = some ⟨511, .wr (scratchWordAccess l g 1 slot)
      (b32 (row % 16)).toBytes⟩)
    (hPageLast : ∀ byte < 4, ∀ j < index, ∀ dst, X.Access (g, j) dst true →
      dst.Covers ((scratchWordAccess l g 0 slot).loc.at byte) → j ≤ pageWrite)
    (hRowLast : ∀ byte < 4, ∀ j < index, ∀ dst, X.Access (g, j) dst true →
      dst.Covers ((scratchWordAccess l g 1 slot).loc.at byte) → j ≤ rowWrite) :
    X.get (g, index) = some ⟨525, .rd (scratchWordAccess l g 0 slot)
      ((b32 (primingScratchPage p batch row)).toBytes.map some)⟩ ∧
    X.get (g, index + 1) = some ⟨527, .rd (scratchWordAccess l g 1 slot)
      ((b32 (row % 16)).toBytes.map some)⟩ ∧
    ∃ u, X.get (g, index + 2) = some ⟨534, .wr (sourceScratchAccess l g slot)
        (b64 (primingKRowPointer p batch head row)).toBytes⟩ ∧
      At u 535 ((7543, b64 (primingKRowPointer p batch head row)) :: F) ∧
      Run kernel Assumptions.all l g u ((X.tr g).drop (index + 3)) ending := by
  let page := primingScratchPage p batch row
  have hPage : page < 2 ^ 31 := by
    unfold page primingScratchPage
    split
    · exact ((hp.pageTable batch hb).2 (row / 16) (by omega)).2
    · decide
  obtain ⟨hFields, hF⟩ := (holds_append ..).mp hs.2.2.2.2
  let G := (primingKScratchInputs p l head slot).tail
  let afterPage := next (setReg s 7537 (b64 page))
  have hIn : At s 525 [(7536, b64 (l.localBase + kvLocalOffset 3 slot))] :=
    hs.mono ⟨hFields.1, trivial⟩
  have hMore := hDemand.nonempty hr
  obtain ⟨pageBytes, hFirst⟩ := scratchWordLoadPresentInPrefix hp 0 slot hIn hr hMore
  obtain ⟨hReadPage, hAt, hAfterPage⟩ :=
    scratchWordReloadObservedInPrefix hp hX hPageBefore hPage 0 slot hIn hr hMore hPageWrite (by
      intro byte hb j dst hAccess hCover
      rcases lt_trichotomy j index with hEarlier | rfl | hLater
      · exact Or.inl (hPageLast byte hb j hEarlier dst hAccess hCover)
      · exact False.elim (writeAccessDoesNotCover hX hFirst (by intro _ _ h; cases h)
          hAccess hb hCover)
      · exact Or.inr hLater)
  have hHeld : Holds afterPage.regs G := by
    simpa [G, primingKScratchInputs, afterPage, next, setReg, Holds] using hFields.2
  have hFPage : Holds afterPage.regs F := holds_update hF (fun _ hm => (hFresh _ hm).1)
  obtain ⟨t, ht, hT⟩ := primingKRowAddress l g slot hp.localMemory.2.1 afterPage
    (hAt.mono ⟨hHeld.1, hHeld.2.1, trivial⟩)
  let keep := (7537, b64 page) :: G
  obtain ⟨htA, hFrame⟩ := loaderLinear (regs := keep.map Prod.fst) (by decide) (by decide) hAt.1
    (by set_option maxRecDepth 100000 in kernel_rfl) (by decide) ht
  have hTFrame : Holds t.regs keep := holdsSchedulerFrame
    (show Holds afterPage.regs keep from ⟨hAt.2.2.2.2.1, hHeld⟩) hFrame
    (fun _ hm => List.mem_map_of_mem hm)
  obtain ⟨_, hFFrame⟩ := loaderLinear (by decide) (by decide) hAt.1 hStep (by decide) ht
  have hFRow := holdsSchedulerFrame hFPage hFFrame (fun _ hm => List.mem_map_of_mem hm)
  have hRow : row % 16 < 2 ^ 31 := by omega
  have hNext := hDemand.advance hReadPage ((by decide : 525 ≤ 534).trans hBound)
  have hNextMore := hNext.nonempty hAfterPage
  have hRunRow := hAfterPage.after_local_nonempty (run_rtg htA) hNextMore
  obtain ⟨rowBytes, hSecond⟩ := scratchWordLoadPresentInPrefix hp 1 slot hT hRunRow hNextMore
  obtain ⟨hReadRow, hAfterRow, hTail⟩ :=
    scratchWordReloadObservedInPrefix hp hX hRowBefore hRow 1 slot hT
      hRunRow hNextMore hRowWrite (by
      intro byte hb j dst hAccess hCover
      by_cases hEarlier : j < index
      · exact Or.inl (hRowLast byte hb j hEarlier dst hAccess hCover)
      by_cases hLater : index + 1 < j
      · exact Or.inr hLater
      have hWhich : j = index ∨ j = index + 1 := by omega
      rcases hWhich with rfl | rfl
      · exact False.elim (writeAccessDoesNotCover hX hReadPage (by intro _ _ h; cases h)
          hAccess hb hCover)
      · exact False.elim (writeAccessDoesNotCover hX hSecond (by intro _ _ h; cases h)
          hAccess hb hCover))
  have hRet : At (next (setReg t 7539 (b64 (row % 16)))) 528
      (sourceScratchInputs l 0 slot page (row % 16) p.kLayout.pageStride p.kLayout.rowStride
        (p.kLayout.base + 2 * (head * p.kLayout.headStride))) := by
    apply hAfterRow.mono
    have hEq : (next (setReg t 7539 (b64 (row % 16)))).regs 7539 =
        some (b64 (row % 16)) := hAfterRow.2.2.2.2.1
    have hRegs : Holds t.regs
        (sourceScratchInputs l 0 slot page (row % 16) p.kLayout.pageStride p.kLayout.rowStride
          (p.kLayout.base + 2 * (head * p.kLayout.headStride))).tail.tail :=
      ⟨hTFrame.2.2.2.1, hTFrame.2.2.2.2.1, hTFrame.2.2.2.2.2.1, hTFrame.2.2.2.2.2.2.1,
       hTFrame.2.2.2.2.2.2.2.1, trivial⟩
    refine ⟨?_, hEq, ?_⟩
    · simpa [scratchReloadSite, sourceScratchSite, next, setReg] using hTFrame.1
    · simpa [sourceScratchInputs, sourceScratchSite, scratchReloadSite, Holds, next, setReg]
        using hRegs
  have hLast : PrefixDemand X g (index + 2) bound ending := by
    simpa only [Nat.add_assoc] using
      hNext.advance hReadRow ((by decide : 527 ≤ 534).trans hBound)
  obtain ⟨u, hSaved, hU, hRest⟩ :=
    primingKRowPointerSavedFrameInPrefix (index := index + 2) hp hb hh slot hSave
      (hRet.mono ((holds_append ..).mpr ⟨hRet.2.2.2.2,
        holds_update hFRow (fun _ hm => (hFresh _ hm).2)⟩)) hTail (hLast.nonempty hTail)
  exact ⟨hReadPage, hReadRow, u, hSaved, hU, hRest⟩

end

end
end PTX.Kernels.TmlFa4Fwd.Loader
