-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKPacket
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKSecondReload
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingKPack
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderInputOrder
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderLocalAccess

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Epilogue
open Thread.Loader.LocalAccessCode

noncomputable section

private theorem primingCuts {cut : Nat} (hc : cut = 538 ∨ cut = 550 ∨ cut = 609 ∨ cut = 610)
    (bound : Nat) :
    ((kernel.code.drop cut).take (1901 - cut)).all
      (fun i => loaderPipelineCutOp cut 1901 bound [2535, 1062] i.op) = true := by
  rcases hc with rfl | rfl | rfl | rfl <;> set_option maxRecDepth 100000 in kernel_rfl

private theorem primingStackWindow {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g j : Nat} {a : Acc}
    (hw : X.Access (g, j) a true) (hLocal : a.loc.space = .local) :
    ∃ e, X.get (g, j) = some e ∧ (173 < e.pc ∧ e.pc < 538 ∨ 610 ≤ e.pc) := by
  rcases hw with ⟨_, _, h⟩ | ⟨_, h, _⟩ | ⟨_, _, h⟩
  · cases h
  · obtain ⟨site, hs, he⟩ := Thread.Loader.localWriteSite hX h hLocal
    have audit : scalarSites.all
        (fun s => decide (173 < s.accessPc ∧ s.accessPc < 538 ∨ 610 ≤ s.accessPc)) = true := by
      decide
    exact ⟨_, he, of_decide_eq_true (List.all_eq_true.mp audit site hs)⟩
  · exact (noActualRmw hX h).elim

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem primingSecondSlotLatestOfBoundaries {g first stop : Nat}
    (hWarp : 14 ≤ Prologue.warpIndex l g) {a : Acc} {bs : List (Option Byte)} {data : List Byte}
    (hFirst : X.get (g,first) = some ⟨543,.rd a bs⟩) (hOrder : first ≤ stop)
    (hSaved : PrimingCellValue X g first 534 (sourceScratchAccess l g 1) data)
    (hNoLater : ∀ {j : Nat} {e : Event}, j < stop → X.get (g,j) = some e → 610 ≤ e.pc → False) :
    PrimingCellValue X g stop 534 (sourceScratchAccess l g 1) data := by
  obtain ⟨w, hw, he, hLast⟩ := hSaved
  refine ⟨w, by omega, he, ?_⟩
  intro byte hb j hj dst hWrite hCover
  by_cases hj' : j < first
  · exact hLast byte hb j hj' dst hWrite hCover
  have hSpace : dst.loc.space = .local := hCover.1.symm
  obtain ⟨e, hEvent, hPc⟩ := primingStackWindow hX hWrite hSpace
  rcases hPc with ⟨hLate, hEarly⟩ | hLate
  · have hBad := Thread.Loader.eventBeforeClosedCut hp hX hWarp (cut := 538) (by decide)
      (primingCuts (by decide)) hFirst hEvent (by omega) hLate hEarly
    exact ((by decide : ¬ 543 < 538) hBad).elim
  · exact (hNoLater hj hEvent hLate).elim

/-- No write to the second slot intervenes between the saved pointer and its actual reload. -/
theorem primingSecondSlotLatest {g first second : Nat} (hWarp : 14 ≤ Prologue.warpIndex l g)
    {a b : Acc} {bs cs : List (Option Byte)} {data : List Byte}
    (hFirst : X.get (g, first) = some ⟨543, .rd a bs⟩)
    (hSecond : X.get (g, second) = some ⟨609, .rd b cs⟩)
    (hSaved : PrimingCellValue X g first 534 (sourceScratchAccess l g 1) data) :
    PrimingCellValue X g second 534 (sourceScratchAccess l g 1) data := by
  have hOrder : first ≤ second := by
    by_contra! h
    have hBad := Thread.Loader.eventBeforeClosedCut hp hX hWarp (cut := 609) (by decide)
      (primingCuts (by decide)) hSecond hFirst (by omega)
      (show 173 < 543 by decide) (show 543 < 609 by decide)
    exact (by decide : ¬ 609 < 609) hBad
  apply primingSecondSlotLatestOfBoundaries hp hX hWarp hFirst hOrder hSaved
  intro j e hj he hPc
  have hBad := Thread.Loader.eventBeforeClosedCut hp hX hWarp (cut := 610) (by decide)
    (primingCuts (by decide)) he hSecond (by omega)
    (show 173 < 609 by decide) (show 609 < 610 by decide)
  omega

/-- The last actual copy of the first half leaves the second packed pointer intact. -/
theorem primingSecondSlotLatestAfterFirstHalf {g first last : Nat}
    (hWarp : 14 ≤ Prologue.warpIndex l g) {a : Acc} {bs : List (Option Byte)} {data : List Byte}
    {event : Event} (hFirst : X.get (g,first) = some ⟨543,.rd a bs⟩)
    (hLast : X.get (g,last) = some event) (hPc : event.pc = 607)
    (hSaved : PrimingCellValue X g first 534 (sourceScratchAccess l g 1) data) :
    PrimingCellValue X g (last+1) 534 (sourceScratchAccess l g 1) data := by
  have hOrder : first ≤ last+1 := by
    by_contra! h
    have hBad := Thread.Loader.eventBeforeClosedCut hp hX hWarp (cut := 550) (by decide)
      (primingCuts (by decide)) hLast hFirst (by omega)
      (show 173 < 543 by decide) (show 543 < 550 by decide)
    omega
  apply primingSecondSlotLatestOfBoundaries hp hX hWarp hFirst hOrder hSaved
  intro j e hj he hLate
  have hBad := Thread.Loader.eventBeforeClosedCut hp hX hWarp (cut := 610) (by decide)
    (primingCuts (by decide)) he hLast (Nat.le_of_lt_succ hj) (by omega) (by omega)
  omega

omit hp hX in
/-- A stored priming K pointer is a bounded, aligned physical cache-row address. -/
theorem primingStoredPointerBounds {p : Params} {l : Launch} {m : Mem0}
    (hp : Pre p l m) {batch head row : Nat} (hb : batch < p.batch) (hh : head < p.kvHeads) :
    primingKRowPointer p batch head row < 2 ^ 64 ∧
      primingKRowPointer p batch head row % 16 = 0 := by
  have hPage : primingScratchPage p batch row < p.pages := primingScratchPageBound hp hb
  obtain ⟨hEq, hBound, hAligned⟩ :=
    sourceScratchPayload_live hp 0 hPage (Nat.mod_lt row (by decide)) hh
  have hPointer : _ = primingKRowPointer p batch head row := hEq
  rw [← hPointer]
  exact ⟨hBound, hAligned⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
