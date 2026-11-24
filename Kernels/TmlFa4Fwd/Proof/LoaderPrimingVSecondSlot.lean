-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVReload
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderInputOrder
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderLocalAccess
import Kernels.TmlFa4Fwd.Flow.Code.Part013

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow PTX.EventFrame Epilogue
open Thread.Loader.LocalAccessCode

noncomputable section

/-- The rest of the loader preserves each checked V pipeline cut. -/
theorem vSecondCuts {cut : Nat} (hc : cut = 804 ∨ cut = 854 ∨ cut = 855) (bound : Nat) :
    ((kernel.code.drop cut).take (1901 - cut)).all
      (fun i => loaderPipelineCutOp cut 1901 bound [2535, 1062] i.op) = true := by
  rcases hc with rfl | rfl | rfl <;> set_option maxRecDepth 100000 in kernel_rfl

/-- A lane-local writer lies outside the first V packet half and its reloads. -/
theorem vSecondStackWindow {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} {a : Acc} (hw : X.Access (g, j) a true) (hLocal : a.loc.space = .local) :
    ∃ e, X.get (g, j) = some e ∧ (173 < e.pc ∧ e.pc < 804 ∨ 855 ≤ e.pc) := by
  rcases hw with ⟨_, _, h⟩ | ⟨_, h, _⟩ | ⟨_, _, h⟩
  · cases h
  · obtain ⟨site, hs, he⟩ := Thread.Loader.localWriteSite hX h hLocal
    have audit : scalarSites.all
        (fun s => decide (173 < s.accessPc ∧ s.accessPc < 804 ∨ 855 ≤ s.accessPc)) = true := by
      decide
    exact ⟨_, he, of_decide_eq_true (List.all_eq_true.mp audit site hs)⟩
  · exact (noActualRmw hX h).elim

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {g first second : Nat}
    (hWarp : 14 ≤ Prologue.warpIndex l g) {e : Event} (hFirst : X.get (g, first) = some e)
include hp hX hWarp hFirst

/-- The first V vectors and broadcasts cannot overwrite the second saved row pointer.
Its exact value remains current at the decoded second reload. -/
theorem primingVSecondSlotLatestOfEvent (hFirstPc : e.pc = 804) {f : Event}
    (hSecond : X.get (g, second) = some f) (hSecondPc : f.pc = 854) {data : List Byte}
    (hSaved : PrimingCellValue X g first 799 (sourceScratchAccess l g 1) data) :
    PrimingCellValue X g second 799 (sourceScratchAccess l g 1) data := by
  have hOrder : first ≤ second := by
    by_contra! h
    have hBad := Thread.Loader.eventBeforeClosedCut hp hX hWarp (cut := 854) (by decide)
      (vSecondCuts (by decide)) hSecond hFirst (by omega) (by rw [hFirstPc]; decide)
      (by rw [hFirstPc]; decide)
    omega
  obtain ⟨w, hw, hStored, hLast⟩ := hSaved
  refine ⟨w, by omega, hStored, ?_⟩
  intro byte hb j hj dst hWrite hCover
  by_cases hBefore : j < first
  · exact hLast byte hb j hBefore dst hWrite hCover
  obtain ⟨write, hEvent, hPc⟩ := vSecondStackWindow hX hWrite hCover.1.symm
  rcases hPc with ⟨hLate, hEarly⟩ | hLate
  · have hBad := Thread.Loader.eventBeforeClosedCut hp hX hWarp (cut := 804) (by decide)
      (vSecondCuts (by decide)) hFirst hEvent (by omega) hLate hEarly
    omega
  · have hBad := Thread.Loader.eventBeforeClosedCut hp hX hWarp (cut := 855) (by decide)
      (vSecondCuts (by decide)) hEvent hSecond (by omega) (by rw [hSecondPc]; decide)
      (by rw [hSecondPc]; decide)
    omega

end
end PTX.Kernels.TmlFa4Fwd.Loader
