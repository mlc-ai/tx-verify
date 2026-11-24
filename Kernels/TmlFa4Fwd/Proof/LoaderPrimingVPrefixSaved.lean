-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVPrefixWait
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVPack
import Kernels.TmlFa4Fwd.Flow.Code.Part012

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

/-- A later V-lane event determines the two actual local slots containing its
value-cache row pointers. It can be the last event of a consistent lane prefix. -/
theorem loaderPrimingVSavedOfActiveEvent {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g src j : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hl : src < 32)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    {e : Event} (he : X.get (warpLane l g src, j) = some e) (hLate : 799 < e.pc)
    (hSafe : ∀ f, e.kind ≠ .ub f) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      let co := assignedCoordinates p batch (g / l.block)
      let tile := Mma.trips p batch co.1 - 1
      let warp := warpIndex l g
      let thread := warpLane l g src
      let row := primingLaneRow tile (32 * warp + src)
      128 * tile + 127 < 2 ^ 31 ∧
      ∃ pos ≤ j, ∃ s ending,
        At s 803 (vPacketAfterKFrame p l g batch (co.2 / 6) tile
          (fun _ => vPrimingResidual p batch co.1) src) ∧
        Run kernel Assumptions.all l thread s ((X.tr thread).drop pos) ending ∧
        ((X.tr thread).take pos).countP Execution.isShfl = primingSearchShuffleCount batch + 32 ∧
        ∀ slot : Fin 2, PrimingCellValue X thread pos 799 (sourceScratchAccess l thread slot)
          (b64 (primingVRowPointer p batch (co.2 / 6) (row + 64 * slot.val))).toBytes := by
  obtain ⟨batch, hb, hLo, hHi, hTile, index, hOrder, s, ending, hs, hRun, hRank, hMeta⟩ :=
    loaderPrimingVWaitOfActiveEvent hp hX hg hw hl writes hCTA he (by omega) hSafe
  let co := assignedCoordinates p batch (g / l.block)
  let tile := Mma.trips p batch co.1 - 1
  let thread := warpLane l g src
  let row := fun (slot : Fin 2) => primingLaneRow tile (32 * warpIndex l g + src) + 64 * slot.val
  let F := vPacketAfterKFrame p l g batch (co.2 / 6) tile
    (fun _ => vPrimingResidual p batch co.1) src
  have hHead := (assignedCoordinates_valid hp hLo hHi).2
  have hh : co.2 / 6 < p.kvHeads := by unfold co; unfold Params.heads at hHead; omega
  have hFrame : PrimingVPackFrame F := by
    constructor
    · set_option maxRecDepth 100000 in kernel_rfl
    · set_option maxRecDepth 100000 in kernel_rfl
    · set_option maxRecDepth 100000 in kernel_rfl
    · set_option maxRecDepth 100000 in kernel_rfl
    · intro pair hPair
      have hAudit : (F.map Prod.fst).all (fun r => decide (r ≠ 7601 ∧ r ≠ 7603)) = true := by
        set_option maxRecDepth 100000 in kernel_rfl
      exact of_decide_eq_true (List.all_eq_true.mp hAudit _ (List.mem_map_of_mem hPair))
  have hAbi : primingVScratchAbi p l (co.2 / 6) ⊆ F := by
    intro pair hPair
    exact List.mem_append_left _ (List.mem_append_right _ hPair)
  have hStack : (7295, b64 (l.localBase + 96)) ∈ F := by
    simp [F, vPacketAfterKFrame, primingVHandoffFrame]
  obtain ⟨u, hu, huRun, _, hTrace, hSaved⟩ := primingVPackSavedLaneInPrefix hp hX hb hh row
    hFrame hAbi hStack hs hRun (bound := 799) (by decide)
    (.inr ⟨j, e, hOrder, hLate, he⟩) hMeta
  let front := primingVPackEvents p l thread batch (co.2 / 6) (row 0) 0 ++
    primingVPackEvents p l thread batch (co.2 / 6) (row 1) 1
  have hTrace' : (X.tr thread).drop index = front ++ (X.tr thread).drop (index + 6) := hTrace
  have hLen : front.length = 6 := rfl
  have hFuture : index + 6 ≤ j := by
    by_contra! hPast
    have hGet : ((X.tr thread).drop index)[j - index]? = some e := by
      rw [List.getElem?_drop, Nat.add_sub_of_le hOrder]
      exact he
    rw [hTrace', List.getElem?_append_left (by omega)] at hGet
    have hIn := List.mem_of_getElem? hGet
    simp only [front, primingVPackEvents, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at hIn
    rcases hIn with (rfl | rfl | rfl) | (rfl | rfl | rfl)
    all_goals
      first
      | exact (by decide : ¬ 799 < 790) hLate
      | exact (by decide : ¬ 799 < 792) hLate
      | exact Nat.lt_irrefl 799 hLate
  have hOrd : ((X.tr thread).take (index + 6)).countP Execution.isShfl =
      primingSearchShuffleCount batch + 32 := by
    have hNone : front.countP Execution.isShfl = 0 := rfl
    rw [← hLen, List.take_add, hTrace', List.take_append_length, List.countP_append,
      hNone, Nat.add_zero, hRank]
  exact ⟨batch, hb, hLo, hHi, hTile, _, hFuture, u, ending, hu, huRun, hOrd, hSaved⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
