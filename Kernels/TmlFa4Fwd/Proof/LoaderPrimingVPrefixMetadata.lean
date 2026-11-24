-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingPrefixCoordinates
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVKnownMetadata

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

/-- An observed V-lane successor determines its active batch and carries the V ABI
through the actual initial metadata and K-acquire records. -/
theorem loaderPrimingVPreparedOfActiveEvent {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g src j : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hl : src < 32)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    {e : Event} (he : X.get (warpLane l g src, j) = some e) (hLate : 517 < e.pc) :
    ∃ batch < p.batch,
      tilePrefix p batch * p.heads ≤ g / l.block ∧
      g / l.block < tilePrefix p (batch + 1) * p.heads ∧
      let co := assignedCoordinates p batch (g / l.block)
      let ktile := Mma.trips p batch co.1 - 1
      let warp := warpIndex l g
      let thread := warpLane l g src
      let row := primingLaneRow ktile (32 * warp + src)
      128 * ktile + 127 < 2 ^ 31 ∧
      ∃ pos ≤ j, ∃ s ending,
        At s 520 (primingVPrepareFacts p l batch co.2 co.1 ktile warp src) ∧
        Run kernel Assumptions.all l thread s ((X.tr thread).drop pos) ending ∧
        ((X.tr thread).take pos).countP Execution.isShfl = primingSearchShuffleCount batch ∧
        ∀ slot : Fin 2, PrimingMetadataAt p l X thread pos batch (row + 64 * slot.val) slot := by
  obtain ⟨batch, hb, hLo, hHi, pos, hBefore, s, ending, hs, hr, hOrd⟩ :=
    loaderPrimingMetadataOfActiveEvent hp hX hg hw hl writes hCTA he (by omega)
  obtain ⟨hTile, hHead⟩ := assignedCoordinates_valid hp hLo hHi
  obtain ⟨t, ht, htAt⟩ := primingKActiveToAddressLane hp hb hTile hs
  let thread := warpLane l g src
  obtain ⟨hBound, u, hu, huAt⟩ := primingVAdmissionWithTripsLane hp (g := thread)
    hb (hHead.trans hp.heads_signed) hTile hl htAt
  have hMore := traceAfterObservedEvent he hBefore
  have huRun := hr.after_local_nonempty (ht.trans hu) hMore
  obtain ⟨n, v, hTrace, hv, hvRun, _, hMeta⟩ :=
    primingVPreparedLaneInPrefix hp hX hb hBound writes
      (huAt.mono ((holds_append ..).mp huAt.2.2.2.2).1) huRun (by decide)
      (.inr ⟨j, e, hBefore, hLate, he⟩)
  let co := assignedCoordinates p batch (g / l.block)
  let row := primingLaneRow (Mma.trips p batch co.1 - 1) (32 * warpIndex l g + src)
  let pre := primingKPrepEvents p l thread batch row n
  have hTrace' : (X.tr thread).drop pos = pre ++ (X.tr thread).drop (pos + pre.length) := hTrace
  have hOrder : pos + pre.length ≤ j := by
    by_contra! hPast
    have hGet : ((X.tr thread).drop pos)[j - pos]? = some e := by
      rw [List.getElem?_drop, Nat.add_sub_of_le hBefore]
      exact he
    rw [hTrace', List.getElem?_append_left (by omega)] at hGet
    exact (Nat.not_le_of_lt hLate) (primingKPrepEvents_before p l thread batch row n
      (List.mem_of_getElem? hGet))
  have hRank : ((X.tr thread).take (pos + pre.length)).countP Execution.isShfl =
      primingSearchShuffleCount batch := by
    rw [List.take_add, hTrace', List.take_append_length, List.countP_append,
      primingKPrepEvents_noShuffle, Nat.add_zero]
    exact hOrd
  exact ⟨batch, hb, hLo, hHi, hBound, _, hOrder, v, ending, hv, hvRun, hRank, hMeta⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
