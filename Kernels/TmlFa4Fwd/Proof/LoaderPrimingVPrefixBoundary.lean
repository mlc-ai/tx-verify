-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVPrefixMetadata
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVPrefixMasks
public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVActual
import Kernels.TmlFa4Fwd.Flow.Code.Part008

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

/-- An observed V-lane successor supplies the launch metadata and all K tail
masks at the actual first K commit. -/
theorem loaderPrimingVCommitOfActiveEvent {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g src j : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hl : src < 32)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    {e : Event} (he : X.get (warpLane l g src, j) = some e) (hLate : 672 < e.pc)
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
        At s 673 (vPacketAfterKFrame p l g batch (co.2 / 6) tile
          (fun _ => vPrimingResidual p batch co.1) src) ∧
        Run kernel Assumptions.all l thread s ((X.tr thread).drop pos) ending ∧
        ((X.tr thread).take pos).countP Execution.isShfl = primingSearchShuffleCount batch + 32 ∧
        X.get (thread, pos) = some ⟨673, .asyncCommit⟩ ∧
        ∀ slot : Fin 2, PrimingMetadataAt p l X thread pos batch (row + 64 * slot.val) slot := by
  obtain ⟨batch, hb, hLo, hHi, hTile, index, hOrder, s, ending, hs, hRun, hRank, hMeta⟩ :=
    loaderPrimingVPreparedOfActiveEvent hp hX hg hw hl writes hCTA he (by omega)
  let co := assignedCoordinates p batch (g / l.block)
  let tile := Mma.trips p batch co.1 - 1
  let warp := warpIndex l g
  let tid := 32 * warp + src
  let thread := warpLane l g src
  let F := primingVPrepareFacts p l batch co.2 co.1 tile warp src
  have hStack : (7295, b64 (l.localBase + 96)) ∈ F := by
    simp [F, primingVPrepareFacts, primingVAdmissionCarry]
  obtain ⟨bytes, hRead⟩ := primingVPreparedFirstKReadInPrefix hp hStack hs hRun
    (traceAfterObservedEvent he hOrder)
  obtain ⟨u, front, stop, _, hu, huRun, huRank, huOrder⟩ :=
    prefixQuietCut (F := F) (by decide) (by
      intro branch
      set_option maxRecDepth 100000 in kernel_rfl) (by
      set_option maxRecDepth 100000 in kernel_rfl) ⟨_, Flow.code_538, rfl⟩ hs hRun he hOrder
      (by omega) hSafe
  have hAt : At u 538 (primingKMaskInputs p l batch tile warp src ++
      primingVAdmissionCarry p l batch co.2 co.1) := by
    apply hu.mono
    obtain ⟨hK, hV⟩ := (holds_append ..).mp hu.2.2.2.2
    exact (holds_append ..).mpr ⟨hK.2.2.2.2.2, hV⟩
  have hLen : p.kLength batch < 2 ^ 31 := by have := (hp.lengths batch hb).2.2; omega
  have hRow : kvCopyRow tile tid 0 < 2 ^ 31 := by
    change 128 * tile + 127 < 2 ^ 31 at hTile
    have := Nat.mod_lt (tid / 8) (by decide : 0 < 8)
    simp only [kvCopyRow, Nat.mul_zero, Nat.add_zero]
    omega
  obtain ⟨v, pos, stop', hPos, hv, hvRun, hvRank⟩ :=
    primingVMasksAtKCommitInPrefix hLen hRow hAt huRun he huOrder hLate hSafe
  have hAtV := hv.mono (vFrameAfterMasks p l g batch co.2 co.1 tile src hv.2.2.2.2)
  obtain ⟨hCommit, _⟩ := primingKCommitAdvanceInPrefix hv hvRun (traceAfterObservedEvent he hPos)
  have hw' : warpIndex l g = warpIndex l thread :=
    (Step.sameWarp_lane (by rw [hp.block]) hg hl).1.2
  refine ⟨batch, hb, hLo, hHi, hTile, pos, hPos, v, stop', hAtV, hvRun, ?_, hCommit, ?_⟩
  · rw [hvRank, huRank, hRank]
  · exact fun slot => primingVMetadataAtKCommit hp hX (hw' ▸ hw) hRead hCommit slot (hMeta slot)

end
end PTX.Kernels.TmlFa4Fwd.Loader
