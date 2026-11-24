-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderPrimingVPrefixBoundary
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderInputOrder
import Kernels.TmlFa4Fwd.Proof.Thread.LoaderPointerInstructions
import Kernels.TmlFa4Fwd.Flow.Code.Part012
import Lemmas.Flow.NotClc

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Prologue Epilogue
open Thread.Loader.LocalAccessCode

noncomputable section

private theorem primingVWaitCuts {cut : Nat} (hCut : cut = 673 ∨ cut = 787)
    (branch : Nat) :
    ((kernel.code.drop cut).take (1901 - cut)).all
      (fun ins => loaderPipelineCutOp cut 1901 branch [2535, 1062] ins.op) = true := by
  rcases hCut with rfl | rfl <;> (set_option maxRecDepth 100000 in kernel_rfl)

/-- The opening V spin preserves both lane-private metadata cells. -/
theorem metadataAtVFirstScratch {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g start wait batch row : Nat} (hw : 14 ≤ warpIndex l g) (hOrder : start ≤ wait)
    (hCommit : X.get (g, start) = some ⟨673, .asyncCommit⟩)
    (hWait : X.get (g, wait) = some (primingVWaitEvent l g true))
    {slot : Fin 2} (hMeta : PrimingMetadataAt p l X g start batch row slot) :
    PrimingMetadataAt p l X g (wait + 1) batch row slot := by
  intro word
  obtain ⟨w, hwIndex, he, hLast⟩ := hMeta word
  refine ⟨w, by omega, he, ?_⟩
  intro byte hb j hj dst hWrite hCover
  by_cases hOld : j < start
  · exact hLast byte hb j hOld dst hWrite hCover
  have hLocal : dst.loc.space = .local := hCover.1.symm
  rcases hWrite with ⟨_, _, hImpossible⟩ | ⟨data, hWrite, _⟩ | ⟨_, _, hRmw⟩
  · cases hImpossible
  · obtain ⟨site, hs, hEvent⟩ := Thread.Loader.localWriteSite hX hWrite hLocal
    have hDecoded : (kernel.code[site.accessPc]?).any (fun ins => writeOp ins.op) = true := by
      rcases get_source hX hEvent with ⟨_, hf⟩ | ⟨_, ins, _, _, hc, hf⟩
      · cases hf
      · rw [hc, Option.any_some, fires_write_op hf rfl]
    have hAudit : scalarSites.all (fun s =>
        !(kernel.code[s.accessPc]?).any (fun ins => writeOp ins.op) ||
          decide (173 < s.accessPc ∧ (s.accessPc < 673 ∨ 790 ≤ s.accessPc))) = true := by
      set_option maxRecDepth 100000 in kernel_rfl
    have hClass := List.all_eq_true.mp hAudit site hs
    simp only [hDecoded, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hClass
    rcases hClass with ⟨hLate, hEarly | hFar⟩
    · have hBad := Thread.Loader.eventBeforeClosedCut hp hX hw (cut := 673) (by decide)
        (primingVWaitCuts (by decide)) hCommit hEvent (by omega) hLate hEarly
      exact (Nat.lt_irrefl _ hBad).elim
    · have hBad := Thread.Loader.eventBeforeClosedCut hp hX hw (cut := 787) (by decide)
        (primingVWaitCuts (by decide)) hEvent hWait (by omega)
        (show 173 < 782 by decide) (show 782 < 787 by decide)
      change site.accessPc < 787 at hBad
      omega
  · exact (noActualRmw hX hRmw).elim

/-- An actual V issue witnesses the parity-one acquire, which keeps the K-prepared
metadata cells intact for the first V pointer assembly. -/
theorem loaderPrimingVWaitOfActiveEvent {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g src j : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hl : src < 32)
    (writes : ∀ w a data loc, X.MemWrites w a data → a.Covers loc → loc.space = .global →
      p.oRegion.Contains loc ∨ p.lseRegion.Contains loc)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    {e : Event} (he : X.get (warpLane l g src, j) = some e) (hLate : 782 < e.pc)
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
        At s 790 (primingVFirstScratchFacts l ++ vPacketAfterKFrame p l g batch (co.2 / 6)
          tile (fun _ => vPrimingResidual p batch co.1) src) ∧
        Run kernel Assumptions.all l thread s ((X.tr thread).drop pos) ending ∧
        ((X.tr thread).take pos).countP Execution.isShfl = primingSearchShuffleCount batch + 32 ∧
        ∀ slot : Fin 2, PrimingMetadataAt p l X thread pos batch (row + 64 * slot.val) slot := by
  obtain ⟨batch, hb, hLo, hHi, hTile, index, hOrder, s, ending, hs, hRun, hRank, hCommit, hMeta⟩ :=
    loaderPrimingVCommitOfActiveEvent hp hX hg hw hl writes hCTA he (by omega) hSafe
  let co := assignedCoordinates p batch (g / l.block)
  let tile := Mma.trips p batch co.1 - 1
  let thread := warpLane l g src
  let F := vPacketAfterKFrame p l g batch (co.2 / 6) tile
    (fun _ => vPrimingResidual p batch co.1) src
  obtain ⟨u, front, stop, _, hu, huRun, huRank, huOrder⟩ :=
    prefixQuietCut (F := F) (by decide) (by
      intro branch
      set_option maxRecDepth 100000 in kernel_rfl) (by
      set_option maxRecDepth 100000 in kernel_rfl) ⟨_, Flow.code_780, rfl⟩ hs hRun he hOrder
      (by omega) hSafe
  let index' := index + front.length
  have hFrame : PrimingVEntryFrame F := by
    constructor
    · set_option maxRecDepth 100000 in kernel_rfl
    · set_option maxRecDepth 100000 in kernel_rfl
    · intro pair hPair
      have hAudit : (F.map Prod.fst).all (fun r => decide (r ≠ 9611)) = true := by
        set_option maxRecDepth 100000 in kernel_rfl
      exact of_decide_eq_true (List.all_eq_true.mp hAudit _ (List.mem_map_of_mem hPair))
  have hBase : (2535, b32 l.sharedBase) ∈ F := by simp [F, vPacketAfterKFrame, primingVHandoffFrame]
  have hStack : (7295, b64 (l.localBase + 96)) ∈ F := by
    simp [F, vPacketAfterKFrame, primingVHandoffFrame]
  have hGet : ((X.tr thread).drop index')[j - index']? = some e := by
    rw [List.getElem?_drop, Nat.add_sub_of_le huOrder]
    exact he
  obtain ⟨n, v, tail, hTrace, hv, hvRun⟩ :=
    primingVWaitAndScratchLaneInPrefix hp hFrame hBase hStack hu huRun
      (.inr ⟨e, List.mem_of_getElem? hGet, hLate⟩)
  let waited :=
    List.replicate n (primingVWaitEvent l thread false) ++ [primingVWaitEvent l thread true]
  let pos := index' + n + 1
  have hTrace' : (X.tr thread).drop index' = waited ++ tail := by
    simpa only [waited, List.append_assoc, List.singleton_append] using hTrace
  have hSize : waited.length = n + 1 := by simp [waited]
  have hPrefix : (X.tr thread).drop pos = tail := by
    rw [show pos = index' + waited.length by omega, ← List.drop_drop, hTrace', List.drop_left]
  have hWait : X.get (thread, index' + n) = some (primingVWaitEvent l thread true) := by
    change (X.tr thread)[index' + n]? = _
    rw [← List.getElem?_drop, hTrace]
    have hn : n = (List.replicate n (primingVWaitEvent l thread false)).length := by simp
    rw [List.getElem?_append_right hn.ge, ← hn, Nat.sub_self]
    rfl
  have hPos : pos ≤ j := by
    by_contra! hBad
    have hk : j - index' < waited.length := by omega
    rw [hTrace', List.getElem?_append_left hk] at hGet
    have he' := List.mem_of_getElem? hGet
    simp only [waited, List.mem_append, List.mem_replicate, List.mem_singleton] at he'
    rcases he' with ⟨_, rfl⟩ | rfl <;> exact Nat.lt_irrefl 782 hLate
  have hOrdinal : ((X.tr thread).take pos).countP Execution.isShfl =
      primingSearchShuffleCount batch + 32 := by
    have hNone : waited.countP Execution.isShfl = 0 := by
      simp [waited, Execution.isShfl, primingVWaitEvent]
    rw [show pos = index' + waited.length by omega, List.take_add, hTrace', List.take_append_length,
      List.countP_append, hNone, Nat.add_zero, huRank, hRank]
  have hw' : warpIndex l g = warpIndex l thread :=
    (Step.sameWarp_lane (by rw [hp.block]) hg hl).1.2
  refine ⟨batch, hb, hLo, hHi, hTile, pos, hPos, v, stop, hv, hPrefix.symm ▸ hvRun, hOrdinal, ?_⟩
  exact fun slot => metadataAtVFirstScratch hp hX (hw' ▸ hw) (by dsimp [index']; omega)
    hCommit hWait (hMeta slot)

end
end PTX.Kernels.TmlFa4Fwd.Loader
