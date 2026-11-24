-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmKeySlot
public import Kernels.TmlFa4Fwd.Proof.LoaderWarmRoundKeyReload
import Kernels.TmlFa4Fwd.Proof.LoaderWarmSecondReload
public import Kernels.TmlFa4Fwd.Proof.LoaderWarmKeyPairSites
import Kernels.TmlFa4Fwd.Proof.LoaderPrefixStableCut

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Proof PTX.Flow Prologue Epilogue

noncomputable section

set_option maxRecDepth 100000 in
/-- Recover the actual scratch pointer and column needed by any pair in a warm K packet. -/
theorem warmRoundKeySlotOfEvent {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g lane batch iteration j : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hl : lane < 32)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    (pair : Fin 16) {e : Event} (he : X.get (warpLane l g lane, j) = some e)
    (hPc : 1003 < e.pc) (hRound : WarmRoundDemand p l X g lane batch iteration j e)
    (hSecond : 8 ≤ pair.val → 1072 < e.pc)
    (hLater : warmKShufflePc pair < e.pc ∨ (Execution.isShfl e = true ∧
      ((X.tr (warpLane l g lane)).take j).countP Execution.isShfl =
        primingSearchShuffleCount batch + 64 + 64 * iteration + 2 * pair.val + 1))
    (hSafe : ∀ f, e.kind ≠ .ub f) :
    let co := assignedCoordinates p batch (g / l.block)
    let thread := warpLane l g lane
    let tid := thread % l.block
    let trips := Mma.trips p batch co.1
    let row := warmKInputRow (trips - 2 - iteration) tid pair
    let ptr := primingKRowPointer p batch (co.2 / 6) row
    ∃ pos ≤ j, ∃ s ending,
      At s (warmKInputPc pair) (warmKSlotWords pair ptr tid) ∧
      Run kernel Assumptions.all l thread s ((X.tr thread).drop pos) ending ∧
      ((X.tr thread).take pos).countP Execution.isShfl =
        primingSearchShuffleCount batch + warmKInputRank pair + 64 * iteration := by
  by_cases hSlot : pair.val < 8
  · obtain ⟨index, hBefore, s, ending, hs, hr, hRank⟩ :=
      warmRoundFirstKeyReloadOfEvent hp hX hFrame hg hw hl hCTA hb hLo hHi
        he hPc hSafe hRound
    let co := assignedCoordinates p batch (g / l.block)
    let thread := warpLane l g lane
    let tid := thread % l.block
    let trips := Mma.trips p batch co.1
    let ptr := primingKRowPointer p batch (co.2 / 6) (primingLaneRow (trips - 2 - iteration) tid)
    let F := [(1998, b32 (ptr % 2 ^ 32)), (1999, b32 (ptr / 2 ^ 32)), (1119, b32 (8 * (tid % 8)))]
    have hAt : At s 1004 F := hs.mono
      ⟨holds_lookup hs.2.2.2.2 rfl, holds_lookup hs.2.2.2.2 rfl,
        holds_lookup hs.2.2.2.2 rfl, trivial⟩
    by_cases hZero : pair.val = 0
    · refine ⟨index + 2, hBefore, s, ending, ?_, hr, ?_⟩
      · simpa only [warmKInputPc, warmKSlotWords, warmKInputRow, warmKShuffleInput,
          warmKInputColumn, ite_eq_left hZero, ite_eq_left hSlot, Nat.add_zero] using hAt
      · simpa only [warmKInputRank, ite_eq_left hZero] using hRank
    have hAudit (bound : Nat) : ((kernel.code.drop 1004).take (1007 - 1004)).all
        (fun ins => loaderPipelineCutOp 1004 1007 bound (F.map Prod.fst) ins.op) = true := by
      kernel_rfl
    have hCounted : (((kernel.code.drop 1004).take (1007 - 1004)).zipIdx 1004).all
        (fun (ins, pc) => LoaderRankedInstr 1007 pc ins) = true := by kernel_rfl
    have hCount : loaderShuffleTail 1007 1004 = 2 := by kernel_rfl
    have hDemand : 1007 ≤ e.pc ∨ (Execution.isShfl e = true ∧
        ((X.tr thread).take (index + 2)).countP Execution.isShfl +
            loaderShuffleTail 1007 1004 ≤ ((X.tr thread).take j).countP Execution.isShfl) := by
      rcases hLater with h | ⟨hMark, hSeen⟩
      · have hMin : 1007 ≤ warmKShufflePc pair := by
          fin_cases pair <;> first | exact (hZero rfl).elim | decide
        exact .inl (hMin.trans h.le)
      · exact .inr ⟨hMark, by rw [hRank, hCount, hSeen]; omega⟩
    obtain ⟨t, front, stop, _, ht, hRun, htRank, htBefore⟩ :=
      prefixRankedShuffleCut (by decide) hAudit hCounted hAt hr he hBefore hDemand hSafe
    obtain ⟨u, hLocal, hu⟩ := warmKeyColumnPrepared (g := thread) (tid := tid) ht (by simp [F])
      (by kernel_rfl)
    have hTail := hRun.after_local_nonempty hLocal (traceAfterObservedEvent he htBefore)
    refine ⟨index + 2 + front.length, htBefore, u, stop, ?_, hTail, ?_⟩
    · have hMinimal : At u 1008 ([(1998, b32 (ptr % 2 ^ 32)),
          (1999, b32 (ptr / 2 ^ 32)), (7666, b64 (16 * (tid % 8)))]) :=
        hu.mono ⟨holds_lookup hu.2.2.2.2 rfl, holds_lookup hu.2.2.2.2 rfl,
          holds_lookup hu.2.2.2.2 rfl, trivial⟩
      simpa only [warmKInputPc, warmKSlotWords, warmKInputRow, warmKShuffleInput,
        warmKInputColumn, ite_eq_right hZero, ite_eq_left hSlot, Nat.add_zero] using hMinimal
    · rw [warmKInputRank, ite_eq_right hZero, ite_eq_left hSlot]
      rw [hRank, hCount] at htRank
      omega
  · obtain ⟨index, hBefore, s, ending, hs, hr, hRank⟩ :=
      warmRoundSecondKeyReloadOfEvent hp hX hFrame hg hw hl hCTA hb hLo hHi
        he (hSecond (Nat.le_of_not_gt hSlot)) hSafe hRound
    have hZero : pair.val ≠ 0 := by omega
    refine ⟨index + 2, hBefore, s, ending, ?_, hr, ?_⟩
    · simp only [warmKInputPc, warmKSlotWords, warmKInputRow, warmKShuffleInput,
        warmKInputColumn, ite_eq_right hZero, ite_eq_right hSlot]
      exact hs.mono ⟨holds_lookup hs.2.2.2.2 rfl, holds_lookup hs.2.2.2.2 rfl,
        holds_lookup hs.2.2.2.2 rfl, trivial⟩
    · rw [warmKInputRank, ite_eq_right hZero, ite_eq_right hSlot]
      omega

end
end PTX.Kernels.TmlFa4Fwd.Loader
