-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmRoundPageWords
public import Kernels.TmlFa4Fwd.Proof.LoaderWarmPointerPrefix

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue

noncomputable section

/-- Any observed warm K traversal saves the current descending tile's two row
pointers, and both stores remain latest at the real first pointer load. -/
theorem warmRoundKeyPointersAtReload {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g lane j batch iteration : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hl : lane < 32)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    {e : Event} (he : X.get (warpLane l g lane, j) = some e)
    (hPc : 1003 < e.pc) (hSafe : ∀ f, e.kind ≠ .ub f)
    (hDemand : WarmRoundDemand p l X g lane batch iteration j e) :
    let co := assignedCoordinates p batch (g / l.block)
    let thread := warpLane l g lane
    let tid := thread % l.block
    let trips := Mma.trips p batch co.1
    let row := primingLaneRow (trips - 2 - iteration) tid
    ∃ pos ≤ j, ∃ s ending,
      At s 1003 (warmCacheFrame p l batch (co.2 / 6) trips (warpIndex l g) tid) ∧
      Run kernel Assumptions.all l thread s ((X.tr thread).drop pos) ending ∧
      ((X.tr thread).take pos).countP Execution.isShfl =
        primingSearchShuffleCount batch + 64 + 64 * iteration ∧
      ∀ slot : Fin 2, ∃ write < pos,
        X.Writes (thread, write) (pointerSaveAccess l thread 0 slot)
          (b64 (primingKRowPointer p batch (co.2 / 6) (row + 64 * slot.val))).toBytes ∧
        ∀ byte < 8, ∀ k < pos, ∀ a, X.Access (thread, k) a true →
          a.Covers ((pointerSaveAccess l thread 0 slot).loc.at byte) → k ≤ write := by
  obtain ⟨pos, hFirst, hSecond, hBefore, s, ending, hs, hr, hsRank⟩ :=
    warmRoundPageWordsOfEvent hp hX hFrame hg hw hl hCTA hb hLo hHi he
      (by omega) hSafe hDemand
  obtain ⟨seed, hLower, hUpper, hUnwritten, hShuffle, v, mid, hv, hvRun⟩ :=
    warmKeyPointerCursorFromPages hs hr he hBefore (by omega) hSafe
  let co := assignedCoordinates p batch (g / l.block)
  let thread := warpLane l g lane
  let tid := thread % l.block
  let trips := Mma.trips p batch co.1
  let F := warmCacheFrame p l batch (co.2 / 6) trips (warpIndex l g) tid
  have hHead := (assignedCoordinates_valid hp hLo hHi).2
  have hh : co.2 / 6 < p.kvHeads := by dsimp [co]; unfold Params.heads at hHead; omega
  have hv' : At v 966 ([(9537, b64 0), (9, .pred true)] ++ F) :=
    hv.mono ⟨hv.2.2.2.2.1, hv.2.2.2.2.2.2.1, hv.2.2.2.2.2.2.2⟩
  obtain ⟨endPos, hEnd, hFinal, u, stop, hu, huRun, hSaves⟩ :=
    warmKeyPointersAtReloadFromCursor hp hX hb hh hFirst hSecond hLower hUnwritten
      hv' hvRun he hUpper hPc hSafe
  exact ⟨endPos, hEnd, u, stop, hu, huRun, hFinal.trans (hShuffle.trans hsRank), hSaves⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
