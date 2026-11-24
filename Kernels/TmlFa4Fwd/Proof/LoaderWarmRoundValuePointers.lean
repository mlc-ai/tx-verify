-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmRoundPageWords
public import Kernels.TmlFa4Fwd.Proof.LoaderWarmValueSaves

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue

noncomputable section

/-- In every observed warm traversal, the V pointer saves consume both actual
page and row cells of that traversal's descending logical tile. -/
theorem warmRoundValuePointerSavesOfEvent {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g lane j batch iteration : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hl : lane < 32)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    {e : Event} (he : X.get (warpLane l g lane, j) = some e)
    (hPc : 1223 < e.pc) (hSafe : ∀ f, e.kind ≠ .ub f)
    (hDemand : WarmRoundDemand p l X g lane batch iteration j e) :
    let co := assignedCoordinates p batch (g / l.block)
    let thread := warpLane l g lane
    let tid := thread % l.block
    let trips := Mma.trips p batch co.1
    let tile := trips - 2 - iteration
    ∃ pos ≤ j, ∃ s ending,
      At s 1227 (warmCacheFrame p l batch (co.2 / 6) trips (warpIndex l g) tid) ∧
      Run kernel Assumptions.all l thread s ((X.tr thread).drop pos) ending ∧
      ((X.tr thread).take pos).countP Execution.isShfl =
        primingSearchShuffleCount batch + 64 + 64 * iteration + 32 ∧
      ∀ slot : Fin 2, ∃ write < pos,
        X.Writes (thread, write) (pointerSaveAccess l thread 1 slot)
          (b64 (primingVRowPointer p batch (co.2 / 6)
            (primingLaneRow tile tid + 64 * slot.val))).toBytes ∧
        ∀ k < 8, ∀ i < pos, ∀ a, X.Access (thread, i) a true →
          a.Covers ((pointerSaveAccess l thread 1 slot).loc.at k) → i ≤ write := by
  obtain ⟨pagePos, hPage0, hPage1, hBefore, raw, ending, hAt, hRun, hRank⟩ :=
    warmRoundPageWordsOfEvent hp hX hFrame hg hw hl hCTA hb hLo hHi he (by omega) hSafe hDemand
  obtain ⟨seed, hSeed, hSeedRun, pos, hBaseBefore, hOrder, s, stop, hs, hsRun, hsRank⟩ :=
    warmValueSaveStartFromPages hAt hRun he hBefore (by omega) hSafe
  let co := assignedCoordinates p batch (g / l.block)
  have hHead := (assignedCoordinates_valid hp hLo hHi).2
  have hh : co.2 / 6 < p.kvHeads := by dsimp [co]; unfold Params.heads at hHead; omega
  obtain ⟨last, hLast, u, hu, huRun, huRank, hSaves⟩ :=
    warmValuePointersFromPageHistory hp hX hb hh hPage0 hPage1 hSeed hSeedRun hBaseBefore
      hs hsRun hsRank he hOrder hPc
  exact ⟨last, hLast, u, stop, hu, huRun, huRank.trans (hsRank.trans (congrArg (· + 32) hRank)),
    hSaves⟩

end
end PTX.Kernels.TmlFa4Fwd.Loader
