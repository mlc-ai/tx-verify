-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmRoundKeyReload
import Kernels.TmlFa4Fwd.Proof.LoaderWarmSecondReload
import Kernels.TmlFa4Fwd.Proof.LoaderRankedObservation

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue

noncomputable section

set_option maxRecDepth 100000 in
/-- The trace ordinal places the upper-half K broadcasts after the second scratch load. -/
theorem warmRoundHighShuffleFloor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g src batch iteration j : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hl : src < 32)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    {e : Event} (he : X.get (warpLane l g src, j) = some e) (hLate : 1003 < e.pc)
    (hRound : WarmRoundDemand p l X g src batch iteration j e) (hShfl : Execution.isShfl e = true)
    (hRankLo : primingSearchShuffleCount batch + 64 + 64 * iteration + 16 ≤
      ((X.tr (warpLane l g src)).take j).countP Execution.isShfl)
    (hRankHi : ((X.tr (warpLane l g src)).take j).countP Execution.isShfl <
      primingSearchShuffleCount batch + 64 + 64 * iteration + 32) :
    1073 ≤ e.pc := by
  have hSafe : ∀ f, e.kind ≠ .ub f := by
    intro f he
    obtain ⟨pc, kind⟩ := e
    change kind = .ub f at he
    subst kind
    cases hShfl
  obtain ⟨index, hBefore, s, ending, hs, hr, hRank, _⟩ :=
    warmRoundKeyPointersAtReload hp hX hFrame hg hw hl hCTA hb hLo hHi he hLate hSafe hRound
  have hStart : At s 1003 [] := hs.mono trivial
  have hAudit (n : Nat) : ((kernel.code.drop 1003).take (1073 - 1003)).all
      (fun ins => loaderPipelineCutOp 1003 1073 n [] ins.op) = true := by kernel_rfl
  have hRanked : (((kernel.code.drop 1003).take (1073 - 1003)).zipIdx 1003).all
      (fun (ins, pc) => LoaderRankedInstr 1073 pc ins) = true := by kernel_rfl
  have hCount : loaderShuffleTail 1073 1003 = 16 := by kernel_rfl
  obtain ⟨t, front, stop, _, ht, htRun, htRank, htBefore⟩ :=
    prefixRankedShuffleCut (by decide) hAudit hRanked hStart hr he hBefore
      (.inr ⟨hShfl, by rw [hRank, hCount]; exact hRankLo⟩) hSafe
  let thread := warpLane l g src
  let nextIndex := index + front.length
  have hAfter (n : Nat) : ((kernel.code.drop 1073).take (1131 - 1073)).all
      (fun ins => loaderPipelineCutOp 1073 1131 n [] ins.op) = true := by kernel_rfl
  have hAfterRanked : (((kernel.code.drop 1073).take (1131 - 1073)).zipIdx 1073).all
      (fun (ins, pc) => LoaderRankedInstr 1131 pc ins) = true := by kernel_rfl
  have hAfterCount : loaderShuffleTail 1131 1073 = 16 := by kernel_rfl
  refine (loaderRankedEventBounds (by decide) hAfter hAfterRanked ht htRun he htBefore ?_).1
  rw [htRank, hRank, hCount, hAfterCount]
  omega

end
end PTX.Kernels.TmlFa4Fwd.Loader
