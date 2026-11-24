-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmRoundKeyReload
import Kernels.TmlFa4Fwd.Proof.LoaderRankedObservation

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue

noncomputable section

set_option maxRecDepth 100000 in
/-- The first V high-word ordinal of a warm visit is beyond all warm K shuffles. -/
theorem warmRoundValueShuffleFloor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g lane batch iteration j : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hl : lane < 32)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    {e : Event} (he : X.get (warpLane l g lane, j) = some e) (hPc : 1003 < e.pc)
    (hRound : WarmRoundDemand p l X g lane batch iteration j e) (hShfl : Execution.isShfl e = true)
    (hNth : ((X.tr (warpLane l g lane)).take j).countP Execution.isShfl =
        primingSearchShuffleCount batch + 64 + 64 * iteration + 32 + 1) :
    1239 ≤ e.pc := by
  have hSafe : ∀ f, e.kind ≠ .ub f := by
    intro f h
    obtain ⟨pc, kind⟩ := e
    change kind = .ub f at h
    subst kind
    cases hShfl
  obtain ⟨i, hOrder, s, ending, hs, hr, hiRank, _⟩ :=
    warmRoundKeyPointersAtReload hp hX hFrame hg hw hl hCTA hb hLo hHi he hPc hSafe hRound
  have hAudit (bound : Nat) : ((kernel.code.drop 1003).take (1239 - 1003)).all
      (fun i => loaderPipelineCutOp 1003 1239 bound [] i.op) = true := by kernel_rfl
  have hRanked : (((kernel.code.drop 1003).take (1239 - 1003)).zipIdx 1003).all
      (fun (i, pc) => LoaderRankedInstr 1239 pc i) = true := by kernel_rfl
  have hCount : loaderShuffleTail 1239 1003 = 32 := by kernel_rfl
  obtain ⟨t, front, stop, _, ht, htRun, htRank, htBefore⟩ :=
    prefixRankedShuffleCut (by decide) hAudit hRanked (hs.mono (G := []) trivial) hr he hOrder
      (.inr ⟨hShfl, by rw [hiRank, hCount, hNth]; omega⟩) hSafe
  have hNext (bound : Nat) : ((kernel.code.drop 1239).take 2).all
      (fun i => loaderPipelineCutOp 1239 1241 bound [] i.op) = true := by kernel_rfl
  have hNextRanked : (((kernel.code.drop 1239).take 2).zipIdx 1239).all
      (fun (i, pc) => LoaderRankedInstr 1241 pc i) = true := by kernel_rfl
  have hNextCount : loaderShuffleTail 1241 1239 = 2 := by kernel_rfl
  refine (loaderRankedEventBounds (cut := 1241) (by decide) hNext hNextRanked
    ht htRun he htBefore ?_).1
  rw [htRank, hiRank, hCount, hNextCount, hNth]
  omega

end
end PTX.Kernels.TmlFa4Fwd.Loader
