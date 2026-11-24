-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderWarmRoundKeyReload
import Kernels.TmlFa4Fwd.Proof.LoaderRankedObservation

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof Prologue Epilogue

noncomputable section

/-- The first shuffle in each of the two V pointer halves. -/
def warmValueHalfStart (slot : Fin 2) : Nat := if slot.val = 0 then 1239 else 1293

set_option maxRecDepth 100000 in
/-- A peer ordinal in a warm V half reaches that half's pointer reload. -/
theorem warmRoundValuePeerFloor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X) (hFrame : OutputFootprint p X)
    {g lane batch iteration j : Nat} (hg : g < l.threads) (hw : 14 ≤ warpIndex l g) (hl : lane < 32)
    (hCTA : g / l.block < tilePrefix p p.batch * p.heads)
    (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ g / l.block)
    (hHi : g / l.block < tilePrefix p (batch + 1) * p.heads)
    {e : Event} (he : X.get (warpLane l g lane, j) = some e) (hPc : 1003 < e.pc)
    (hRound : WarmRoundDemand p l X g lane batch iteration j e) (hShfl : Execution.isShfl e = true)
    (slot : Fin 2)
    (hEnough : primingSearchShuffleCount batch + 64 + 64 * iteration + 32 + 16 * slot.val ≤
      ((X.tr (warpLane l g lane)).take j).countP Execution.isShfl)
    (hBeforeEnd : ((X.tr (warpLane l g lane)).take j).countP Execution.isShfl <
      primingSearchShuffleCount batch + 64 + 64 * iteration + 64) :
    warmValueHalfStart slot ≤ e.pc := by
  have hSafe : ∀ f, e.kind ≠ .ub f := by
    intro f h
    obtain ⟨pc, kind⟩ := e
    change kind = .ub f at h
    subst kind
    cases hShfl
  obtain ⟨i, hOrder, s, ending, hs, hr, hiRank, _⟩ :=
    warmRoundKeyPointersAtReload hp hX hFrame hg hw hl hCTA hb hLo hHi he hPc hSafe hRound
  let cut := warmValueHalfStart slot
  have hRange : 174 ≤ 1003 ∧ 1003 ≤ cut ∧ cut ≤ 1901 := by fin_cases slot <;> decide
  have hAudit (bound : Nat) : ((kernel.code.drop 1003).take (cut - 1003)).all
      (fun i => loaderPipelineCutOp 1003 cut bound [] i.op) = true := by
    fin_cases slot <;> kernel_rfl
  have hRanked : (((kernel.code.drop 1003).take (cut - 1003)).zipIdx 1003).all
      (fun (i, pc) => LoaderRankedInstr cut pc i) = true := by fin_cases slot <;> kernel_rfl
  have hCount : loaderShuffleTail cut 1003 = 32 + 16 * slot.val := by
    fin_cases slot <;> kernel_rfl
  obtain ⟨t, front, stop, _, ht, htRun, htRank, htBefore⟩ :=
    prefixRankedShuffleCut (F := []) hRange hAudit hRanked (hs.mono (G := []) trivial) hr he hOrder
      (.inr ⟨hShfl, by rw [hiRank, hCount]; omega⟩) hSafe
  have hNextRange : 174 ≤ cut ∧ cut ≤ 1348 ∧ 1348 ≤ 1901 := by fin_cases slot <;> decide
  have hNext (bound : Nat) : ((kernel.code.drop cut).take (1348 - cut)).all
      (fun i => loaderPipelineCutOp cut 1348 bound [] i.op) = true := by
    fin_cases slot <;> kernel_rfl
  have hNextRanked : (((kernel.code.drop cut).take (1348 - cut)).zipIdx cut).all
      (fun (i, pc) => LoaderRankedInstr 1348 pc i) = true := by fin_cases slot <;> kernel_rfl
  have hNextCount : loaderShuffleTail 1348 cut = 32 - 16 * slot.val := by
    fin_cases slot <;> kernel_rfl
  refine (loaderRankedEventBounds hNextRange hNext hNextRanked ht htRun he htBefore ?_).1
  rw [htRank, hiRank, hCount, hNextCount]
  have hSlot := slot.isLt
  omega

end
end PTX.Kernels.TmlFa4Fwd.Loader
