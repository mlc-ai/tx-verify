-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderRecurringPageRefresh
public import Kernels.TmlFa4Fwd.Proof.LoaderPrefixStableCut

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Loader
open PTX PTX.Flow PTX.Proof

def scratchExit (site : Fin 2) : Nat := if site = 0 then 957 else 1427

private def traversalEnd (site : Fin 2) : Nat := if site = 0 then 1348 else 1741

/-- A loader that has left the scratch slots cannot make that traversal's lookup
again. A return to the scratch slots must first cross the traversal's shuffles. -/
theorem noPageAfterSlotsAtSameRank {l : Launch} {X : Execution} {g pos j : Nat}
    (site : Fin 2) {s : TState} {ending : Option TState} (hs : s.pc = scratchExit site)
    (hSub : s.sub = 0) (hAcc : s.acc = []) (hFault : s.fault = none)
    (hr : Run kernel Assumptions.all l g s ((X.tr g).drop pos) ending)
    {a : Acc} {bytes : List (Option Byte)} (hPos : pos ≤ j)
    (he : X.get (g, j) = some ⟨(recurringPageReadSite site).pc, .rd a bytes⟩)
    (hRank : ((X.tr g).take j).countP Execution.isShfl =
      ((X.tr g).take pos).countP Execution.isShfl) : False := by
  let lo := scratchExit site
  let hi := traversalEnd site
  have hRange : 174 ≤ lo ∧ lo ≤ hi ∧ hi ≤ 1901 := by fin_cases site <;> decide
  have hOutside : (recurringPageReadSite site).pc < lo := by fin_cases site <;> decide
  have hAudit (branch : Nat) : ((kernel.code.drop lo).take (hi - lo)).all
      (fun ins => loaderPipelineCutOp lo hi branch [] ins.op) = true := by
    fin_cases site <;> set_option maxRecDepth 100000 in kernel_rfl
  have hCount : (((kernel.code.drop lo).take (hi - lo)).zipIdx lo).all
      (fun (ins, pc) => LoaderRankedInstr hi pc ins) = true := by
    fin_cases site <;> set_option maxRecDepth 100000 in kernel_rfl
  have hNonzero : 0 < loaderShuffleTail hi lo := by
    fin_cases site <;> decide +kernel
  have hAt : At s lo [] := ⟨hs, hSub, hAcc, hFault, trivial⟩
  rcases prefixProjectionsCutOrEvent (F := []) hRange hAudit
    (fun (_ : Unit) => loaderShuffleTail hi) (fun _ => Execution.isShfl)
    (fun _ => by simp [loaderShuffleTail])
    (fun hlo hhi hstep _ => rankedLoaderStep hRange hCount hlo hhi hstep)
    hAt hr he hPos (by intro _ h; cases h) with ⟨hLower, _, _⟩ |
      ⟨next, hNext, _, _, _, _, hNextRank⟩
  · exact (Nat.not_le_of_gt hOutside) hLower
  · have hLe := countP_take_mono Execution.isShfl (X.tr g) hNext
    have hCount := hNextRank ()
    omega

end PTX.Kernels.TmlFa4Fwd.Loader
