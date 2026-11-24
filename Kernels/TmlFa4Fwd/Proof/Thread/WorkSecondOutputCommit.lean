-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.QueryOutputCommit
public import Kernels.TmlFa4Fwd.Proof.OutputProtection
import Kernels.TmlFa4Fwd.Proof.Thread.AllocationBarrierOrder
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStatsExit
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionSecondOutputAcquire
import Kernels.TmlFa4Fwd.Proof.Thread.CorrectionStagingAcquire
import Kernels.TmlFa4Fwd.Proof.Thread.Exit
import Lemmas.Protocol.NamedBarSources
import Kernels.TmlFa4Fwd.Proof.PollSafety
public import Lemmas.Kernel.ExitChain

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Proof PTX.AsyncCopy Epilogue Prologue

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem correctionFinalLoadBeforeOwnerExit {cta : Nat} (hGrid : cta < l.grid)
    (hWork : cta < tilePrefix p p.batch * p.heads) (hExit : CtaExited l X cta) :
    ∃ load address values finish,
      X.get load = some
        ⟨TmlFa4Fwd.Correction.finalizeLoadPc 1 0, .tc (.ld address values .s32x32b)⟩ ∧
      TraceBefore X load finish ∧ OwnerExit l X cta finish := by
  let g := cta * l.block + 256
  have hOwner : g / l.block = cta := by
    unfold g
    rw [hp.block]
    omega
  have hg : g < l.threads := by
    change cta * l.block + 256 < l.grid * l.block
    rw [hp.block]
    omega
  have hWarp : warpIndex l g = 8 := by
    unfold warpIndex g
    rw [hp.block]
    omega
  obtain ⟨exitSite, hLast⟩ := hExit g hg hOwner
  let finish : EvId := (g, (X.tr g).length - 1)
  have he : X.get finish = some ⟨exitSite, .exit⟩ := by
    simpa only [finish, Execution.get, List.getLast?_eq_getElem?] using hLast
  obtain ⟨j, _, mode, hArrival⟩ :=
    finalAllocationArrivalBeforeExit hp hX (hWarp.symm ▸ (by decide : 8 < 13)) ⟨exitSite, he⟩
  obtain ⟨i, _, _, hLoad⟩ := correctionFinalOutputLoadOfActiveTail hp hX
    (g := g) (by omega) (by omega) (hOwner.symm ▸ hWork)
      (hArrival.correctionDecoded hp hX (by omega) (by omega))
  have hLen := (List.getElem?_eq_some_iff.mp hLoad).1
  have hLe : i ≤ finish.2 := by
    change i < (X.tr g).length at hLen
    dsimp [finish]
    omega
  have hLt := hLe.lt_of_ne (fun h => by
    have hEq : (g, i) = finish := Prod.ext rfl h
    rw [hEq, he] at hLoad
    cases hLoad)
  exact ⟨(g, i), _, _, finish, hLoad,
    ⟨rfl, hLt, (List.getElem?_eq_some_iff.mp he).1⟩, hg, hOwner, exitSite, he⟩

omit hp hX in
private theorem observesOutputBeforeOwnerExit
    {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {load wait finish : EvId} (hLoad : TraceBefore X load finish) (hPo : po X wait load)
    {ref : Ref} {obj : Loc} {scope : MbarScope}
    (hObserve : WaitObserves X ref wait obj true scope) : Resumes kernel X wait finish := by
  obtain ⟨site, parity, hWait⟩ := hObserve.1
  obtain ⟨next, hSpin⟩ := actualCanonicalPoll hX hWait
  exact Resumes.of_spin hWait hSpin (hPo.1.trans hLoad.1) (hPo.2.1.trans hLoad.2.1) hLoad.2.2

/-- The correction role observes the first output commit before exiting an active CTA. -/
theorem terminalFirstOutputObservedBeforeExit {cta : Nat} (hGrid : cta < l.grid)
    (hWork : cta < tilePrefix p p.batch * p.heads) (hExit : CtaExited l X cta) :
    ∃ commit spec rank wait scope finish, FirstOutputCommit X commit spec ∧
      commit.1 / l.block = cta ∧ TcCommit.target spec rank = some (firstOutputObject l cta) ∧
      rank ∈ X.tcNotified commit ∧
      WaitObserves X (.async commit (.tcNotify rank)) wait (firstOutputObject l cta) true scope ∧
      Resumes kernel X wait finish ∧ OwnerExit l X cta finish := by
  obtain ⟨i, address, values, finish, hLoad, hBefore, hFinish⟩ :=
    correctionFinalLoadBeforeOwnerExit hp hX hGrid hWork hExit
  obtain ⟨wait, hWait, hPo⟩ :=
    Correction.firstAcquireBeforeSecondFinalizationLoad hp hX hLoad
  obtain ⟨commit, spec, rank, scope, hCommit, hLocal, hTarget, hNotify, hObserve⟩ :=
    firstOutputAcquireCommit hp hX hWait
  have hResumes := observesOutputBeforeOwnerExit hX hBefore hPo hObserve
  have hWaitOwner : wait.1 / l.block = cta := (hPo.1.trans hBefore.1) ▸ hFinish.2.1
  rw [hWaitOwner] at hTarget hObserve
  exact ⟨commit, spec, rank, wait, scope, finish, hCommit, hLocal.2.2.trans hWaitOwner,
    hTarget, hNotify, hObserve, hResumes, hFinish⟩

/-- An active CTA's correction exit certifies an actual successful O1 acquire. -/
theorem secondOutputAcquireOfWorkExit {cta : Nat} (hGrid : cta < l.grid)
    (hWork : cta < tilePrefix p p.batch * p.heads) (hExit : CtaExited l X cta) :
    ∃ wait, Correction.SecondOutputAcquire l X wait ∧ wait.1/l.block = cta := by
  obtain ⟨i,_,_,finish,hLoad,hBefore,hExit⟩ :=
    correctionFinalLoadBeforeOwnerExit hp hX hGrid hWork hExit
  obtain ⟨wait,hWait,hPo⟩ := Correction.secondAcquireBeforeFinalizationLoad hp hX hLoad
  have hOwner : wait.1/l.block = cta := (hPo.1.trans hBefore.1) ▸ hExit.2.1
  exact ⟨wait,hWait,hOwner⟩

/-- The correction role observes the last output commit before exiting a CTA with work. -/
theorem terminalOutputObservedBeforeExit {cta : Nat} (hGrid : cta < l.grid)
    (hWork : cta < tilePrefix p p.batch * p.heads) (hExit : CtaExited l X cta) :
    ∃ commit spec rank wait scope finish, SecondOutputCommit X commit spec ∧
      commit.1 / l.block = cta ∧ TcCommit.target spec rank = some (secondOutputObject l cta) ∧
      rank ∈ X.tcNotified commit ∧
      WaitObserves X (.async commit (.tcNotify rank)) wait (secondOutputObject l cta) true scope ∧
      Resumes kernel X wait finish ∧ OwnerExit l X cta finish := by
  obtain ⟨i, address, values, finish, hLoad, hBefore, hFinish⟩ :=
    correctionFinalLoadBeforeOwnerExit hp hX hGrid hWork hExit
  obtain ⟨wait, hWait, hPo⟩ := Correction.secondAcquireBeforeFinalizationLoad hp hX hLoad
  obtain ⟨commit, spec, rank, scope, hCommit, hLocal, hTarget, hNotify, hObserve⟩ :=
    secondOutputAcquireCommit hp hX hWait
  have hResumes := observesOutputBeforeOwnerExit hX hBefore hPo hObserve
  have hWaitOwner : wait.1 / l.block = cta := (hPo.1.trans hBefore.1) ▸ hFinish.2.1
  rw [hWaitOwner] at hTarget hObserve
  exact ⟨commit, spec, rank, wait, scope, finish, hCommit, hLocal.2.2.trans hWaitOwner,
    hTarget, hNotify, hObserve, hResumes, hFinish⟩

/-- The active correction warp's output load identifies the final O1 commit of its CTA. -/
theorem secondOutputCommitOfCompletedWork (hDone : Complete l X) {g : Nat} (hg : g < l.threads)
    (hWork : g / l.block < tilePrefix p p.batch * p.heads) :
    ∃ commit spec, SecondOutputCommit X commit spec ∧ g/l.block = commit.1/l.block := by
  have hExit : CtaExited l X (g / l.block) :=
    fun peer hPeer _ => (exitedOfComplete hX hDone hPeer).lastEvent hX hPeer
  obtain ⟨commit, spec, _, _, _, _, hCommit, hOwner, _⟩ :=
    terminalOutputObservedBeforeExit hp hX (NamedBar.cta_lt hg) hWork hExit
  exact ⟨commit, spec, hCommit, hOwner.symm⟩

end PTX.Kernels.TmlFa4Fwd.Thread
