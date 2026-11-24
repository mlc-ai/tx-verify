-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.RecurringCacheCoverage
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReadyToFinalRelease
import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderPhaseAlignment
import Kernels.TmlFa4Fwd.Proof.Protocol.LoaderActualReady
import Kernels.TmlFa4Fwd.Proof.Thread.OutputCommitOrder

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol
open PTX PTX.Proof Thread
open PTX.Kernels.TmlFa4Fwd.Mma
open PTX.Kernels.TmlFa4Fwd.Loader (kvUseStage)
open Protocol.LoaderReady

namespace LoaderReady

/-- An actual ready poll on the final issuer supplies its completed generation. -/
theorem completedAtFinalReady {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g wait final use : Nat} {output : TcCommit.Spec}
    (hFinal : SecondOutputCommit X (g,final) output)
    (hReady : Thread.Mma.ReadyPoll l X g wait (readyStage use) (readyWord use) true .cta)
    (hRank : Thread.Mma.readyCount X g wait = use) :
    Nonempty (Completed l X (g,wait) (kvUseStage use) (use/3)) := by
  let slot := kvUseStage use
  have hw : Prologue.warpIndex l g = 12 := hFinal.issuerWarp hp hX
  have hg : g < l.threads := event_thread_lt hX hFinal.decoded
  have hCounts := Thread.Mma.readyUsesAtPrefix hp hX hg hw wait
  have hUse : (Thread.Mma.atPrefix l X g wait).kvAcquires 0 +
      (Thread.Mma.atPrefix l X g wait).kvAcquires 1 +
      (Thread.Mma.atPrefix l X g wait).kvAcquires 2 = use := hCounts.symm.trans hRank
  have hPhase := (hReady.exactOccurrence hp hX hw).2.1
  rw [hUse] at hPhase
  have hIssuer {h i : Nat} {form : Thread.Mma.ReleaseForm} {spec : TcCommit.Spec}
      (he : Thread.Mma.ReleaseIssue X h i form spec) (hCta : g/l.block = h/l.block) : g = h :=
    hFinal.sameReleaseIssuer hp hX he hCta
  have hCompleted := completedForObservedIssuer hp hX hw hIssuer hReady
    (actualEmptyGuardLower hp hX g slot)
  rw [hPhase] at hCompleted
  exact hCompleted

end LoaderReady

namespace Output

/-- Every byte of a V generation already acquired by the final issuer has an
actual consuming fragment before O1. The release notification can still be pending. -/
theorem observedValueReadyBeforeFinal {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g wait final use : Nat} {output : TcCommit.Spec}
    (hFinal : SecondOutputCommit X (g,final) output)
    (hReady : Thread.Mma.ReadyPoll l X g wait (readyStage use) (readyWord use) true .cta)
    (hRank : Thread.Mma.readyCount X g wait = use) (hOdd : use % 2 = 1)
    (hBefore : TraceBefore X (g,wait) (g,final))
    (stage : Fin 2) (lane : Fin 64) (pair : Fin 16) (upper : Bool) {off : Nat} (hOff : off < 16) :
    CacheUseBeforeCommit l X (g,final) (kvUseStage use) (use/3)
      ⟨.shared, g / l.block,
        kvCopyAddress l.sharedBase (kvUseStage use) lane pair upper + off⟩ := by
  obtain ⟨steady, commit, release, hRelease, hObs, hOrdinal, _, hEnd⟩ :=
    Thread.Mma.valueReadyReleaseIssueBeforeFinal hp hX hFinal hReady hRank hOdd hBefore
  let slot := kvUseStage use
  obtain ⟨step, index, hCoord⟩ :=
    valueVectorHasOperandCoordinate l g (firstPvBlock steady stage) slot lane pair upper
      hp.shared.1 hOff
  obtain ⟨j,d,op,accum,mask,hFragment,hStart,hMiddle⟩ :=
    hRelease.valueBank hp hX steady hOrdinal stage step
  have hSteady : decide ((firstPvBlock steady stage).val < 2) = steady := by
    cases steady <;> fin_cases stage <;> rfl
  have hB := Thread.Mma.valueFragmentDescriptorOfReadyAndRelease hp hX hFragment
    (hSteady.symm ▸ hObs) hReady (hSteady.symm ▸ hOrdinal) hStart hMiddle
  obtain ⟨_,_,hDescriptor,hLow,hHigh⟩ := hFragment.valueOperand hp hX
  have hSame : op.byteLoc .b index =
      (pvOperands l g (firstPvBlock steady stage) step slot.val).byteLoc .b index := by
    simp only [TcMma.OperandSpec.byteLoc, pvOperands, hB, hDescriptor, hLow, hHigh,
      reduceCtorEq, false_and, ↓reduceIte]
    rfl
  have hCompleted := completedAtFinalReady hp hX hFinal hReady hRank
  exact ⟨(g,wait),(g,j),d,op,accum,mask,index,hCompleted,hStart,hMiddle.trans hEnd,
    ⟨_,hFragment.decoded⟩,hSame.trans hCoord⟩

end Output
end PTX.Kernels.TmlFa4Fwd.Protocol
