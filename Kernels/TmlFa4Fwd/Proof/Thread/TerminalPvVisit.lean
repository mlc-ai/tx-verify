-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaSteadyReadyExtent
import Kernels.TmlFa4Fwd.Proof.Thread.WorkSecondOutputCommit
import Kernels.TmlFa4Fwd.Proof.Thread.MmaMaximalCacheExtent
import Kernels.TmlFa4Fwd.Proof.Thread.MmaFirstGroupShuffles
import Kernels.TmlFa4Fwd.Proof.Termination
import Kernels.TmlFa4Fwd.Proof.Thread.Exit
import Lemmas.Kernel.Existence
import Lemmas.Step.ExitLast

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX PTX.Proof PTX.Flow Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Mma

noncomputable section

/-- The selected terminal PV uses the last V packet of the request. Completion
lets the maximal extension recover the metadata cursor while retaining the lane trace. -/
theorem terminalFragmentUseOfCompletedWork {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X)
    (hFrame : ∀ Y, Consistent l kernel Assumptions.all m Y → OutputFootprint p Y)
    {g index batch d : Nat} {stage : Fin 2} {step : Fin 8}
    {op : TcMma.OperandSpec} {accum : Bool} {mask : List Nat}
    (hFragment : PvInstruction X (g,index) (firstPvBlock false stage) step d op accum mask)
    (hb : batch < p.batch) (hLo : tilePrefix p batch*p.heads ≤ g/l.block)
    (hHi : g/l.block < tilePrefix p (batch+1)*p.heads) :
    LatestValueReadyUse l X g index
      (2 * trips p batch (assignedCoordinates p batch (g/l.block)).1 - 1) := by
  have hg := event_thread_lt hX hFragment.decoded
  have hWork := hHi.trans_le (Nat.mul_le_mul_right p.heads
    (tilePrefix_mono p (show batch+1 ≤ p.batch by omega)))
  obtain ⟨final,spec,hFinal,hCta⟩ := secondOutputCommitOfCompletedWork hp hX hDone
    hg hWork
  have hBefore := mmaBeforeSameCtaSecondOutputCommit hp hX ⟨_,hFragment.decoded⟩ hFinal hCta
  have hIssuer : g = final.1 := hBefore.1
  obtain ⟨Y,hY,hPrefix,hLargest⟩ := bounded_largest_extension (terminates hp) hX
  have hMax : Maximal l kernel Assumptions.all m Y :=
    ⟨hY,fun Z hZ hExt => hLargest Z hZ (Execution.le_trans hPrefix hExt)⟩
  have hFinalY := hFinal.mono hPrefix
  have hFragY := PvInstruction.of_decoded (Execution.le_get hPrefix hFragment.decoded)
  obtain ⟨pos,t,s,ending,_,_,_,_,_,hAt,hPast,hLocal,hRun⟩ :=
    Allocation.mmaMetadataOfMaximal hp hMax (event_thread_lt hY hFinalY.decoded)
      (hFinalY.issuerWarp hp hY) ((hFrame Y hY).metadataProtected hp).1 hb
      (hCta ▸ hLo) (hCta ▸ hHi)
  have hReached := selectedMetadataBeforeBodyEvent hPast hLocal hAt.1 hFinalY.decoded
    (show 2110 ≤ (2646 : Nat) by decide)
  obtain ⟨finish,⟨pc,kind⟩,hExit,hKind⟩ :=
    exitedOfComplete hX hDone (event_thread_lt hX hFinal.decoded)
  change kind = .exit at hKind
  subst kind
  have hExitY := Execution.le_get hPrefix hExit
  have hLastX := Execution.exit_last hX (event_thread_lt hX hFinal.decoded) hExit
  have hLastY := Execution.exit_last hY (event_thread_lt hY hFinalY.decoded) hExitY
  have hIndex := len_of_get hFinalY.decoded
  change final.2 < (Y.tr final.1).length at hIndex
  have hLocalExit : ((Y.tr final.1).drop pos)[finish-pos]? = some ⟨pc,.exit⟩ := by
    rwa [List.getElem?_drop,Nat.add_sub_of_le (show pos ≤ finish by omega)]
  have hPresent : (Y.tr final.1).drop pos ≠ [] := by
    intro hNil
    simp [hNil] at hLocalExit
  have hEnding : ending = none := by
    cases h : ending with
    | none => rfl
    | some u =>
      rw [h] at hRun
      exact (hRun.no_exit hLocalExit).elim
  have hTail := (hEnding ▸ hRun).after_local_nonempty hLocal hPresent
  have hExact := tailFragmentUseOfSelectedTerminal hp hY (hFrame Y hY) hFinalY hb
    (assignedCoordinates_valid hp (hCta ▸ hLo) (hCta ▸ hHi)).1 hAt hTail hCta hFragY
  have hTr : Y.tr g = X.tr g := by
    rw [hIssuer]
    obtain ⟨suffix,hSuffix⟩ := hPrefix.1 final.1
    rw [← hSuffix] at hLastY
    have hEmpty : suffix = [] := List.length_eq_zero_iff.mp (by simp at hLastY; omega)
    simp [← hSuffix,hEmpty]
  have hUse := hExact.1
  rw [← hCta] at hUse
  obtain ⟨wait,hPoll,hCount,hOdd,hBefore,hOnly⟩ := hUse
  obtain ⟨e,hGet,hKind⟩ := hPoll
  exact ⟨wait,⟨e,by simpa only [Execution.get,hTr] using hGet,hKind⟩,
    by simpa only [readyCount,hTr] using hCount,hOdd,
    ⟨rfl,hBefore.2.1,len_of_get hFragment.decoded⟩,fun j slot parity hj hi hPoll => by
      have hForward : ReadyPoll l Y g j slot parity true .cta := by
        obtain ⟨e,hR,hKind⟩ := hPoll
        exact ⟨e,Execution.le_get hPrefix hR,hKind⟩
      simpa only [readyCount,hTr] using hOnly j slot parity hj hi hForward⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Mma
