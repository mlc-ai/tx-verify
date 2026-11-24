-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaInitialKeyReady
import Kernels.TmlFa4Fwd.Proof.Thread.MmaReadyTraversal
import Kernels.TmlFa4Fwd.Proof.Thread.MmaIssueElection
import Kernels.TmlFa4Fwd.Proof.MmaReleaseOrdinals

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX PTX.Proof
open PTX.Kernels.TmlFa4Fwd.Mma (initialQkBlock qkPc slotWait slotElect pendingReadyOrdinal
  initialReadyPollOperands readyHead readyEvent ReadyUseSite)

/-- An actual opening QK fragment follows the first ready acquire of slot zero. -/
theorem InitialQueryFragment.keyReadyInPrefix {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {stage : Fin 2} {mma : EvId} (hInit : InitialQueryFragment X stage mma) :
    ∃ wait, ReadyPoll l X mma.1 wait 0 0 true .cta ∧
      TraceBefore X (mma.1,wait) mma ∧ (atPrefix l X mma.1 wait).kvAcquires 0 = 0 := by
  obtain ⟨g,index⟩ := mma
  obtain ⟨step,d,op,accum,mask,he⟩ := hInit
  have hMma : X.MmaIssue (g,index) d op accum mask := ⟨_,he⟩
  have hWarp : Prologue.warpIndex l g = 12 := (mmaIssueElection hp hX hMma).1
  have hGate : (slotWait 0).pc + 3 ≤ qkPc (initialQkBlock stage) + step.val ∧
      qkPc (initialQkBlock stage) + step.val ≤ (slotElect 0).pc := by
    fin_cases stage <;> fin_cases step <;> decide
  obtain ⟨wait,hBefore,_,_,_,_,hKey,_⟩ := pendingReadyOrdinal hp hX 0 he hGate
  obtain ⟨rfl,rfl,rfl,rfl⟩ := initialReadyPollOperands hp hX hKey
  have hPoll : ReadyPoll l X g wait 0 0 true .cta := ⟨_,hKey,rfl⟩
  obtain ⟨pc,hGet,hUse⟩ := hPoll.useSite hp hX hWarp
  have hPc : pc = readyHead 0 := congrArg Event.pc (Option.some.inj (hGet.symm.trans hKey))
  rw [hPc] at hUse
  have hFirst : (((X.tr g).take wait).filterMap readyEvent).length = 0 := by
    rcases hUse with ⟨_,hZero⟩ | ⟨hOther,_,_⟩ | ⟨hOther,_⟩
    · exact hZero
    · exact (by decide : readyHead 0 ≠ readyHead 2) hOther |>.elim
    · rcases hOther with hOther | hOther
      · exact (by decide : readyHead 0 ≠ readyHead 1) hOther |>.elim
      · exact (by decide : readyHead 0 ≠ readyHead 3) hOther |>.elim
  have hExact := hPoll.exactOccurrence hp hX hWarp
  have hCount := readyUsesAtPrefix hp hX (event_thread_lt hX hKey) hWarp wait
  dsimp only at hExact hCount
  rw [← hCount,hFirst] at hExact
  exact ⟨wait,hPoll,⟨rfl,hBefore,len_of_get he⟩,hExact.2.1⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Mma
