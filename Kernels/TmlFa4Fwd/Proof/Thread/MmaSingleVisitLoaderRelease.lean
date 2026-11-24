-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaTerminalOutputProgress
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaTailValueProgress
import all Kernels.TmlFa4Fwd.Proof.Thread.MmaTerminalOutputProgress
import all Kernels.TmlFa4Fwd.Proof.Thread.MmaReadyTraversal

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX PTX.Proof PTX.Flow Prologue Epilogue
open PTX.Kernels.TmlFa4Fwd.Mma
open Observation (readyObject)

noncomputable section

/-- After the single-visit branch, the trace has at most the first K and V acquisitions. -/
theorem singleVisitReadyBudget {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hw : warpIndex l g = 12) {ends : Nat → Option TState}
    (cur : OpeningKeyReturnedWithTrip l X g 1 shuffles votes ends)
    {peer : Nat} (hPeer : SameWarp l g peer) (slot : Fin 3) :
    (atPrefix l X peer (X.tr peer).length).kvAcquires slot ≤ (2 + (2-slot.val))/3 := by
  have hWarp : warpIndex l peer = 12 := hPeer.2.symm.trans hw
  let es := (X.tr peer).filterMap readyEvent
  have hLimit : es.length ≤ 2 := by
    by_contra! hUse
    obtain ⟨j,_,hPoll,hRank⟩ := readyPollAtOrdinalBefore hp hX hPeer.1.2.1 hWarp
      (use := 2) (stop := (X.tr peer).length) (by simpa [es] using hUse)
    obtain ⟨site,he,hTagged⟩ := hPoll.useSite hp hX hWarp
    have hSite : site = readyHead 2 := by
      simpa [hRank, ReadyUseSite] using hTagged
    have hLane := Step.warpLane_of_sameWarp hPeer
    rw [← hLane] at he
    exact noSteadyEventOfSingleVisitOpening hp (Nat.mod_lt _ (by decide)) cur he
      (hSite ▸ (by decide : 2285 ≤ readyHead 2)) (hSite ▸ (by decide : readyHead 2 < 2534))
  have hSeq : ReadySequence l peer 0 es := rawReadySequence hp hX hPeer.1.2.1 hWarp
  have hCount := readySequenceSlotCount hSeq (n := es.length) (le_refl _) slot
  rw [List.take_length, Nat.zero_add, Nat.zero_add] at hCount
  have hPrefix := readyCountsAtPrefix hp hX hWarp (index := (X.tr peer).length) slot
  rw [List.take_length] at hPrefix
  change es.countP _ = _ at hPrefix
  rw [hPrefix] at hCount
  omega

end
end PTX.Kernels.TmlFa4Fwd.Thread.Mma

namespace PTX.Kernels.TmlFa4Fwd.Mma
open PTX PTX.Proof PTX.Flow Prologue Epilogue

/-- The terminal PV checkpoint issues the V-slot return before committing output. -/
theorem terminalValueReleaseOfCursor {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hMax : Maximal l kernel Assumptions.all m X)
    {g shuffles votes : Nat} (hg : g < l.threads) {ends : Nat → Option TState}
    (cur : SchedulerWarpReached l X g 2635 (fun _ => terminalPvFrame l)
      shuffles votes ends) :
    ∃ issuer index, SameWarp l g issuer ∧ X.Commit (issuer,index)
      (commitSpec l issuer (l.sharedBase+64)) := by
  obtain ⟨_,issuer,index,hWarp,he⟩ := terminalCommitStep hp hMax hg 0 cur
  have h : l.sharedBase+8+56 = l.sharedBase+64 := by omega
  change X.get (issuer,index) = some ⟨2638,.tc (.commit (commitSpec l issuer
    (l.sharedBase+8+56)))⟩ at he
  rw [h] at he
  exact ⟨issuer,index,hWarp,_,he⟩

end PTX.Kernels.TmlFa4Fwd.Mma
