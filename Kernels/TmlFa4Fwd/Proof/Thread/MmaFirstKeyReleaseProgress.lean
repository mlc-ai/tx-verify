-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReleaseOrdinal
public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReadyTraversal
import Kernels.TmlFa4Fwd.Proof.Thread.MmaReleaseSource

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Mma
open PTX PTX.Proof Prologue
open PTX.Kernels.TmlFa4Fwd.Mma

/-- A lane participating in a cache release has recorded its opening K acquire. -/
theorem ReleaseIssue.peerFirstKeyAcquire {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g peer index : Nat} {form : ReleaseForm} {spec : TcCommit.Spec}
    (hRelease : ReleaseIssue X g index form spec) (hPeer : SameWarp l g peer) :
    ∃ i, ReadyPoll l X peer i 0 0 true .cta ∧ (atPrefix l X peer i).kvAcquires 0 = 0 := by
  obtain ⟨j, loc, parity, he, _, _⟩ := hRelease.readyOccurrence hp hX hPeer
  let ev : Event := ⟨(slotWait (releaseIndex form)).pc,.wait loc parity true true .cta⟩
  have hMark : (readyEvent ev).isSome = true := by
    cases form <;> rfl
  have hPresent : ev ∈ (X.tr peer).take (j+1) := by
    apply List.mem_of_getElem? (i := j)
    rw [List.getElem?_take_of_lt (Nat.lt_succ_self _)]
    exact he
  have hLen : 0 < (((X.tr peer).take (j+1)).filterMap readyEvent).length := by
    rw [List.length_filterMap_eq_countP, List.countP_pos_iff]
    exact ⟨ev,hPresent,hMark⟩
  have hw : warpIndex l peer = 12 := hPeer.2.symm.trans (hRelease.issuerWarp hp hX)
  obtain ⟨i,_,hi,hRank⟩ := readyPollAtOrdinalBefore hp hX hPeer.1.2.1 hw hLen
  have hCount := readyUsesAtPrefix hp hX hPeer.1.2.1 hw i
  exact ⟨i,hi,by omega⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Mma
