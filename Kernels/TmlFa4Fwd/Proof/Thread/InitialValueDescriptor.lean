-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.InitialValueRoute
public import Kernels.TmlFa4Fwd.Proof.MmaInitialValueSend

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.Flow PTX.Proof Prologue
open PTX.Kernels.TmlFa4Fwd.Mma (initialMmaTrace valueDescriptorEvent
  initialValueSendBeforeEventInWalk readyHead readyEvent valueDescriptorSite valueDescriptorLow
  valueDescriptorReceivedFromPeer)
open Mma.Observation (readyObject)

noncomputable section

/-- The initial V descriptor broadcast sends the physical slot-one word. Its received
word is recorded separately because the instruction broadcasts from warp lane zero. -/
def InitialValueDescriptorSend (l : Launch) (X : Execution) (id : EvId)
    (recv : Value) (valid : Bool) : Prop :=
  ∃ steady, X.get id = some (valueDescriptorEvent l steady recv valid)

/-- The actual state and visit suffix after the value descriptor broadcast. -/
structure InitialValueReplyCursor (l : Launch) (X : Execution) (commit : EvId) where
  steady : Bool
  index : Nat
  word : Value
  valid : Bool
  state : TState
  visits : List Visit
  send : X.get (commit.1,index) = some (valueDescriptorEvent l steady word valid)
  beforeCommit : TraceBefore X (commit.1,index) commit
  atState : At state ((valueDescriptorSite steady).prepare + 9)
    [((valueDescriptorSite steady).output, word), (1062, b32 12)]
  suffix : Walk kernel Assumptions.all l commit.1 state ((X.tr commit.1).drop (index+1)) visits

private theorem markReady (gate : Fin 4) (loc : Loc) (parity : Nat) :
    readyEvent ⟨readyHead gate, .wait loc parity true true .cta⟩ = some (loc, parity) := by
  have h : (List.finRange 4).any (fun i => readyHead i == readyHead gate) = true :=
    List.any_eq_true.mpr ⟨gate, by simp, beq_self_eq_true _⟩
  simp [readyEvent,h]

/-- Recover the actual cursor after the initial value broadcast on the final O1 issuer. -/
theorem initialValueReplyBeforeSecondOutputCommit {p : Params} {l : Launch}
    {m : Mem0} {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {commit : EvId} {spec : TcCommit.Spec} (hCommit : SecondOutputCommit X commit spec) :
    Nonempty (InitialValueReplyCursor l X commit) := by
  obtain ⟨g,j⟩ := commit
  let target : Event := ⟨2646, .tc (.commit spec)⟩
  have hCommitGet : X.get (g,j) = some target := hCommit.decoded
  have hw : warpIndex l g = 12 := by
    have hBody := roleBodyPcOfEvent hp hX hCommitGet (show 173 < 2646 by decide)
      (show 2646 ∉ registerHintSites by decide)
    change roleBodyPc (warpIndex l g) 2646 at hBody
    unfold roleBodyPc at hBody
    rcases hBody with h | h
    · omega
    · split_ifs at h <;> omega
  obtain ⟨value, hv, hvOrder, hvOrd⟩ := initialValueAcquireBeforeSecondOutputCommit hp hX hCommit
  have hValueBefore : value < j := hvOrder.2.1
  have hBefore : 0 < (((X.tr g).take value).filterMap readyEvent).length := by
    change (((X.tr g).take value).filterMap readyEvent).length = 1 at hvOrd
    omega
  obtain ⟨key, hKeyBefore, hk, _⟩ :=
    Mma.readyPollAtOrdinalBefore hp hX (event_thread_lt hX hCommitGet) hw hBefore
  obtain ⟨keyGate, hKey⟩ := hk.atGate hp hX hw
  obtain ⟨valueGate, hValue⟩ := hv.atGate hp hX hw
  have hKeyLo : 2145 ≤ readyHead keyGate := by fin_cases keyGate <;> decide
  have hKeyHi : readyHead keyGate < 2768 := by fin_cases keyGate <;> decide
  obtain ⟨base,s,_,hBase,hs,hWalk⟩ := initialMmaTrace hp hX hKey hKeyLo hKeyHi
  let es := (X.tr g).drop (base+1)
  let keyEvent : Event := ⟨readyHead keyGate, .wait (readyObject l g 0) 0 true true .cta⟩
  have hKeyAt : es[key-(base+1)]? = some keyEvent := by
    dsimp only [es]
    rw [List.getElem?_drop, Nat.add_sub_of_le (show base+1 ≤ key by omega)]
    exact hKey
  let valueEvent : Event := ⟨readyHead valueGate, .wait (readyObject l g 1) 0 true true .cta⟩
  have hVAt : es[value-(base+1)]? = some valueEvent := by
    dsimp only [es]
    rw [List.getElem?_drop, Nat.add_sub_of_le (show base+1 ≤ value by omega)]
    exact hValue
  have hCommitAt : es[j-(base+1)]? = some target := by
    dsimp only [es]
    rw [List.getElem?_drop, Nat.add_sub_of_le (show base+1 ≤ j by omega)]
    exact hCommitGet
  have hTwo : 1 < ((es.take (j-(base+1))).filterMap readyEvent).length :=
    twoReadyProjections hKeyAt hVAt (by omega) (by omega)
      (markReady keyGate _ _) (markReady valueGate _ _)
  have hs' : At s 1908 (PTX.Kernels.TmlFa4Fwd.Mma.readyFrame l) :=
    hs.mono ⟨hs.2.2.2.2.2.1, hs.2.2.2.2.1, trivial⟩
  obtain ⟨steady, u, recv, ok, pre, tail, nextVisits, hEs, hLt, hu, hUWalk⟩ :=
    initialValueSendBeforeEventInWalk hp hs' hWalk hCommitAt (show 2559 < 2646 by decide) hTwo
  let send : EvId := (g, base+1+pre.length)
  change es = pre ++ valueDescriptorEvent l steady recv ok :: tail at hEs
  have hSendAt : es[pre.length]? = some (valueDescriptorEvent l steady recv ok) := by
    rw [hEs, List.getElem?_append_right le_rfl, Nat.sub_self]
    rfl
  have hSend : X.get send = some (valueDescriptorEvent l steady recv ok) := by
    change ((X.tr g).drop (base+1))[pre.length]? = _ at hSendAt
    rw [List.getElem?_drop] at hSendAt
    exact hSendAt
  have hRest : (X.tr g).drop (send.2+1) = tail := by
    change (X.tr g).drop ((base+1+pre.length)+1) = tail
    rw [← List.drop_drop, ← List.drop_drop]
    change ((es.drop pre.length).drop 1) = tail
    rw [hEs,List.drop_append_length]
    rfl
  exact ⟨⟨steady,send.2,recv,ok,u,nextVisits,hSend,
    ⟨rfl, by dsimp [send]; omega, (List.getElem?_eq_some_iff.mp hCommitGet).1⟩,hu,
    hRest.symm ▸ hUWalk⟩⟩

/-- When both actual sends are paired by the same shuffle ordinal, the issuing
lane receives the physical slot-one descriptor computed by lane zero. -/
theorem InitialValueDescriptorSend.receivesFromLaneZero {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g i j ordinal : Nat}
    {recv sourceRecv : Value} {ok sourceOk : Bool}
    (here : InitialValueDescriptorSend l X (g,i) recv ok)
    (peer : InitialValueDescriptorSend l X (g-laneOf l g,j) sourceRecv sourceOk)
    (hereOrdinal : X.ShflK (g,i) ordinal) (peerOrdinal : X.ShflK (g-laneOf l g,j) ordinal) :
    recv = b32 (valueDescriptorLow l 1) := by
  obtain ⟨_, hHere⟩ := here
  obtain ⟨_, hPeer⟩ := peer
  exact valueDescriptorReceivedFromPeer hX hHere hereOrdinal hPeer peerOrdinal

end
end PTX.Kernels.TmlFa4Fwd.Thread
