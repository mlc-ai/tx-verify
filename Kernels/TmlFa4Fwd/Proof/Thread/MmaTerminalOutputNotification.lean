-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaTerminalOutputProgress

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread
open PTX PTX.AsyncCopy PTX.MBarrier

/-- A notified terminal MMA commit contributes a real unit arrival to its stage object. -/
theorem terminalOutputNotification {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) {g : Nat}
    (hCommit : Mma.TerminalOutputIssues l X g) (stage : Fin 2)
    (hNotify : ∀ i s rank target, X.Commit i s → TcCommit.target s rank = some target →
      rank ∈ X.tcNotified i) :
    ∃ r ∈ X.objects (outputCompletionObject l (g/l.block) stage), r.action = .arrive 1 0 := by
  obtain ⟨issuer,index,hWarp,hIssued⟩ := hCommit stage
  let i : EvId := (issuer,index)
  let s := Mma.commitSpec l issuer (l.sharedBase+(144+8*stage.val))
  let obj := outputCompletionObject l (g/l.block) stage
  have hTarget : TcCommit.target s 0 = some obj := by
    simp [s,obj,TcCommit.target,Mma.commitSpec,outputCompletionObject,← hWarp.1.2.2]
  have hIssue : X.Commit i s := by
    revert hIssued
    fin_cases stage
    · exact FirstOutputCommit.issued
    · exact SecondOutputCommit.issued
  have hn := hNotify _ _ _ _ hIssue hTarget
  obtain ⟨site,he⟩ := hIssue
  have hAction : objectAction X X.async obj (.async i (.tcNotify 0)) = some (.arrive 1 0) := by
    simp [objectAction, he, hTarget, hn]
  obtain ⟨r,hr,hrId⟩ := (hX.tma.2.2.1 obj).2.2 _ _ hAction
  have hMatch := ((hX.tma.2.2.1 obj).2.1 r hr).1
  rw [hrId,hAction] at hMatch
  exact ⟨r,hr,(Option.some.inj hMatch).symm⟩

end PTX.Kernels.TmlFa4Fwd.Thread
