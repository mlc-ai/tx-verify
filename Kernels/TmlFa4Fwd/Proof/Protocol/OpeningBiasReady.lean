-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.BiasReturnObservation
import Kernels.TmlFa4Fwd.Proof.Thread.BiasReadRendezvous
public import Kernels.TmlFa4Fwd.Proof.Thread.BiasBarrierProgress
import Kernels.TmlFa4Fwd.Proof.MbarSafety

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Bias
open PTX PTX.Flow PTX.MBarrier Prologue Epilogue Thread Thread.Loader

/-- A Bias-ready object stays within its first completed phase while a participating
lane of an active CTA still has no successful ready acquire. -/
theorem openingBiasPhaseLeOneForPendingLane {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hCuQ : DrainCuQProtected p X) {g : Nat} (stage : Fin 2)
    (hWork : g/l.block < tilePrefix p p.batch*p.heads)
    (hMember : warpIndex l g ∈ biasParticipants stage)
    (hMissing : okPolls (biasReadyObject l (g/l.block) stage) (X.tr g) = 0)
    {s : State} (hs : stateBefore (X.objects (biasReadyObject l (g/l.block) stage))
      (X.objects (biasReadyObject l (g/l.block) stage)).length = some s) :
    s.phase ≤ 1 := by
  by_contra! hPhase
  obtain ⟨i,r,⟨loader,j⟩,hRecord,hId,hExpect,hAt⟩ :=
    biasReadyExpectationOfCompletedPhase hp hX stage hs hPhase
  have hOrdinal := biasExpectationPhaseLeOrdinal hp hX stage hRecord hId hExpect hAt
  obtain ⟨_,k,phase,poll,hPoll,_,_,hSuccess,_,hSeen,_⟩ :=
    biasReuseGuardObserved hp hX stage hExpect (by omega)
  obtain ⟨ret,hReturn,hOwner,_,_,_⟩ :=
    biasEmptyObservedReturnOfWarp hp hX stage 0 hPoll hSuccess hSeen
  obtain ⟨b,hIndex,hBar,_⟩ := Scores.biasReturnRendezvousBudget hp hX stage hReturn
  have hLen : ret.2 < (X.tr ret.1).length := by
    obtain ⟨_,he⟩ := hReturn
    exact (List.getElem?_eq_some_iff.mp he).1
  have hPass : b+1 < (X.tr ret.1).length := hIndex ▸ hLen
  obtain ⟨hw, hStage⟩ := (biasParticipantIff stage (warpIndex l g)).mp hMember
  have hExited : ¬ Exited X g := by
    intro hExit
    obtain ⟨x,hExitBar⟩ := firstBiasArrivalOfActiveExit hp hX hCuQ hWork hw hExit
    rw [hStage] at hExitBar
    have hPositive := Scores.biasReadyCountOfRendezvous hp hX stage hExitBar
    omega
  obtain ⟨x,mode,hArrived,_⟩ := memberBarrierArrival hX
    (biasBarrierSources hp hX stage) (biasBarrierShape hp stage) hBar hPass
    hOwner.symm hMember (fun hExit => (hExited hExit).elim)
  have hPositive := Scores.biasReadyCountOfRendezvous hp hX stage hArrived
  omega

end PTX.Kernels.TmlFa4Fwd.Protocol.Bias
