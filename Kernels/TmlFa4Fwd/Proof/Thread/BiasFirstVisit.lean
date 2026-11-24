-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstBiasSources
import Kernels.TmlFa4Fwd.Proof.MmaReadyHistory
import Lemmas.Protocol.PairTmaRing.Order

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Scores
open PTX PTX.AsyncCopy PTX.MBarrier Softmax

noncomputable section

/-- This lane passed the initial acquire for its stage's pair of Bias boxes. -/
def FirstBiasAcquire (l : Launch) (X : Execution) (g wait : Nat) (stage : Fin 2) : Prop :=
  X.get (g, wait) = some ⟨3498, .wait (waitLoc l g stage 2) 0 true true .cta⟩

theorem FirstBiasAcquire.pollRecord {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g wait : Nat} {stage : Fin 2} (hWait : FirstBiasAcquire l X g wait stage) :
    ∃ (j : Nat) (r : Record Ref), (X.objects (waitLoc l g stage 2))[j]? = some r ∧
      r.id = .thread (g, wait) ∧ r.action = .pollParity 0 true ∧
      r.fault = none ∧ r.reply.waited = some true :=
  actualPollRecordClean hp hX hWait

theorem FirstBiasAcquire.observes {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {g wait bytes : Nat} {stage : Fin 2} {tensor : EvId}
    (hWait : FirstBiasAcquire l X g wait stage)
    (hNote : objectAction X X.async (waitLoc l g stage 2) (.async tensor (.notify .load)) =
      some (.completeTx bytes))
    (hOrd : UpdateBeforeWait (X.objects (waitLoc l g stage 2)) (.async tensor (.notify .load))
      (.thread (g, wait))) :
    AsyncObserved X tensor (.notify .load) (g, wait) true .cta :=
  PairTmaRing.tensorObserved_of_notified hX hNote hWait hOrd

theorem FirstBiasAcquire.target {l : Launch} {X : Execution} {g wait : Nat}
    {stage : Fin 2} {loc : Loc} (hWait : FirstBiasAcquire l X g wait stage)
    (hActual : ∃ site parity, X.get (g, wait) = some ⟨site, .wait loc parity true true .cta⟩) :
    loc = waitLoc l g stage 2 := by
  obtain ⟨_, _, hActual⟩ := hActual
  exact (Kind.wait.inj (congrArg Event.kind (Option.some.inj (hActual.symm.trans hWait)))).1

/-- A real observation made by the opening acquire uses that acquire's object and scope. -/
theorem FirstBiasAcquire.ownObservation {l : Launch} {X : Execution}
    {g wait : Nat} {stage : Fin 2} (hWait : FirstBiasAcquire l X g wait stage)
    {source : Ref} (hObserved : MbarObserved X source (.thread (g,wait))) :
    WaitObserves X source (g,wait) (waitLoc l g stage 2) true .cta := by
  obtain ⟨_,i,loc,acq,scope,hId,hObserve,_⟩ := hObserved
  obtain rfl : i = (g,wait) := (Ref.thread.inj hId).symm
  obtain ⟨_,_,he⟩ := hObserve.1
  have hSame := Kind.wait.inj (congrArg Event.kind (Option.some.inj (he.symm.trans hWait)))
  obtain ⟨rfl,_,_,rfl,rfl⟩ := hSame
  exact hObserve

end
end PTX.Kernels.TmlFa4Fwd.Thread.Scores
