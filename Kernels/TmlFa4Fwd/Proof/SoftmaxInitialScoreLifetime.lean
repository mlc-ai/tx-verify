-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.SoftmaxFirstScoreValues
import Kernels.TmlFa4Fwd.Proof.Thread.AllocationBarrierRelease
import Kernels.TmlFa4Fwd.Proof.MmaResources
import Lemmas.Tmem.TmemPairHistory

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Softmax
open PTX PTX.Proof PTX.TcMma PTX.Tmem.Pair

private theorem scoreReleaseOwner {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X)
    {cta : Nat} {r : Requests} (hr : r ∈ X.tmemHistory cta) {cell : Cell} {e d : EvId}
    (hCover : Covers l X r cell.cta e cell.column) (hRelease : ReleaseOf l X r d) :
    d.1 / l.block = cell.cta ∧ Thread.Deallocation X d := by
  obtain ⟨_,_,_,hOwn,_,_,_⟩ := hCover
  rcases hRelease with hRelease | ⟨q,hPair,_⟩
  · obtain ⟨n,base,pc,_,⟨group,he⟩,hSame | ⟨hOther,_⟩⟩ := hRelease
    · obtain ⟨lane,hLane,_,_⟩ := hSame
      refine ⟨?_,Thread.Deallocation.of_decoded he⟩
      rw [hOwn,hLane]
      exact (WarpRequest.event_props ((hX.tmemPair.1 cta).1 r hr).2.2 lane).1
    · exact ⟨hOther.trans hOwn.symm,Thread.Deallocation.of_decoded he⟩
  · obtain ⟨_,⟨req,hRecord,_,hTwo⟩,_⟩ := hX.tmemPair.2.1 q hPair
    have hValid := (hX.tmemPair.1 q.1.cta).1 req hRecord
    have hOne := (Mma.actualResourceRequest hX (hValid.2.2.2.2.1 0)).1
    exact CtaGroup.noConfusion (hTwo.symm.trans hOne)

/-- A score load whose actual wait has been reached retains the result until deallocation. -/
theorem initialScoreLoadLive {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g read complete : Nat} {source : EvId} {cell : Cell} {addr : Nat} {vals : List Value}
    (hOwner : cell.cta = g / l.block) (hLoad : X.TLd (g,read) addr vals .s32x32b)
    (hComplete : X.get (g,complete) = some ⟨4826,.tc .waitLd⟩) (hLater : read < complete) :
    SourceLive l X source (g,read) cell := by
  obtain ⟨_,he⟩ := hLoad
  intro cta r hr hCover d hRelease
  obtain ⟨hCta,hRelease⟩ := scoreReleaseOwner hX hr hCover hRelease
  have hData : Thread.TensorDataEvent X (g,complete) :=
    ⟨_,hComplete,.inl rfl⟩
  have hDone := Thread.tensorDataBeforeDeallocation hp hX (hOwner.symm.trans hCta.symm)
    hData hRelease
  left
  refine ⟨fun _ => ⟨(g,complete),⟨4826,hComplete⟩,rfl,hLater,.inl hDone⟩,?_,?_⟩
  · rintro ⟨a,values,shape,pc,hStore⟩
    rw [he] at hStore
    cases hStore
  · rintro (⟨_,_,_,_,_,hMma⟩ | ⟨_,_,hCopy⟩ | ⟨_,_,hShift⟩)
    · rw [he] at hMma
      cases hMma
    · rw [he] at hCopy
      cases hCopy
    · rw [he] at hShift
      cases hShift

/-- The initial score acquire completes each MMA before the CTA can deallocate its accumulator. -/
theorem initialScoreAccumulatorLive {p : Params} {l : Launch} {m : Mem0} {X : Execution}
    (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {stage : Fin 2} {producer consumer commit wait issue read prev : Nat}
    (hPhase : FirstQkPhase l X stage producer consumer commit wait)
    {dst : Nat} {spec : OperandSpec} {acc : Bool} {mask : List Nat}
    (hIssue : X.MmaIssue (producer,issue) dst spec acc mask) (hBefore : issue < commit)
    (q : Fin 4) {vals : List Value}
    (he : X.get (consumer,read) = some
      ⟨scorePc .first q,.tc (.ld (scoreAddress l consumer stage q) vals .s32x32b)⟩)
    (hAfter : wait < read) {cell : Cell} (hOwner : cell.cta = consumer / l.block) :
    SourceLive l X (producer,prev) (producer,issue) cell := by
  intro cta r hr hCover release hRelease
  obtain ⟨hCta,hRelease⟩ := scoreReleaseOwner hX hr hCover hRelease
  have hData : Thread.TensorDataEvent X (consumer,read) := ⟨_,he,.inl rfl⟩
  have hBeforeRelease := Thread.tensorDataBeforeDeallocation hp hX
    (hOwner.symm.trans hCta.symm) hData hRelease
  have hLen : read < (X.tr consumer).length := (List.getElem?_eq_some_iff.mp he).1
  have hPO : po X (consumer,wait) (consumer,read) :=
    po_of_not_access rfl hAfter hLen (by rw [he]; rfl)
  obtain ⟨pc,hi⟩ := hIssue
  left
  refine ⟨?_,?_,fun hAsync => .inl ⟨(consumer,wait),.cta,
    firstQkPhase_observed hX hPhase hAsync hBefore,
    MbarRing.Unit.Gate.scopesMeet hPhase.sameCta .cluster .cta,
    Relation.TransGen.head (.inl hPO) hBeforeRelease⟩⟩
  · rintro ⟨a,vals,shape,pc',hLoad⟩
    rw [hi] at hLoad
    cases hLoad
  · rintro ⟨a,vals,shape,pc',hStore⟩
    rw [hi] at hStore
    cases hStore

end PTX.Kernels.TmlFa4Fwd.Softmax
