-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.MmaReady
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderReadyFacts

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.Proof PTX.MBarrier PTX.MbarRing PTX.AsyncCopy

/-- A successful parity-zero ready poll has a real publication to its cache slot. -/
theorem publicationOfReadyPollZero {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g index : Nat} (slot : Fin 3) (h : Thread.Mma.ReadyPoll l X g index slot 0 true .cta) :
    ∃ source, X.AsyncArrive source (readyObject l g slot) true := by
  obtain ⟨⟨pc,kind⟩,he,hKind⟩ := h
  cases hKind
  let loc := readyObject l g slot
  have hGet : X.get (g,index) = some ⟨pc,.wait loc 0 true true .cta⟩ := he
  obtain ⟨hObj,k,poll,hRecord,hPoll,hSuccess⟩ := Loader.actualReadyAcquireRecord hp hX slot hGet
  change (X.objects loc)[k]? = some poll at hRecord
  have hAction : objectAction X X.async loc (.thread (g,index)) = some (.pollParity 0 true) := by
    simp [objectAction,hGet]
  have hActual := ((hX.tma.2.2.1 loc).2.1 poll (List.mem_of_getElem? hRecord)).1
  rw [hPoll,hAction] at hActual
  have hChecked := X.objects_checked hX loc
  obtain ⟨s,parity,hs,hParity,hOpposite,hCompleted⟩ := hChecked.okPoll hRecord hSuccess
  have hEq : parity = 0 :=
    (Action.pollParity.inj (hParity.symm.trans (Option.some.inj hActual).symm)).1
  have hPositive : 0 < s.phase := by
    rw [hEq] at hOpposite
    omega
  have hObserved : observedAt (X.objects loc) k = some (s.phase-1) := by
    change ((X.objects loc)[k]?).bind (·.reply.completed) = _
    rw [hRecord,Option.bind_some,hCompleted,ite_eq_left hPositive]
  classical
  obtain ⟨hCount,hPackets⟩ := Loader.readyPhaseObserved hX slot rfl hGet hObj hRecord hPoll
    hSuccess hObserved
  have hCount' : ((Finset.range (X.objects loc).length).filter
      (UnitArrivalIn (X.objects loc) (s.phase-1))).card = 64 := hCount
  have hNonempty := (show 0 < 64 by decide)
  rw [← hCount'] at hNonempty
  obtain ⟨j,hJ⟩ := Finset.card_pos.mp hNonempty
  obtain ⟨_,i,pc',hIssue,_,_⟩ := hPackets j hJ
  exact ⟨i,pc',hIssue⟩

end PTX.Kernels.TmlFa4Fwd.Thread.Loader
