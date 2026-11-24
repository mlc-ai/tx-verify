-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.SingleVisitProbabilityPhase
public import Kernels.TmlFa4Fwd.Proof.Protocol.JointProbabilityGate
import Kernels.TmlFa4Fwd.Proof.MbarSafety

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Scores
open PTX PTX.AsyncCopy PTX.MBarrier PTX.MbarRing Prologue Epilogue Thread.Scores

/-- A single visit supplies the softmax half of the joint object only in phase zero.
The correction lanes alone cannot complete a later 256-credit phase. -/
theorem singleVisitEarlyObservedPhaseZero {p : Params} {l : Launch} {m : Mem0}
    {X : Execution} (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    (hDone : Complete l X) (hFrame : OutputFootprint p X)
    (hGuard : CorrectionJointGuards l X)
    {batch cta : Nat} (hb : batch < p.batch) (hLo : tilePrefix p batch * p.heads ≤ cta)
    (hHi : cta < tilePrefix p (batch+1) * p.heads)
    (hTrip : Mma.trips p batch (assignedCoordinates p batch cta).1 = 1)
    (stage : Fin 2) {k : Nat} {poll : Record Ref}
    (hRecord : (X.objects (probabilityObject l cta stage 0))[k]? = some poll)
    (hAction : poll.action = .pollParity 0 true) (hSuccess : poll.reply.waited = some true) :
    observedAt (X.objects (probabilityObject l cta stage 0)) k = some 0 := by
  classical
  let loc := probabilityObject l cta stage 0
  let log := X.objects loc
  have hChecked := X.objects_checked hX loc
  have hInit := probabilityInitialized hp hX stage 0 (List.mem_of_getElem? hRecord)
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have hUnit {r : Record Ref} (hr : r ∈ log) (hu : CounterUpdate r.action) :
      r.action = .arrive 1 0 := by
    obtain ⟨_,_,_,_,ha⟩ := probabilityUpdate hp hX stage 0 hr hu
    exact ha
  have hIncr : incrementsBefore log log.length = 0 := by
    apply incrementsBefore_length_of
    intro r hr hInc
    have h := hUnit hr (by rw [hInc]; trivial)
    rw [hInc] at h
    cases h
  obtain ⟨st,parity,hState,hAct,hOpposite,hReply⟩ := hChecked.okPoll hRecord hSuccess
  have hParity : parity = 0 := (Action.pollParity.inj (hAct.symm.trans hAction)).1
  have hPositive : 0 < st.phase := by rw [hParity] at hOpposite; omega
  let phase := st.phase-1
  have hObserve : observedAt log k = some phase := by
    change (log[k]?).bind (·.reply.completed) = some phase
    rw [hRecord, Option.bind_some, hReply, ite_eq_left hPositive]
  suffices hZero : phase = 0 by rwa [hZero] at hObserve
  by_contra hLater
  let credits := (Finset.range log.length).filter (UnitArrivalIn log phase)
  let creditLane (n : Nat) : Nat :=
    match (log[n]?.getD poll).id with
    | .thread e => e.1 % l.block - 256
    | .async .. => 0
  have hCard : credits.card = 256 := by
    exact hChecked.card_unit_arrivals_phase hNo (q := phase)
      (fun _ r count tx hr _ ha =>
        (Action.arrive.inj (ha.symm.trans (hUnit (List.mem_of_getElem? hr)
          (by rw [ha]; trivial)))).1)
      (fun _ _ _ h => PairTmaRing.expected_of_init hX hInit hNo h) hIncr
      (List.getElem?_eq_some_iff.mp hRecord).1.le hState (show phase < st.phase by
        dsimp [phase]
        omega)
  have source {n : Nat} (hn : n ∈ credits) :
      ∃ (r : Record Ref) (i : EvId), log[n]? = some r ∧ r.id = .thread i ∧
        ProbabilityCredit l X i cta stage 0 ∧ i.1/l.block = cta ∧
        256 ≤ i.1%l.block ∧ i.1%l.block < 384 ∧
        probabilityOrdinal l X cta stage 0 i = phase ∧ creditLane n = i.1%l.block-256 := by
    obtain ⟨_,r,tx,hr,hArrive,_,hPhase⟩ := Finset.mem_filter.mp hn
    have hUpdate : CounterUpdate r.action := by rw [hArrive]; trivial
    obtain ⟨i,hId,hCredit,hCta,_⟩ := probabilityUpdate hp hX stage 0
      (List.mem_of_getElem? hr) hUpdate
    have hExact := (jointProbabilityCreditPhaseExact hp hX hGuard stage hr hUpdate hId).2
    have hOrdinal : probabilityOrdinal l X cta stage 0 i = phase :=
      Option.some.inj (hExact.symm.trans hPhase)
    have hRole : 8 ≤ warpIndex l i.1 ∧ warpIndex l i.1 < 12 := by
      rcases (probabilityCreditRole hp hX stage 0 hCredit).2 with h | h
      · exact (hLater (hOrdinal.symm.trans
          (singleVisitSoftmaxCreditOrdinalZero hp hX hDone hFrame
            hb hLo hHi hTrip stage 0 h.1 hCredit))).elim
      · exact h.2
    change 8 ≤ (i.1%l.block)/32 ∧ (i.1%l.block)/32 < 12 at hRole
    exact ⟨r,i,hr,hId,hCredit,hCta,by omega,by omega,hOrdinal,by
      simp only [creditLane,hr,Option.getD_some,hId]⟩
  have hMap {n : Nat} (hn : n ∈ credits) : creditLane n ∈ Finset.range 128 := by
    obtain ⟨_,_,_,_,_,_,hLo,hHi,_,hLabel⟩ := source hn
    rw [Finset.mem_range,hLabel]
    omega
  have hInject : Set.InjOn creditLane credits := by
    intro a ha b hb hEq
    obtain ⟨r,i,hr,hId,hC,hCta,hLo,_,hOrd,hLabel⟩ := source ha
    obtain ⟨s,j,hs,hJd,hD,hJCta,hJLo,_,hJOrd,hJLabel⟩ := source hb
    rw [hLabel,hJLabel] at hEq
    have hMod : i.1 % l.block = j.1 % l.block := by omega
    have hSame : i.1 = j.1 := by
      calc
        i.1 = i.1 % l.block + l.block * (i.1/l.block) := (Nat.mod_add_div ..).symm
        _ = j.1 % l.block + l.block * (j.1/l.block) := by rw [hMod,hCta,hJCta]
        _ = j.1 := Nat.mod_add_div ..
    have hE := probabilityOrdinalInjective hC hD hSame (hOrd.trans hJOrd.symm)
    exact ObjectInit.checked_record_index_eq hChecked hr hs (by simp only [hId,hJd,hE])
  have hFit := Finset.card_le_card_of_injOn creditLane (fun _ => hMap) hInject
  rw [hCard,Finset.card_range] at hFit
  omega

end PTX.Kernels.TmlFa4Fwd.Protocol.Scores
