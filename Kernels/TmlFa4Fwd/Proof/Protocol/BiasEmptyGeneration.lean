-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.BiasReadyAccounting
public import Kernels.TmlFa4Fwd.Proof.Thread.SoftmaxBiasPhase
import Kernels.TmlFa4Fwd.Proof.MbarSafety
import Lemmas.Order.DependencyWitness
import Lemmas.Protocol.GatedFaults

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Bias
open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier PTX.EventFrame PTX.Proof Thread.Loader

/-- The ordinal of a source arrival in its physical issuer's stage history. -/
def biasArrivalOrdinal (X : Execution) (object : Loc) (issue : EvId) : Nat :=
  arrivals object ((X.tr issue.1).take issue.2)

/-- Each return follows a successful observation that has already completed at least the
return's own local ordinal on the ready object. -/
def BiasReturnReadyLower (l : Launch) (X : Execution) (cta : Nat) (stage : Fin 2) : Prop :=
  ∀ e, X.Arrive e (biasEmptyObject l cta stage) 0 1 true .cta →
    let log := X.objects (biasReadyObject l cta stage)
    ∃ (k i phase : Nat) (r : Record Ref),
      log[i]? = some r ∧ r.id = .thread (e.1,k) ∧ r.reply.waited = some true ∧
      observedAt log i = some phase ∧ biasArrivalOrdinal X (biasEmptyObject l cta stage) e ≤ phase ∧
      Resumes kernel X (e.1,k) e

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem biasEmptyInitialized {cta : Nat} (stage : Fin 2) {r : Record Ref}
    (hr : r ∈ X.objects (biasEmptyObject l cta stage)) :
    PairTmaRing.InitFirst X (biasEmptyObject l cta stage) 4 := by
  fin_cases stage
  · exact (activeObjectHistory hp hX (32 : Fin 34) hr).1
  · exact (activeObjectHistory hp hX (33 : Fin 34) hr).1

private theorem biasReturnGate {cta : Nat} (stage : Fin 2)
    (hReady : BiasReturnReadyLower l X cta stage) {e : EvId}
    (hIssue : X.Arrive e (biasEmptyObject l cta stage) 0 1 true .cta)
    (hPositive : 0 < biasArrivalOrdinal X (biasEmptyObject l cta stage) e) :
    let log := X.objects (biasEmptyObject l cta stage)
    ∃ (i : Nat) (poll : Record Ref) (s : State),
      log[i]? = some poll ∧ poll.reply.waited = some true ∧
      stateBefore log i = some s ∧ biasArrivalOrdinal X (biasEmptyObject l cta stage) e ≤ s.phase ∧
      Relation.TransGen (DepStep l kernel X) (poll.id, true) (.thread e, false) := by
  let loc := biasEmptyObject l cta stage
  let log := X.objects loc
  obtain ⟨k, j, q, ready, hRecord, hRid, hReply, hObs, hLower, hTail⟩ := hReady e hIssue
  obtain ⟨⟨g,r⟩, he, hObserved, hOrdinal⟩ :=
    biasObservedExpectation hp hX stage hRecord hReply hObs
  change 0 < biasArrivalOrdinal X loc e at hPositive
  change biasArrivalOrdinal X loc e ≤ q at hLower
  change q ≤ arrivals (biasReadyObject l cta stage) ((X.tr g).take r) at hOrdinal
  have hP : 0 < arrivals (biasReadyObject l cta stage) ((X.tr g).take r) := by
    omega
  obtain ⟨a, i, phase, poll, hAt, hId, _, hSuccess, hFirst, hPhase, hBound⟩ :=
    biasReuseGuardObserved hp hX stage he hP
  obtain ⟨s, hs, hS⟩ := (X.objects_checked hX loc).observed_phase hAt hSuccess hPhase
  rw [hRid] at hObserved
  have hDep := (Relation.TransGen.single (DepStep.of_resumes l hFirst)).tail
    (DepStep.of_witness l (Witness.of_mbarObserved hObserved))
  have hPath := hDep.tail (DepStep.of_resumes l hTail)
  rw [← hId] at hPath
  refine ⟨i, poll, s, hAt, hSuccess, hs, ?_, hPath⟩
  change biasArrivalOrdinal X loc e ≤ s.phase
  omega

omit hp hX in
private def biasReturnLabel (l : Launch) (X : Execution) (loc : Loc) :
    Ref → Fin 4 × Nat
  | .thread e => (⟨Prologue.warpIndex l e.1 % 4, Nat.mod_lt _ (by decide)⟩,
      biasArrivalOrdinal X loc e)
  | .async .. => (0, 0)

/-- All real Bias-empty releases are fault-free and are recorded at their local generation,
as soon as the consumer's actual ready observation supplies the ordinal lower bound. -/
theorem biasEmptyReleaseGenerationOfReadyLower {cta i : Nat} (stage : Fin 2)
    (hReady : BiasReturnReadyLower l X cta stage) {r : Record Ref}
    (hr : (X.objects (biasEmptyObject l cta stage))[i]? = some r) {e : EvId}
    (hId : r.id = .thread e) (hAct : r.action = .arrive 1 0) :
    r.fault = none ∧ phaseAt (X.objects (biasEmptyObject l cta stage)) i =
      some (biasArrivalOrdinal X (biasEmptyObject l cta stage) e) := by
  let loc := biasEmptyObject l cta stage
  let log := X.objects loc
  let label := biasReturnLabel l X loc
  have hInit := biasEmptyInitialized hp hX stage (List.mem_of_getElem? hr)
  have hNo := objects_noInval hX.tma.2.2.1 (fun i _ => noMbarInval hX (i := i)) loc
  have hChecked := X.objects_checked hX loc
  have hFrom {w : Record Ref} (hw : w ∈ log) {n tx : Nat} (ha : w.action = .arrive n tx) :
      ∃ j, w.id = .thread j ∧ X.Arrive j loc 0 1 true .cta ∧ j.1 / l.block = cta ∧
        Prologue.warpIndex l j.1 < 8 ∧ Prologue.warpIndex l j.1 / 4 = stage.val ∧
        n = 1 ∧ tx = 0 := by
    obtain ⟨j, hId, hi, hCta, hWarp, hStage, hAct⟩ :=
      Thread.Softmax.biasEmptyUpdate hp hX stage hw (ha.symm ▸ trivial)
    obtain ⟨rfl,rfl⟩ := Action.arrive.inj (ha.symm.trans hAct)
    exact ⟨j, hId, hi, hCta, hWarp, hStage, rfl, rfl⟩
  have hUnit {w : Record Ref} (hw : w ∈ log) {n tx : Nat} (ha : w.action = .arrive n tx) :
      n = 1 ∧ tx = 0 := by
    obtain ⟨_, _, _, _, _, _, hh⟩ := hFrom hw ha
    exact hh
  have hNoComplete (w : Record Ref) (hw : w ∈ log) (n : Nat) : w.action ≠ .completeTx n := by
    intro ha
    obtain ⟨_, _, _, _, _, _, hEq⟩ :=
      Thread.Softmax.biasEmptyUpdate hp hX stage hw (ha.symm ▸ trivial)
    rw [ha] at hEq
    cases hEq
  have hNoIncrement : incrementsBefore log log.length = 0 := by
    apply incrementsBefore_length_of
    intro w hw ha
    obtain ⟨_, _, _, _, _, _, hEq⟩ :=
      Thread.Softmax.biasEmptyUpdate hp hX stage hw (ha.symm ▸ trivial)
    rw [ha] at hEq
    cases hEq
  have hGated := hChecked.gated_arrive hNo (Finset.univ : Finset (Fin 4)) label
    (fun j s hLen hs => ⟨by
      have h := PairTmaRing.expected_of_init hX hInit hNo hs
      simpa using h,
      MbarRing.tx_zero_of hX hNo (fun _ hw _ _ ha => (hUnit hw ha).2) hNoComplete hLen hs⟩)
    (fun j w _ _ hj ha => by
      obtain ⟨_, s, hs, _⟩ := PairTmaRing.state_of_init hX hInit hNo hj
        (by intro n; rw [ha]; simp)
      exact ⟨s, hs⟩)
    (fun _ _ _ _ hw ha => ⟨(hUnit (List.mem_of_getElem? hw) ha).1,
      (hUnit (List.mem_of_getElem? hw) ha).2, Finset.mem_univ _⟩)
    (fun k k' w w' _ _ _ _ hw hw' ha ha' hEq => by
      obtain ⟨⟨g,j⟩, hI, hE, hC, hW, hS, _, _⟩ := hFrom (List.mem_of_getElem? hw) ha
      obtain ⟨⟨g',j'⟩, hI', hE', hC', hW', hS', _, _⟩ := hFrom (List.mem_of_getElem? hw') ha'
      rw [hI, hI'] at hEq
      have hEqWarp : Prologue.warpIndex l g % 4 = Prologue.warpIndex l g' % 4 := by
        have hEq' := congrArg (fun x : Fin 4 × Nat => x.1.val) hEq
        exact hEq'
      have hWarp : Prologue.warpIndex l g = Prologue.warpIndex l g' := by
        change Prologue.warpIndex l g / 4 = stage.val at hS
        change Prologue.warpIndex l g' / 4 = stage.val at hS'
        omega
      have hWarp' : SameWarp l g g' :=
        ⟨⟨Thread.Softmax.arrivalIssuerPresent hX hE, Thread.Softmax.arrivalIssuerPresent hX hE',
          hC.trans hC'.symm⟩, hWarp⟩
      have hSame := Thread.Softmax.biasReturnSameWarpIssuer hp hX stage hE hE' hWarp'
      change g = g' at hSame
      subst g'
      have hJ := Thread.Softmax.arrivalOrdinalInjective hE hE' (congrArg Prod.snd hEq)
      subst j'
      exact ObjectInit.checked_record_index_eq hChecked hw hw' (hI.trans hI'.symm))
    (fun k w _ _ hw ha hPos => by
      obtain ⟨j, hI, hE, _, _, _, _, _⟩ := hFrom (List.mem_of_getElem? hw) ha
      rw [hI] at hPos ⊢
      change 0 < biasArrivalOrdinal X loc j at hPos
      obtain ⟨q, poll, s, hAt, hReply, hs, hLower, hPath⟩ :=
        biasReturnGate hp hX stage hReady hE hPos
      have hNot := MbarRing.Round.Slot.not_before_of_reach (m := loc) hX hPath
      have hBefore : q < k := by
        rcases Nat.lt_trichotomy q k with h | rfl | h
        · exact h
        · have hEq := Option.some.inj (hAt.symm.trans hw)
          subst poll
          obtain ⟨_, _, _, hPoll, _, _⟩ := hChecked.okPoll hw hReply
          rw [ha] at hPoll
          cases hPoll
        · exact (hNot ⟨k, q, w, poll, hw, hI, hAt, rfl, h⟩).elim
      exact ⟨q, poll, s, hBefore, hAt, hReply, hs, hLower⟩)
    hNoIncrement i r 1 0 hr hAct
  rw [hId] at hGated
  exact hGated


/-- Each physical softmax warp supplies one unit for its Bias generation, with no fault. -/
theorem biasEmptyReleaseGeneration {cta i : Nat} (stage : Fin 2) {r : Record Ref}
    (hr : (X.objects (biasEmptyObject l cta stage))[i]? = some r) {e : EvId}
    (hId : r.id = .thread e) (hAct : r.action = .arrive 1 0) :
    r.fault = none ∧ phaseAt (X.objects (biasEmptyObject l cta stage)) i =
      some (biasArrivalOrdinal X (biasEmptyObject l cta stage) e) :=
  biasEmptyReleaseGenerationOfReadyLower hp hX stage
    (fun _ hi => Thread.Softmax.biasReadyObservedOfReturn hp hX stage hi) hr hId hAct

/-- Initialization, polls, and every generation of returns on a Bias-empty object are safe. -/
theorem biasEmptyHistoryClean {cta : Nat} (stage : Fin 2) {r : Record Ref}
    (hr : r ∈ X.objects (biasEmptyObject l cta stage)) : r.fault = none := by
  have hUpd (h : CounterUpdate r.action) : r.fault = none := by
    obtain ⟨issue, hId, _, _, _, _, ha⟩ := Thread.Softmax.biasEmptyUpdate hp hX stage hr h
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
    exact (biasEmptyReleaseGeneration hp hX stage hi hId ha).1
  cases ha : r.action with
  | init n => exact actualInitOrPollClean hp hX hr (.inl ⟨n, ha⟩)
  | pollParity q ok => exact actualInitOrPollClean hp hX hr (.inr ⟨q, ok, ha⟩)
  | inval => exact (objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) _ _ hr ha).elim
  | increment | completeTx | arrive => exact hUpd (ha.symm ▸ trivial)

/-- A loader's completed Bias-empty observation sees an actual softmax return of that generation. -/
theorem biasEmptyObservedReturn {cta j phase : Nat} (stage : Fin 2) {poll : Record Ref}
    (hj : (X.objects (biasEmptyObject l cta stage))[j]? = some poll)
    (hSuccess : poll.reply.waited = some true)
    (hPhase : observedAt (X.objects (biasEmptyObject l cta stage)) j = some phase) :
    ∃ e, X.Arrive e (biasEmptyObject l cta stage) 0 1 true .cta ∧
      biasArrivalOrdinal X (biasEmptyObject l cta stage) e = phase ∧
      MbarObserved X (.thread e) poll.id := by
  classical
  let loc := biasEmptyObject l cta stage
  let log := X.objects loc
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have hChecked := X.objects_checked hX loc
  have hInit := biasEmptyInitialized hp hX stage (List.mem_of_getElem? hj)
  obtain ⟨s, hs, hP⟩ := hChecked.observed_phase hj hSuccess hPhase
  have hLt : phase < s.phase := by omega
  have hInc : incrementsBefore log log.length = 0 := by
    apply incrementsBefore_length_of
    intro r hr ha
    obtain ⟨_, _, _, _, _, _, hb⟩ :=
      Thread.Softmax.biasEmptyUpdate hp hX stage hr (ha.symm ▸ trivial)
    rw [ha] at hb
    cases hb
  have hUnit (i : Nat) (r : Record Ref) (units bytes : Nat) (hr : log[i]? = some r)
      (_ : r.fault = none) (ha : r.action = .arrive units bytes) : units = 1 := by
    obtain ⟨_, _, _, _, _, _, hb⟩ := Thread.Softmax.biasEmptyUpdate hp hX stage
      (List.mem_of_getElem? hr) (ha.symm ▸ trivial)
    exact (Action.arrive.inj (ha.symm.trans hb)).1
  have hCard := hChecked.card_unit_arrivals_phase hNo hUnit
    (fun _ _ _ hs => PairTmaRing.expected_of_init hX hInit hNo hs) hInc
    (List.getElem?_eq_some_iff.mp hj).1.le hs hLt
  have hPos : 0 < ((Finset.range log.length).filter (fun i => UnitArrivalIn log phase i)).card :=
    hCard.symm ▸ (by decide : 0 < 4)
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hPos
  obtain ⟨_, r, tx, hr, ha, hf, hQ⟩ := Finset.mem_filter.mp hi
  obtain ⟨e, hId, hIssue, _, _, _, hb⟩ := Thread.Softmax.biasEmptyUpdate hp hX stage
    (List.mem_of_getElem? hr) (ha.symm ▸ trivial)
  have hReal := (biasEmptyReleaseGeneration hp hX stage hr hId hb).2
  rw [hQ] at hReal
  have hObs := hX.observed_of_phase hNo hr hf (hb.symm ▸ trivial) hj hSuccess hQ hPhase
  rw [hId] at hObs
  exact ⟨e, hIssue, (Option.some.inj hReal).symm, hObs⟩
end PTX.Kernels.TmlFa4Fwd.Protocol.Bias
