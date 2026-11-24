-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderBiasCredits
public import Lemmas.Protocol.PairTxCredits
import Kernels.TmlFa4Fwd.Proof.MbarSafety
import Lemmas.Protocol.PairTmaRing.Faults

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Bias
open PTX PTX.AsyncCopy PTX.MBarrier Thread.Loader

noncomputable section

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem biasInitialized {cta : Nat} (stage : Fin 2) {r : Record Ref}
    (hr : r ∈ X.objects (biasReadyObject l cta stage)) :
    PairTmaRing.InitFirst X (biasReadyObject l cta stage) 1 := by
  fin_cases stage
  · exact (activeObjectHistory hp hX (30 : Fin 34) hr).1
  · exact (activeObjectHistory hp hX (31 : Fin 34) hr).1

private theorem biasPairTxActions {cta : Nat} (stage : Fin 2) {r : Record Ref}
    (hr : r ∈ X.objects (biasReadyObject l cta stage)) : PairTxAction r := by
  cases biasReadyRecord hp hX stage hr with
  | init ha => exact .init ha
  | poll ha => exact .poll ha
  | expect _ _ _ ha => exact .expect ha
  | notify _ _ _ _ _ _ ha => exact .notify ha

/-- Every successfully observed Bias-ready generation has one actual expectation
and two actual transaction notifications, all without faults. -/
theorem biasReadyObservedCredits {cta j phase : Nat} (stage : Fin 2) {poll : Record Ref}
    (hj : (X.objects (biasReadyObject l cta stage))[j]? = some poll)
    (hSuccess : poll.reply.waited = some true)
    (hPhase : observedAt (X.objects (biasReadyObject l cta stage)) j = some phase) :
    let log := X.objects (biasReadyObject l cta stage)
    ∃ stop ≤ j, (pairTxPhaseRecords log stop phase (.arrive 1 32768)).card = 1 ∧
      (pairTxPhaseRecords log stop phase (.completeTx 16384)).card = 2 ∧
      ∀ i r, log[i]? = some r → phaseAt log i = some phase → i < stop := by
  let loc := biasReadyObject l cta stage
  have hChecked := X.objects_checked hX loc
  have hNo := objects_noInval hX.tma.2.2.1 (fun i _ => noMbarInval hX (i := i)) loc
  have hInit := biasInitialized hp hX stage (List.mem_of_getElem? hj)
  exact completedPairTxCounts hChecked hNo (fun _ hr => biasPairTxActions hp hX stage hr)
    (fun _ _ hs => PairTmaRing.expected_of_init hX hInit hNo hs) hj hSuccess hPhase

/-- A completed Bias-ready phase records an actual expectation in that phase. -/
theorem biasReadyExpectationOfCompletedPhase {cta : Nat} (stage : Fin 2) {s : State} {phase : Nat}
    (hs : stateBefore (X.objects (biasReadyObject l cta stage))
      (X.objects (biasReadyObject l cta stage)).length = some s) (hOlder : phase < s.phase) :
    let log := X.objects (biasReadyObject l cta stage)
    ∃ k r issue, log[k]? = some r ∧ r.id = .thread issue ∧
      X.Arrive issue (biasReadyObject l cta stage) 32768 1 true .cta ∧
      phaseAt log k = some phase := by
  classical
  let loc := biasReadyObject l cta stage
  let log := X.objects loc
  have hLength : 0 < log.length := by
    cases hLength : log.length with
    | zero =>
      change stateBefore log log.length = some s at hs
      rw [List.length_eq_zero_iff.mp hLength] at hs
      simp [stateBefore] at hs
    | succ n => omega
  have hInit := biasInitialized hp hX stage (List.getElem_mem (l := log) (n := 0) hLength)
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  obtain ⟨stop, _, hCount, _, _⟩ := completedPairTxCountsBeforeState (X.objects_checked hX loc)
    hNo (fun _ hr => biasPairTxActions hp hX stage hr)
    (fun _ _ ht => PairTmaRing.expected_of_init hX hInit hNo ht) (Nat.le_refl _) hs hOlder
  have hPos : 0 < (pairTxPhaseRecords log stop phase (.arrive 1 32768)).card := by
    rw [hCount]
    decide
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hPos
  obtain ⟨_, hPhase, r, hr, _, hAct⟩ := memPairTxPhaseRecords.mp hk
  cases biasReadyRecord hp hX stage (List.mem_of_getElem? hr) with
  | init ha => obtain ⟨_, ha⟩ := ha; rw [ha] at hAct; cases hAct
  | poll ha => obtain ⟨_, _, ha⟩ := ha; rw [ha] at hAct; cases hAct
  | expect e hId hIssue _ => exact ⟨k,r,e,hr,hId,hIssue,hPhase⟩
  | notify _ _ _ _ _ _ ha => rw [ha] at hAct; cases hAct

omit hp hX in
/-- One actual tensor completion contributes its 16 KiB credit to the observed stage. -/
def BiasReadyBox (p : Params) (l : Launch) (X : Execution) (cta : Nat)
    (stage : Fin 2) (phase : Nat) (tensor : EvId) : Prop :=
  (∃ half spec, BiasSubbox p l X tensor stage half spec) ∧
  ∃ i r, (X.objects (biasReadyObject l cta stage))[i]? = some r ∧
    r.id = .async tensor (.notify .load) ∧ r.fault = none ∧
    phaseAt (X.objects (biasReadyObject l cta stage)) i = some phase

/-- The Bias-ready phase observed by an actual acquire retires two distinct Bias tensors. -/
theorem biasReadyObservedBoxes {cta j phase : Nat} (stage : Fin 2) {poll : Record Ref}
    (hj : (X.objects (biasReadyObject l cta stage))[j]? = some poll)
    (hSuccess : poll.reply.waited = some true)
    (hPhase : observedAt (X.objects (biasReadyObject l cta stage)) j = some phase) :
    ∃ a b, a ≠ b ∧ BiasReadyBox p l X cta stage phase a ∧
      BiasReadyBox p l X cta stage phase b := by
  classical
  let loc := biasReadyObject l cta stage
  let log := X.objects loc
  obtain ⟨stop, _, _, hCount, _⟩ := biasReadyObservedCredits hp hX stage hj hSuccess hPhase
  have box {i : Nat} (hi : i ∈ pairTxPhaseRecords log stop phase (.completeTx 16384)) :
      ∃ tid r, log[i]? = some r ∧ r.id = .async tid (.notify .load) ∧
        BiasReadyBox p l X cta stage phase tid := by
    obtain ⟨_, hAt, r, hr, hClean, hAct⟩ := memPairTxPhaseRecords.mp hi
    cases biasReadyRecord hp hX stage (List.mem_of_getElem? hr) with
    | notify tid half spec hId _ hBox _ =>
      exact ⟨tid, r, hr, hId, ⟨half, spec, hBox⟩, i, r, hr, hId, hClean, hAt⟩
    | init ha => obtain ⟨_, ha⟩ := ha; rw [ha] at hAct; cases hAct
    | poll ha => obtain ⟨_, _, ha⟩ := ha; rw [ha] at hAct; cases hAct
    | expect _ _ _ ha => rw [ha] at hAct; cases hAct
  obtain ⟨u, v, hNe, hPair⟩ := Finset.card_eq_two.mp hCount
  obtain ⟨a, ar, ha, hAId, hABox⟩ := box (hPair ▸ Finset.mem_insert_self _ _)
  obtain ⟨b, br, hb, hBId, hBBox⟩ := box
    (hPair ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  refine ⟨a, b, ?_, hABox, hBBox⟩
  intro h
  subst b
  exact hNe (ObjectInit.checked_record_index_eq (X.objects_checked hX loc) ha hb
    (hAId.trans hBId.symm))

end
end PTX.Kernels.TmlFa4Fwd.Protocol.Bias
