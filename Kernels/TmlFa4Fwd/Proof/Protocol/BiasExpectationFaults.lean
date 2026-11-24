-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.BiasEmptyGeneration
import Kernels.TmlFa4Fwd.Proof.MbarSafety
import Lemmas.Protocol.PairTmaRing.Faults

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Bias
open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier Thread.Loader

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution} (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X)
include hp hX

private theorem biasReadyInit {cta : Nat} (stage : Fin 2) {r : Record Ref}
    (hr : r ∈ X.objects (biasReadyObject l cta stage)) :
    PairTmaRing.InitFirst X (biasReadyObject l cta stage) 1 := by
  fin_cases stage
  · exact (activeObjectHistory hp hX (30 : Fin 34) hr).1
  · exact (activeObjectHistory hp hX (31 : Fin 34) hr).1

/-- Each actual Bias expectation only issues in its own generation, after the preceding
ready completion was observed. This holds even for an expectation that would fault. -/
theorem biasExpectationStateWithGuard {cta i : Nat} (stage : Fin 2) {r : Record Ref}
    (hr : (X.objects (biasReadyObject l cta stage))[i]? = some r) {e : EvId}
    (hId : r.id = .thread e) (hIssue : X.Arrive e (biasReadyObject l cta stage) 32768 1 true .cta)
    (ha : r.action = .arrive 1 32768) :
    ∃ s, stateBefore (X.objects (biasReadyObject l cta stage)) i = some s ∧
      s.phase = biasArrivalOrdinal X (biasReadyObject l cta stage) e ∧ s.observed = true ∧
      (0 < s.phase →
        ∃ release k, X.Arrive release (biasEmptyObject l cta stage) 0 1 true .cta ∧
          biasArrivalOrdinal X (biasEmptyObject l cta stage) release + 1 = s.phase ∧
          MbarObserved X (.thread release) (.thread (e.1,k)) ∧
          Resumes kernel X (e.1,k) e) := by
  let loc := biasReadyObject l cta stage
  let log := X.objects loc
  let ordinal := biasArrivalOrdinal X loc e
  let empty := biasEmptyObject l cta stage
  have hInit := biasReadyInit hp hX stage (List.mem_of_getElem? hr)
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have hChecked := X.objects_checked hX loc
  obtain ⟨_, s, hs, _⟩ := PairTmaRing.state_of_init hX hInit hNo hr
    (by intro n; rw [ha]; simp)
  have hPhase : phaseAt log i = some s.phase := by
    change stateBefore log i = some s at hs
    simp [phaseAt, hs]
  have hUpper : s.phase ≤ ordinal := by
    obtain ⟨g,k⟩ := e
    exact biasExpectationPhaseLeOrdinal hp hX stage hr hId hIssue hPhase
  refine ⟨s, hs, ?_⟩
  change s.phase = ordinal ∧ s.observed = true ∧ _
  rcases Nat.eq_zero_or_pos ordinal with hZero | hPos
  · have hPhaseZero : s.phase = 0 := by omega
    exact ⟨by omega, hChecked.observed_of_poll hNo hs (.inl hPhaseZero), by omega⟩
  obtain ⟨g,k⟩ := e
  have hReused : 0 < arrivals loc ((X.tr g).take k) := hPos
  obtain ⟨w, j, phase, poll, hPoll, hPollId, _, hReply, hResume, hObs, hLower⟩ :=
    biasReuseGuardObserved hp hX stage hIssue hReused
  obtain ⟨release, hReturn, hRetOrdinal, hWaits⟩ :=
    biasEmptyObservedReturn hp hX stage hPoll hReply hObs
  obtain ⟨sensor, atReady, q, ready, hReady, hReadyId, hSeen, hReadyObs, hPhaseGe, hRelease⟩ :=
    Thread.Softmax.biasReadyObservedOfReturn hp hX stage hReturn
  obtain ⟨st, hState, hS⟩ := hChecked.observed_phase hReady hSeen hReadyObs
  rw [hPollId] at hWaits
  have hPath := (Relation.TransGen.single (DepStep.of_resumes l hRelease)).tail
    (DepStep.of_witness l (Witness.of_mbarObserved hWaits))
  have hChain := hPath.tail (DepStep.of_resumes l hResume)
  rw [← hReadyId, ← hId] at hChain
  have hNot := MbarRing.Round.Slot.not_before_of_reach (m := loc) hX hChain
  have hPrior : atReady < i := by
    rcases Nat.lt_trichotomy atReady i with h | rfl | h
    · exact h
    · obtain rfl := Option.some.inj (hReady.symm.trans hr)
      obtain ⟨_, _, _, hAction, _, _⟩ := hChecked.okPoll hr hSeen
      rw [ha] at hAction
      cases hAction
    · exact (hNot ⟨i, atReady, r, ready, hr, rfl, hReady, rfl, h⟩).elim
  obtain ⟨t, ht, hMono⟩ := hChecked.phase_mono hNo hPrior.le
    (List.getElem?_eq_some_iff.mp hr).1.le hState
  rw [hs] at ht
  obtain rfl := Option.some.inj ht
  change ordinal ≤ phase + 1 at hLower
  change arrivals empty ((X.tr release.1).take release.2) = phase at hRetOrdinal
  change arrivals empty ((X.tr release.1).take release.2) ≤ q at hPhaseGe
  have hEq : st.phase = s.phase := by omega
  refine ⟨by omega, hChecked.observed_of_poll hNo hs
    (.inr ⟨atReady, ready, st, hPrior, hReady, hSeen, hState, hEq⟩), ?_⟩
  intro _
  refine ⟨release,w,hReturn,?_,hWaits,hResume⟩
  change arrivals empty ((X.tr release.1).take release.2) + 1 = s.phase
  omega

/-- Each actual Bias expectation issues in its own observed ready generation. -/
theorem biasExpectationState {cta i : Nat} (stage : Fin 2) {r : Record Ref}
    (hr : (X.objects (biasReadyObject l cta stage))[i]? = some r) {e : EvId}
    (hId : r.id = .thread e) (hIssue : X.Arrive e (biasReadyObject l cta stage) 32768 1 true .cta)
    (ha : r.action = .arrive 1 32768) :
    ∃ s, stateBefore (X.objects (biasReadyObject l cta stage)) i = some s ∧
      s.phase = biasArrivalOrdinal X (biasReadyObject l cta stage) e ∧ s.observed = true := by
  obtain ⟨s,hs,hPhase,hObserved,_⟩ := biasExpectationStateWithGuard hp hX stage hr hId hIssue ha
  exact ⟨s,hs,hPhase,hObserved⟩

/-- Every actual Bias expectation is safe, including when one or both box completions arrived
before its expectation was recorded. -/
theorem biasExpectationClean {cta i : Nat} (stage : Fin 2) {r : Record Ref}
    (hi : (X.objects (biasReadyObject l cta stage))[i]? = some r) (ha : r.action = .arrive 1 32768)
    : r.fault = none := by
  classical
  let loc := biasReadyObject l cta stage
  let log := X.objects loc
  have hNo := objects_noInval hX.tma.2.2.1 (fun _ _ => noMbarInval hX) loc
  have hChecked := X.objects_checked hX loc
  have hLen := (List.getElem?_eq_some_iff.mp hi).1
  have hExpect {r : Record Ref} (hr : r ∈ log) (hA : ∃ units tx, r.action = .arrive units tx) :
      ∃ e, r.id = .thread e ∧ X.Arrive e loc 32768 1 true .cta ∧
        r.action = .arrive 1 32768 := by
    obtain ⟨_, _, hA⟩ := hA
    cases biasReadyRecord hp hX stage hr with
    | init h => obtain ⟨_, h⟩ := h; rw [h] at hA; cases hA
    | poll h => obtain ⟨_, _, h⟩ := h; rw [h] at hA; cases hA
    | expect e hid he ha => exact ⟨e, hid, he, ha⟩
    | notify _ _ _ _ _ _ h => rw [h] at hA; cases hA
  obtain ⟨⟨g,j⟩, hId, he, _⟩ := hExpect (List.mem_of_getElem? hi) ⟨_, _, ha⟩
  obtain ⟨s, hs, hPhase, hObs⟩ := biasExpectationState hp hX stage hi hId he ha
  have hNoEarlier {k : Nat} (hk : k < i) {f : Record Ref} (hf : log[k]? = some f)
      (hSamePhase : phaseAt log k = some s.phase) {u tx : Nat} (hA : f.action = .arrive u tx) :
      False := by
    obtain ⟨⟨g',j'⟩, hI, hE, hAction⟩ := hExpect (List.mem_of_getElem? hf) ⟨u,tx,hA⟩
    have hLane := PTX.Kernels.TmlFa4Fwd.Loader.biasExpectationSameIssuer hp hX he hE
    change g = g' at hLane
    subst g'
    obtain ⟨t, ht, hT, _⟩ := biasExpectationState hp hX stage hf hI hE hAction
    have hT' : t.phase = s.phase := by
      change stateBefore log k = some t at ht
      simpa only [phaseAt, ht, Option.map_some, Option.some.injEq] using hSamePhase
    have hSame : arrivals loc ((X.tr g).take j) = arrivals loc ((X.tr g).take j') :=
      hPhase.symm.trans (hT'.symm.trans hT)
    have hIndex := Thread.Softmax.arrivalOrdinalInjective he hE hSame
    subst j'
    have h := ObjectInit.checked_record_index_eq hChecked hf hi (hI.trans hId.symm)
    omega
  have hNoUnits : phaseUnits log i s.phase = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hLt := Finset.mem_range.mp hk
    have hK : k < log.length := hLt.trans hLen
    obtain ⟨r, hr⟩ : ∃ a, log[k]? = some a := ⟨_, List.getElem?_eq_getElem hK⟩
    by_cases hPh : phaseAt log k = some s.phase
    · rw [ite_eq_left hPh]
      have hAction : r.action.units = 0 := by
        cases h : r.action <;> simp [Action.units]
        exact (hNoEarlier hLt hr hPh h).elim
      simp [unitsAt, hr, hAction]
    · simp [hPh]
  have hTxNonpos : s.tx ≤ 0 := by
    rw [hChecked.tx_eq hNo hLen.le hs]
    change phaseTx log i s.phase ≤ 0
    apply Finset.sum_nonpos
    intro k hk
    have hLt := Finset.mem_range.mp hk
    have hK : k < log.length := hLt.trans hLen
    obtain ⟨r, hr⟩ : ∃ a, log[k]? = some a := ⟨_, List.getElem?_eq_getElem hK⟩
    by_cases hPh : phaseAt log k = some s.phase
    · rw [ite_eq_left hPh]
      unfold txDeltaAt
      rw [hr]
      have hDelta : r.action.txDelta ≤ 0 := by
        cases h : r.action <;> simp [Action.txDelta]
        exact (hNoEarlier hLt hr hPh h).elim
      change r.txDelta ≤ 0
      unfold Record.txDelta
      split
      · exact hDelta
      · decide
    · rw [ite_eq_right hPh]
  have hExp := PairTmaRing.expected_of_init hX (biasReadyInit hp hX stage (List.mem_of_getElem? hi))
    hNo hs
  have hPending := hChecked.pending_eq hNo hLen.le hs
  rw [hNoUnits, hExp, Nat.add_zero] at hPending
  have hUnit : 1 ≤ s.pending := by omega
  have hTx := hChecked.txValid hLen.le hs
  have hValid : validTx (s.tx + 32768) := by
    obtain ⟨hLo, _⟩ := hTx
    unfold validTx limit at *
    omega
  have hCount : validCount 1 ∧ validTxOperand 32768 := by decide
  have hRun : ∃ reply, perform (some s) (.arrive 1 32768) = .ok reply := by
    simp only [perform, hObs, hUnit, ↓reduceIte, bind, Except.bind, pure, Except.pure]
    rw [ite_eq_left hCount, Int.cast_ofNat_Int, ite_eq_left hValid]
    exact ⟨_, rfl⟩
  obtain ⟨reply, hr⟩ := hRun
  have hOk := hChecked.at hi
  unfold RecordOk at hOk
  rw [hs, ha, hr] at hOk
  exact hOk.2

end PTX.Kernels.TmlFa4Fwd.Protocol.Bias
