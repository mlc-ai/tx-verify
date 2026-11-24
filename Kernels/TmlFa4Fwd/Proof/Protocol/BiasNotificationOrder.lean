-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.BiasExpectationFaults
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderBiasTensorOrdinal
import Kernels.TmlFa4Fwd.Proof.MbarSafety
import Lemmas.Order.DependencyWitness
import Lemmas.Order.GuardOrder

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Protocol.Bias
open PTX PTX.Flow PTX.AsyncCopy PTX.MBarrier Thread.Loader

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- A positive Bias half ordinal has an observed preceding empty guard. -/
theorem biasTensorGuardObserved (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {g j : Nat} {stage half : Fin 2} {spec : TensorCopy.Spec}
    (hIssue : BiasSubbox p l X (g,j) stage half spec)
    (hReused : 0 < biasTensorOrdinal l X stage half (g,j)) :
    let ordinal := biasTensorOrdinal l X stage half (g,j)
    let log := X.objects (biasEmptyObject l (g / l.block) stage)
    ∃ (k i phase : Nat) (r : Record Ref), log[i]? = some r ∧ r.id = .thread (g,k) ∧
      r.reply.waited = some true ∧ Resumes kernel X (g,k) (g,j) ∧
      observedAt log i = some phase ∧ ordinal ≤ phase + 1 := by
  let ordinal := biasTensorOrdinal l X stage half (g,j)
  let obj := biasEmptyObject l (g / l.block) stage
  let log := X.objects obj
  obtain ⟨k, e, _, hGet, hKind, hOrdinal, hResume⟩ := biasTensorOrdinalGuard hp hX hIssue
  have hClean : ∀ r ∈ log, (∃ q ok, r.action = .pollParity q ok) → r.fault = none :=
    fun _ hr _ => biasEmptyHistoryClean hp hX stage hr
  have hNo := objects_noInval hX.tma.2.2.1 (fun i _ => noMbarInval hX (i := i)) obj
  have hAlt := biasTensorEmptyAlternates hp hX hIssue hClean
  obtain ⟨source, kind⟩ := e
  change kind = _ at hKind
  subst kind
  have hOrdinal' := MbarRing.Poll.nth_eq hGet
  rw [hOrdinal] at hOrdinal'
  have hBound : ordinal < okPolls obj (X.tr g) := by
    apply MbarRing.Poll.nth_present.mp
    rw [hOrdinal']
    exact ⟨_, hGet⟩
  obtain ⟨i, r, _, hIndex, hI, _, hSuccess, _, hCount⟩ :=
    MbarRing.Poll.record hX hClean hBound
  have hId : r.id = .thread (g,k) := by rw [hI, hOrdinal']
  have hSel : objectThreadSelected g r.id = true := objectThreadSelected_iff.mpr ⟨k, hId⟩
  have hChecked := X.objects_checked hX obj
  obtain ⟨st, hSt, hLower, _⟩ := hChecked.selected_poll_phase_ge hNo
    (objectThreadSelected g) (by decide : 1 ≤ 1) hAlt hIndex hSel hSuccess
  have hPos : 0 < st.phase := by omega
  obtain ⟨s, q, hs, _, _, hComplete⟩ := hChecked.okPoll hIndex hSuccess
  rw [hSt] at hs
  obtain rfl := Option.some.inj hs
  have hObs : observedAt log i = some (st.phase - 1) := by
    change ((X.objects obj)[i]?.bind (·.reply.completed)) = _
    rw [hIndex, Option.bind_some, hComplete, ite_eq_left hPos]
  exact ⟨k, i, st.phase - 1, r, hIndex, hId, hSuccess, hResume, hObs, by omega⟩

/-- Every recorded Bias notification is reached from its real issue through a written byte. -/
theorem biasNotificationAfterIssue (hX : Consistent l kernel Assumptions.all m X) {e : EvId}
    {stage half : Fin 2} {spec : TensorCopy.Spec} (hIssue : BiasSubbox p l X e stage half spec)
    (hPresent : X.AsyncPresent e (.notify .load)) :
    Relation.TransGen (DepStep l kernel X) (.thread e, false)
      (.async e (.notify .load), false) := by
  obtain ⟨o, ho, hn⟩ := hPresent
  obtain ⟨x, y, k, hw⟩ := tensor_write_present hX.effectValidity ho hn
  have hNotify : X.AsyncPresent e (.notify .load) := ⟨o, ho, hn⟩
  obtain ⟨_, hGet⟩ := hIssue.1
  have hStage : StageEdge X (.async e (.write (.load x y k))) (.async e (.notify .load)) :=
    ⟨rfl, rfl, hw, hNotify⟩
  exact ((Relation.TransGen.single
    (DepStep.issue ⟨_, hGet⟩ hw (fun _ h => by cases h) (fun h => by cases h)
      (fun h => by cases h) (fun h => by cases h))).tail (DepStep.node hw)).tail
    (DepStep.stage (.inr ⟨rfl, rfl, hStage⟩))

/-- A real Bias notification cannot precede the ready phase of its own half's reuse ordinal. -/
theorem biasNotificationPhaseLower (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {cta i : Nat} (stage : Fin 2) {r : Record Ref} {current : State} {e : EvId} {half : Fin 2}
    {spec : TensorCopy.Spec} (hr : (X.objects (biasReadyObject l cta stage))[i]? = some r)
    (hId : r.id = .async e (.notify .load)) (hOwner : e.1 / l.block = cta)
    (hBox : BiasSubbox p l X e stage half spec) (ha : r.action = .completeTx 16384)
    (hCurrent : stateBefore (X.objects (biasReadyObject l cta stage)) i = some current) :
    biasTensorOrdinal l X stage half e ≤ current.phase := by
  rcases Nat.eq_zero_or_pos (biasTensorOrdinal l X stage half e) with hZero | hPos
  · simp [hZero]
  let loc := biasReadyObject l cta stage
  let log := X.objects loc
  have hNo := objects_noInval hX.tma.2.2.1 (fun i _ => noMbarInval hX (i := i)) loc
  have hChecked := X.objects_checked hX loc
  have hPresent := object_record_present hX.tma (List.mem_of_getElem? hr)
  rw [hId] at hPresent
  obtain ⟨g,k⟩ := e
  obtain ⟨w, j, phase, poll, hPoll, hPollId, hReply, hResume, hObs, hLower⟩ :=
    biasTensorGuardObserved hp hX hBox hPos
  change g / l.block = cta at hOwner
  rw [hOwner] at hPoll hObs
  obtain ⟨release, hReturn, hRetOrdinal, hWaits⟩ :=
    biasEmptyObservedReturn hp hX stage hPoll hReply hObs
  obtain ⟨sensor, atReady, q, ready, hReady, hReadyId, hSeen, hReadyObs, hPhaseGe, hRelease⟩ :=
    Thread.Softmax.biasReadyObservedOfReturn hp hX stage hReturn
  obtain ⟨st, hState, hS⟩ := hChecked.observed_phase hReady hSeen hReadyObs
  rw [hPollId] at hWaits
  have hPath := (Relation.TransGen.single (DepStep.of_resumes l hRelease)).tail
    (DepStep.of_witness l (Witness.of_mbarObserved hWaits))
  have hChain := (hPath.tail (DepStep.of_resumes l hResume)).trans
    (biasNotificationAfterIssue hX hBox hPresent)
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
  rw [hCurrent] at ht
  obtain rfl := Option.some.inj ht
  change biasTensorOrdinal l X stage half (g,k) ≤ phase + 1 at hLower
  change biasArrivalOrdinal X (biasEmptyObject l cta stage) release ≤ q at hPhaseGe
  omega

end PTX.Kernels.TmlFa4Fwd.Protocol.Bias
