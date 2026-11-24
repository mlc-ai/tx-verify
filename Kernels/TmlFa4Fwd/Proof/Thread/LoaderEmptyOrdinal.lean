-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.LoaderReusePriming
public import Kernels.TmlFa4Fwd.Proof.Thread.LoaderReuse
public import Lemmas.Protocol.PollIndex

@[expose] public section

namespace PTX.Kernels.TmlFa4Fwd.Thread.Loader
open PTX PTX.AsyncCopy PTX.MBarrier PTX.MbarRing
open PTX.Kernels.TmlFa4Fwd.Thread.Mma.Observation (emptyObject)

noncomputable section

/-- The number of earlier successful acquires of this loader lane's empty slot. -/
def emptyOrdinal (l : Launch) (X : Execution) (wait : EvId) (slot : Fin 3) : Nat :=
  Flow.okPolls (emptyObject l wait.1 slot) ((X.tr wait.1).take wait.2)

variable {p : Params} {l : Launch} {m : Mem0} {X : Execution}

/-- The actual successful empty poll has a clean and successful object record. -/
theorem EmptyAcquire.record (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {wait : EvId} {slot : Fin 3} {parity : Nat} (h : EmptyAcquire l X wait slot parity) :
    ∃ (j : Nat) (r : Record Ref), (X.objects (emptyObject l wait.1 slot))[j]? = some r ∧
      r.id = .thread wait ∧ r.action = .pollParity parity true ∧
      r.fault = none ∧ r.reply.waited = some true := by
  obtain ⟨⟨pc, kind⟩, he, hk⟩ := h
  dsimp only at hk
  subst kind
  exact actualPollRecordClean hp hX he

private theorem emptyPollRecordsClean (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) (loc : Loc) :
    ∀ r ∈ X.objects loc, (∃ p ok, r.action = .pollParity p ok) → r.fault = none := by
  intro r hMem hPoll
  obtain ⟨q, ok, hAction⟩ := hPoll
  cases record_source hX.tma.2.2.1 hMem with
  | wait hId he hr =>
    obtain ⟨i, found, hAt, hFound, _, hf, _⟩ :=
      actualPollRecordClean hp hX he
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hMem
    have hEq := ObjectInit.checked_record_index_eq (X.objects_checked hX loc) hAt hj
      (hFound.trans hId.symm)
    rw [hEq, hj] at hAt
    exact (Option.some.inj hAt) ▸ hf
  | _ => grind

/-- Object-log counting and the loader's thread cursor give the same empty-poll ordinal. -/
theorem EmptyAcquire.recordOrdinal (hp : Pre p l m) (hX : Consistent l kernel Assumptions.all m X)
    {wait : EvId} {slot : Fin 3} {parity : Nat} (h : EmptyAcquire l X wait slot parity) :
    let loc := emptyObject l wait.1 slot
    ∃ (j : Nat) (r : Record Ref), (X.objects loc)[j]? = some r ∧
      r.id = .thread wait ∧ r.fault = none ∧ r.reply.waited = some true ∧
      selectedBefore (objectThreadSelected wait.1) (X.objects loc) j =
        emptyOrdinal l X wait slot := by
  obtain ⟨j, r, hj, hr, _, hf, hs⟩ := h.record hp hX
  exact ⟨j, r, hj, hr, hf, hs, Poll.count_before hX hj hr (emptyPollRecordsClean hp hX _)⟩

/-- Only successful polls at or before the named event are needed for its observation. -/
def AlternatesEmptyThrough (l : Launch) (X : Execution) (g stop : Nat) (slot : Fin 3)
    (offset : Nat) : Prop :=
  ∀ (j : Nat) (e : Event) (q : Nat) (acq : Bool) (scope : MbarScope), j ≤ stop →
    X.get (g, j) = some e →
    e.kind = .wait (emptyObject l g slot) q true acq scope →
    q % 2 = (emptyOrdinal l X (g, j) slot + offset) % 2

private theorem emptyNoInval {l : Launch} {m : Mem0} {X : Execution}
    (hX : Consistent l kernel Assumptions.all m X) (loc : Loc) : NoInval (X.objects loc) := by
  apply objects_noInval hX.tma.2.2.1
  intro i loc h
  exact noMbarInval hX h

/-- Alternation through this wait gives a lower bound on the completed generation it observes
after the initially free use. Later polls play no role in the bound. -/
theorem EmptyAcquire.observedAtLeastOfPrefix (hp : Pre p l m)
    (hX : Consistent l kernel Assumptions.all m X) {wait : EvId} {slot : Fin 3}
    {parity offset : Nat} (h : EmptyAcquire l X wait slot parity) (hOffset : offset ≤ 1)
    (hAlternates : AlternatesEmptyThrough l X wait.1 wait.2 slot offset)
    (hIssued : offset ≤ emptyOrdinal l X wait slot) :
    let log := X.objects (emptyObject l wait.1 slot)
    ∃ (j phase : Nat) (r : Record Ref), log[j]? = some r ∧ r.id = .thread wait ∧
      r.fault = none ∧ r.reply.waited = some true ∧ observedAt log j = some phase ∧
      emptyOrdinal l X wait slot ≤ phase + offset := by
  dsimp only
  let loc := emptyObject l wait.1 slot
  let log := X.objects loc
  obtain ⟨j, r, hj, hr, hf, hSuccess, hCount⟩ := h.recordOrdinal hp hX
  let logPrefix := log.take (j + 1)
  have hLog := X.objects_checked hX loc
  have hJP : j + 1 ≤ log.length := (List.getElem?_eq_some_iff.mp hj).1
  have hPrefix : CheckedLog logPrefix :=
    ⟨hLog.1.sublist ((List.take_sublist _ _).map _), ⟨_, hLog.prefix hJP⟩⟩
  have hClean := emptyPollRecordsClean hp hX loc
  have hCounts (i : Nat) (hi : i ≤ j + 1) :
      selectedBefore (objectThreadSelected wait.1) logPrefix i =
        selectedBefore (objectThreadSelected wait.1) log i := by
    simp [selectedBefore, logPrefix, List.take_take, Nat.min_eq_left hi]
  have hAlternating : SelectedAlternates (objectThreadSelected wait.1) logPrefix offset := by
    intro i w p ok hi hAction hSelected hReply
    have hiLe : i ≤ j := by
      have hIndex := (List.getElem?_eq_some_iff.mp hi).1
      simp [logPrefix, List.length_take, Nat.min_eq_left hJP] at hIndex
      omega
    have hiLog : log[i]? = some w := by
      simpa only [logPrefix, List.getElem?_take_of_lt (show i < j + 1 by omega)] using hi
    obtain ⟨k, hThread⟩ := objectThreadSelected_iff.mp hSelected
    have hK : k ≤ wait.2 := by
      by_cases hEq : i = j
      · subst i
        have hId := Option.some.inj (hiLog.symm.trans hj)
        have hWait := Ref.thread.inj (hThread.symm.trans (hId ▸ hr))
        exact (congrArg Prod.snd hWait).le
      · have hMem : w ∈ log.take j := by
          have hGet : (log.take j)[i]? = some w := by
            rw [List.getElem?_take_of_lt (show i < j by omega), hiLog]
          exact List.mem_of_getElem? hGet
        exact (hX.object_thread_take_mem_iff hj hr (List.mem_of_getElem? hiLog) hThread).mp
          hMem |>.le
    have hMem := List.mem_of_getElem? hiLog
    have hFault := hClean w hMem ⟨p, ok, hAction⟩
    have hReplySrc := (hX.object_thread_waited_iff hMem hThread hFault).mp hReply
    cases record_source hX.tma.2.2.1 hMem with
    | @wait actor pos site q matched acquire scope hId hEvent hAct =>
      obtain rfl := Action.pollParity.inj (hAction.symm.trans hAct) |>.1
      have hiEq := Ref.thread.inj (hId.symm.trans hThread)
      rw [hiEq] at hEvent
      rw [hEvent] at hReplySrc
      have hOk : matched = true := by cases matched <;> simp [sourceWaitSuccess] at hReplySrc ⊢
      rw [hOk] at hEvent
      rw [hCounts i (by omega), Poll.count_before hX hiLog hThread hClean]
      exact hAlternates k _ _ _ _ hK hEvent rfl
    | _ => grind
  have hSelect : objectThreadSelected wait.1 r.id = true :=
    objectThreadSelected_iff.mpr ⟨wait.2, hr⟩
  have hPrefixNoInval : NoInval logPrefix :=
    fun r hr => emptyNoInval hX loc r (List.mem_of_mem_take hr)
  have hJPrefix : logPrefix[j]? = some r := by
    rw [List.getElem?_take_of_lt (Nat.lt_succ_self j), hj]
  obtain ⟨st, hSt, hLower, _⟩ := hPrefix.selected_poll_phase_ge hPrefixNoInval
    (objectThreadSelected wait.1) hOffset hAlternating hJPrefix hSelect hSuccess
  rw [hCounts j (by omega), hCount] at hLower
  have hState : stateBefore logPrefix j = stateBefore log j := by
    simp only [stateBefore, logPrefix, List.getElem?_take_of_lt (show j - 1 < j + 1 by omega)]
  rw [hState] at hSt
  obtain ⟨u, q, hu, _, _, hCompleted⟩ := hLog.okPoll hj hSuccess
  rw [hSt] at hu
  obtain rfl := Option.some.inj hu
  have hPositive : 0 < st.phase := by omega
  have hObserved : observedAt log j = some (st.phase - 1) := by
    change ((X.objects (emptyObject l wait.1 slot))[j]?.bind (·.reply.completed)) = _
    rw [hj, Option.bind_some, hCompleted, ite_eq_left hPositive]
  exact ⟨j, st.phase - 1, r, hj, hr, hf, hSuccess, hObserved, by omega⟩

end
end PTX.Kernels.TmlFa4Fwd.Thread.Loader
