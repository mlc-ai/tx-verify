-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.MbarUnitTx
public import Lemmas.Protocol.PollPhase
import Lemmas.Protocol.MbarInit
public import Core.Assembly.WaitOrder

@[expose] public section

namespace PTX.MBarrier

private theorem CheckedLog.zeroTxBefore {ι : Type} {log : List (Record ι)}
    (hChecked : CheckedLog log) (hNo : NoInval log)
    (hShape : ∀ {q}, q ∈ log → CounterUpdate q.action → q.action = .arrive 1 0)
    {i : Nat} {r : Record ι} {st : State}
    (hi : log[i]? = some r) (hState : stateBefore log i = some st) : st.tx = 0 := by
  have hLen := (List.getElem?_eq_some_iff.mp hi).1.le
  have hTxA : expectedTxBytes (log.take i) = 0 := by
    simpa using (expectedTxBytes_unit (xs := log.take i) (T := 0) (by
      intro q hq _ count tx h
      have hAct := hShape (List.mem_of_mem_take hq) (by rw [h]; trivial)
      exact (Action.arrive.inj (h.symm.trans hAct))))
  have hTxC : completedTxBytes (log.take i) = 0 := by
    simpa using (completedTxBytes_eq_unit_mul_count (log := log.take i) (unit := 0) (by
      intro q hq _ bytes h
      have hAct := hShape (List.mem_of_mem_take hq) (by rw [h]; trivial)
      rw [h] at hAct
      cases hAct))
  have hTx := hChecked.tx_balance hNo hLen hState
  rw [hTxA, hTxC] at hTx
  exact hTx

/-- In an initialized zero-transaction history of unit updates, an arrival can fault only
if the previous phase has yet to be observed. -/
theorem CheckedLog.zeroTxUpdateFaultCases {ι : Type} {log : List (Record ι)}
    (hChecked : CheckedLog log) (hNo : NoInval log)
    (hShape : ∀ {q}, q ∈ log → CounterUpdate q.action → q.action = .arrive 1 0)
    {i : Nat} {r : Record ι} {st : State}
    (hi : log[i]? = some r) (hState : stateBefore log i = some st)
    (hUpdate : CounterUpdate r.action) :
    r.fault = none ∨ r.fault = some .precedingPhaseNotObserved := by
  have hAction := hShape (List.mem_of_getElem? hi) hUpdate
  have hTx := hChecked.zeroTxBefore hNo hShape hi hState
  have hPending := stateBefore_pending_pos hChecked hState hTx
  have hOk := hChecked.at hi
  rw [hState] at hOk
  cases hObs : st.observed
  · right
    have hPerform : perform (some st) (.arrive 1 0) = .error .precedingPhaseNotObserved := by
      simp [perform, hObs, limit, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
    rw [RecordOk, hAction, hPerform] at hOk
    exact hOk.2
  · exact .inl (hOk.arrive_fault_none hAction (by decide) (by decide) hObs (by omega)
      (by rw [hTx]; decide))

/-- An initialized object with unit zero-transaction updates accepts a credit while the
preceding history contains fewer credits than the initial expected count. -/
theorem CheckedLog.zeroTxUpdateCleanOfUnits {ι : Type} {log : List (Record ι)}
    (hChecked : CheckedLog log) (hNo : NoInval log)
    (hShape : ∀ {q}, q ∈ log → CounterUpdate q.action → q.action = .arrive 1 0)
    {i : Nat} {r : Record ι} {st : State}
    (hi : log[i]? = some r) (hState : stateBefore log i = some st)
    (hUnits : ∀ before, stateBefore log i = some before → unitsBefore log i < before.expected)
    (hUpdate : CounterUpdate r.action) : r.fault = none := by
  have hAction := hShape (List.mem_of_getElem? hi) hUpdate
  have hTx := hChecked.zeroTxBefore hNo hShape hi hState
  have hOut := hChecked.arrive_fault_free hNo hi hAction (s := 0)
    (fun before hs => by simpa using hUnits before hs)
    (by intro n hlo hhi; omega)
  have hOk := hChecked.at hi
  rw [hState] at hOk
  exact hOk.arrive_fault hAction (by decide) (by decide)
    (by rw [hTx]; decide) hOut.1 hOut.2

/-- A published one-shot object with one possible unit notification and no transaction updates
accepts its first notification, irrespective of the parity or number of its polls. -/
theorem CheckedLog.singleZeroTxUpdateClean {ι : Type} {log : List (Record ι)}
    (hChecked : CheckedLog log) (hNo : NoInval log)
    (hShape : ∀ {q}, q ∈ log → CounterUpdate q.action → q.action = .arrive 1 0)
    (hUnique : ∀ {q r}, q ∈ log → r ∈ log →
      CounterUpdate q.action → CounterUpdate r.action → q.id = r.id)
    {i : Nat} {r : Record ι} {st : State}
    (hi : log[i]? = some r) (hState : stateBefore log i = some st)
    (hExpected : ∀ j before, stateBefore log j = some before → before.expected = 1)
    (hUpdate : CounterUpdate r.action) : r.fault = none := by
  classical
  have hUnits : unitsBefore log i = 0 := by
    let selected (q : Record ι) := decide (q.action = .arrive 1 0)
    apply Nat.eq_zero_of_le_zero
    apply (arrivalUnits_le_countP selected ?_).trans
    · have hBound := countP_take_le_card hChecked.1 selected (∅ : Finset ι) (i := i) (by
        intro j hj q hq hSelect
        have hqUpdate : CounterUpdate q.action := by
          rw [show q.action = .arrive 1 0 from of_decide_eq_true hSelect]
          trivial
        have hId := hUnique (List.mem_of_getElem? hq) (List.mem_of_getElem? hi) hqUpdate hUpdate
        exact (hj.ne (ObjectInit.checked_record_index_eq hChecked hq hi hId)).elim)
      simpa using hBound
    · intro q hq _ count tx h
      have hAct := hShape (List.mem_of_mem_take hq) (by rw [h]; trivial)
      exact ⟨(Action.arrive.inj (h.symm.trans hAct)).1, decide_eq_true hAct⟩
  exact hChecked.zeroTxUpdateCleanOfUnits hNo hShape hi hState
    (fun before hs => by rw [hUnits, hExpected i before hs]; decide) hUpdate

end PTX.MBarrier
