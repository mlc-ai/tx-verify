-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.MbarUnitTx
public import Lemmas.Protocol.PollPhase
public import Lemmas.MBarrier.MBarrierRound

@[expose] public section

namespace PTX.MBarrier
noncomputable section
variable {ι : Type}

private theorem advance_tx (s : State) : (advance s).tx = s.tx := by
  unfold advance
  split <;> rfl

private theorem perform_tx_valid {s : Option State} {a : Action} {r : Reply}
    (hs : ∀ st, s = some st → validTx st.tx) (h : perform s a = .ok r)
    {t : State} (ht : r.state = some t) : validTx t.tx := by
  cases a <;> cases s <;>
    simp only [perform, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw, Option.isSome] at h
  all_goals (try split_ifs at h) <;> (try contradiction)
  all_goals
    cases h
    cases ht
  all_goals simp only [advance_tx]
  all_goals first | exact hs _ rfl | assumption | norm_num [validTx, limit]

private theorem history_tx_valid {s t : Option State} {log : List (Record ι)}
    (hh : RecordedHistory s log t) (hs : ∀ st, s = some st → validTx st.tx) :
    ∀ st, t = some st → validTx st.tx := by
  induction hh with
  | nil => exact hs
  | @cons s r rest t hr hh ih =>
    apply ih
    intro st hst
    unfold RecordOk at hr
    split at hr
    · rename_i rep hp
      exact perform_tx_valid hs hp (hr.1 ▸ hst)
    · rw [hr.1] at hst
      exact hs st hst

/-- Every state reached by the checked history has a signed transaction counter in range. -/
theorem CheckedLog.txValid {log : List (Record ι)} (h : CheckedLog log)
    {i : Nat} (hi : i ≤ log.length) {st : State} (hs : stateBefore log i = some st) :
    validTx st.tx :=
  history_tx_valid (h.prefix hi) (fun _ he => by cases he) st hs

/-- The precise record weights for an input object's transaction protocol. -/
inductive PairTxAction (r : Record ι) : Prop
  | init (h : ∃ count, r.action = .init count)
  | poll (h : ∃ parity ok, r.action = .pollParity parity ok)
  | expect (h : r.action = .arrive 1 32768)
  | notify (h : r.action = .completeTx 16384)

def pairTxCreditedIn (log : List (Record ι)) (phase : Nat) (act : Action)
    (index : Nat) : Prop :=
  phaseAt log index = some phase ∧
    ∃ r : Record ι, log[index]? = some r ∧ r.fault = none ∧ r.action = act

def pairTxPhaseRecords (log : List (Record ι)) (stop phase : Nat) (act : Action) :
    Finset Nat := by
  classical
  exact (Finset.range stop).filter (pairTxCreditedIn log phase act)

theorem memPairTxPhaseRecords {log : List (Record ι)} {stop phase index : Nat} {act : Action} :
    index ∈ pairTxPhaseRecords log stop phase act ↔
      index < stop ∧ pairTxCreditedIn log phase act index := by
  classical
  simp [pairTxPhaseRecords]

private theorem unitsAndBytes {log : List (Record ι)} {stop phase : Nat}
    (hShape : ∀ r ∈ log, PairTxAction r) :
    let expects := pairTxPhaseRecords log stop phase (.arrive 1 32768)
    let notifies := pairTxPhaseRecords log stop phase (.completeTx 16384)
    phaseUnits log stop phase = expects.card ∧
      phaseTx log stop phase = 32768 * (expects.card : Int) - 16384 * (notifies.card : Int) := by
  classical
  dsimp only
  have units (j : Nat) :
      (if phaseAt log j = some phase then unitsAt log j else 0) =
        if pairTxCreditedIn log phase (.arrive 1 32768) j then 1 else 0 := by
    cases h : log[j]? with
    | none => simp [pairTxCreditedIn, unitsAt, h]
    | some r =>
      cases hShape r (List.mem_of_getElem? h) with
      | init ha => obtain ⟨_, ha⟩ := ha; simp [pairTxCreditedIn, unitsAt, h, ha, Action.units]
      | poll ha => obtain ⟨_, _, ha⟩ := ha; simp [pairTxCreditedIn, unitsAt, h, ha, Action.units]
      | expect ha =>
        by_cases hf : r.fault = none <;> by_cases hp : phaseAt log j = some phase <;>
          simp [pairTxCreditedIn, unitsAt, h, ha, Action.units, hf, hp]
      | notify ha => simp [pairTxCreditedIn, unitsAt, h, ha, Action.units]
  have bytes (j : Nat) :
      (if phaseAt log j = some phase then txDeltaAt log j else 0) =
        (if pairTxCreditedIn log phase (.arrive 1 32768) j then (32768 : Int) else 0) -
        (if pairTxCreditedIn log phase (.completeTx 16384) j then (16384 : Int) else 0) := by
    cases h : log[j]? with
    | none => simp [pairTxCreditedIn, txDeltaAt, h]
    | some r =>
      have neutral (hz : r.action.txDelta = 0)
          (hn : r.action ≠ .arrive 1 32768) (ht : r.action ≠ .completeTx 16384) :
          (if phaseAt log j = some phase then txDeltaAt log j else 0) =
            (if pairTxCreditedIn log phase (.arrive 1 32768) j then (32768 : Int) else 0) -
            (if pairTxCreditedIn log phase (.completeTx 16384) j then (16384 : Int) else 0) := by
        simp [pairTxCreditedIn, txDeltaAt, Record.txDelta, h, hz, hn, ht]
      cases hShape r (List.mem_of_getElem? h) with
      | init ha =>
        obtain ⟨_, ha⟩ := ha
        exact neutral (by simp [ha, Action.txDelta]) (by simp [ha]) (by simp [ha])
      | poll ha =>
        obtain ⟨_, _, ha⟩ := ha
        exact neutral (by simp [ha, Action.txDelta]) (by simp [ha]) (by simp [ha])
      | expect ha =>
        by_cases hf : r.fault = none <;> by_cases hp : phaseAt log j = some phase <;>
          simp [pairTxCreditedIn, txDeltaAt, Record.txDelta, h, ha, Action.txDelta, hf, hp]
      | notify ha =>
        by_cases hf : r.fault = none <;> by_cases hp : phaseAt log j = some phase <;>
          simp [pairTxCreditedIn, txDeltaAt, Record.txDelta, h, ha, Action.txDelta, hf, hp]
  constructor
  · unfold phaseUnits pairTxPhaseRecords
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_congr rfl (fun j _ => units j)
  · calc
      phaseTx log stop phase =
          ∑ j ∈ Finset.range stop,
            ((if pairTxCreditedIn log phase (.arrive 1 32768) j then (32768 : Int) else 0) -
              (if pairTxCreditedIn log phase (.completeTx 16384) j then (16384 : Int) else 0)) :=
        Finset.sum_congr rfl (fun j _ => bytes j)
      _ = _ := by
        unfold pairTxPhaseRecords
        simp only [Finset.sum_sub_distrib, Finset.sum_ite, Finset.sum_const_zero, add_zero,
          Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- Every phase already completed before a checked state has one live 32768-byte
expectation and exactly two live 16384-byte notifications. -/
theorem completedPairTxCountsBeforeState {log : List (Record ι)} (hLog : CheckedLog log)
    (hNo : NoInval log) (hShape : ∀ r ∈ log, PairTxAction r)
    (hExpected : ∀ i st, stateBefore log i = some st → st.expected = 1)
    {j phase : Nat} {s : State} (hLen : j ≤ log.length)
    (hState : stateBefore log j = some s) (hLt : phase < s.phase) :
    ∃ stop ≤ j, (pairTxPhaseRecords log stop phase (.arrive 1 32768)).card = 1 ∧
      (pairTxPhaseRecords log stop phase (.completeTx 16384)).card = 2 ∧
      ∀ i r, log[i]? = some r → phaseAt log i = some phase → i < stop := by
  classical
  obtain ⟨q, hq, hCross⟩ := hLog.crossing hNo hLen hState hLt
  obtain ⟨hTx, hUnits⟩ := hLog.completion_sums hNo (hq.trans_le hLen) hCross
  let exp := pairTxPhaseRecords log (q + 1) phase (.arrive 1 32768)
  let nt := pairTxPhaseRecords log (q + 1) phase (.completeTx 16384)
  obtain ⟨hU, hT⟩ := unitsAndBytes (stop := q + 1) (phase := phase) hShape
  have hNoInc : incrementsBefore log log.length = 0 := by
    apply incrementsBefore_length_of
    intro r hr hi
    cases hShape r hr with
    | init ha => obtain ⟨_, ha⟩ := ha; rw [ha] at hi; cases hi
    | poll ha => obtain ⟨_, _, ha⟩ := ha; rw [ha] at hi; cases hi
    | expect ha | notify ha => rw [ha] at hi; cases hi
  have hUnit : ∀ (k : Nat) (r : Record ι) (c tx : Nat), log[k]? = some r → r.fault = none →
      r.action = .arrive c tx → c = 1 := by
    intro k r c tx hr _ ha
    cases hShape r (List.mem_of_getElem? hr) with
    | init h => obtain ⟨_, h⟩ := h; rw [h] at ha; cases ha
    | poll h => obtain ⟨_, _, h⟩ := h; rw [h] at ha; cases ha
    | expect h => exact (Action.arrive.inj (ha.symm.trans h)).1
    | notify h => rw [h] at ha; cases ha
  have hAll := hLog.card_unit_arrivals_phase hNo hUnit
    (fun i st _ hs => hExpected i st hs) hNoInc hLen hState hLt
  have hLe : exp.card ≤ 1 := by
    rw [← hAll]
    apply Finset.card_le_card
    intro i hi
    obtain ⟨hlt, hPhase, r, hr, hf, ha⟩ := memPairTxPhaseRecords.mp hi
    have hIndex : i < log.length := by omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hIndex, r, 32768, hr, ha, hf, hPhase⟩
  change phaseUnits log (q + 1) phase = exp.card at hU
  change phaseTx log (q + 1) phase = 32768 * (exp.card : Int) - 16384 * (nt.card : Int) at hT
  change 0 < phaseUnits log (q + 1) phase at hUnits
  change phaseTx log (q + 1) phase = 0 at hTx
  have hOne : exp.card = 1 := by omega
  have hTwo : nt.card = 2 := by omega
  refine ⟨q + 1, by omega, hOne, hTwo, ?_⟩
  intro i r hi hPhaseI
  obtain ⟨_, st, _, _, hAfter, hNext⟩ := hCross
  change stateBefore log (q + 1) = some st at hAfter
  change phaseAt log i = some phase at hPhaseI
  by_contra! hAfterI
  have hBefore : phaseAt log (q + 1) = some (phase + 1) := by
    simp [phaseAt, hAfter, hNext]
  cases hI : stateBefore log i with
  | none => simp [phaseAt, hI] at hPhaseI
  | some u =>
    have hu : u.phase = phase := by simpa [phaseAt, hI] using hPhaseI
    have hMono := hLog.phaseAt_le hNo (List.getElem?_eq_some_iff.mp hi).1.le hAfterI hI hBefore
    omega

/-- The observed generation has one live 32768-byte expectation and exactly two live
16384-byte tensor notifications in its completed prefix. -/
theorem completedPairTxCounts {log : List (Record ι)} (hLog : CheckedLog log)
    (hNo : NoInval log) (hShape : ∀ r ∈ log, PairTxAction r)
    (hExpected : ∀ i st, stateBefore log i = some st → st.expected = 1)
    {j phase : Nat} {poll : Record ι} (hj : log[j]? = some poll)
    (hSuccess : poll.reply.waited = some true) (hPhase : observedAt log j = some phase) :
    ∃ stop ≤ j, (pairTxPhaseRecords log stop phase (.arrive 1 32768)).card = 1 ∧
      (pairTxPhaseRecords log stop phase (.completeTx 16384)).card = 2 ∧
      ∀ i r, log[i]? = some r → phaseAt log i = some phase → i < stop := by
  obtain ⟨s, hState, hCompare⟩ := hLog.observed_phase hj hSuccess hPhase
  exact completedPairTxCountsBeforeState hLog hNo hShape hExpected
    (List.getElem?_eq_some_iff.mp hj).1.le hState (by omega)

end
end PTX.MBarrier
