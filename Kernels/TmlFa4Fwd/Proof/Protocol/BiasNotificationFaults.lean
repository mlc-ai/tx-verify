-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Protocol.BiasNotificationOrder
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

private theorem biasExpectedUnits {cta : Nat} (stage : Fin 2) (xs : List (Record Ref))
    (hSub : ∀ r ∈ xs, r ∈ X.objects (biasReadyObject l cta stage)) :
    expectedTxBytes xs = 32768 * arrivalUnits xs ∧ incrementUnits xs = 0 := by
  induction xs with
  | nil => exact ⟨rfl, rfl⟩
  | cons r xs ih =>
    obtain ⟨hBytes, hInc⟩ := ih (fun r hr => hSub r (List.mem_cons_of_mem _ hr))
    have hKind := biasReadyRecord hp hX stage (hSub r List.mem_cons_self)
    obtain ⟨act, ha, h⟩ : ∃ act, r.action = act ∧
        (act = .arrive 1 32768 ∨ act = .completeTx 16384 ∨
          (∃ n, act = .init n) ∨ (∃ q ok, act = .pollParity q ok)) := by
      cases hKind with
      | init hi => obtain ⟨n, ha⟩ := hi; exact ⟨_, ha, .inr (.inr (.inl ⟨n, rfl⟩))⟩
      | poll hi => obtain ⟨q, ok, ha⟩ := hi; exact ⟨_, ha, .inr (.inr (.inr ⟨q, ok, rfl⟩))⟩
      | expect _ _ _ ha => exact ⟨_, ha, .inl rfl⟩
      | notify _ _ _ _ _ _ ha => exact ⟨_, ha, .inr (.inl rfl)⟩
    rcases h with rfl | rfl | ⟨n, rfl⟩ | ⟨q, ok, rfl⟩ <;> cases hf : r.fault <;>
      simp [arrivalUnits, incrementUnits, expectedTxBytes, Record.expectedTxBytes,
        ha, hf, hBytes, hInc]
    omega

omit hp hX in
private def completedAt (log : List (Record Ref)) (i : Nat) : Prop :=
  ∃ r, log[i]? = some r ∧ r.action = .completeTx 16384 ∧ r.fault = none

private theorem biasCompletedBytes {cta : Nat} (stage : Fin 2) {i : Nat}
    (hi : i ≤ (X.objects (biasReadyObject l cta stage)).length) :
    let log := X.objects (biasReadyObject l cta stage)
    have := Classical.propDecidable
    completedTxBytes (log.take i) = 16384 * ((Finset.range i).filter (completedAt log)).card := by
  classical
  dsimp
  let log := X.objects (biasReadyObject l cta stage)
  have hAppend (xs ys : List (Record Ref)) :
      completedTxBytes (xs ++ ys) = completedTxBytes xs + completedTxBytes ys := by
    induction xs with
    | nil => simp [completedTxBytes]
    | cons r xs ih => simp [completedTxBytes, ih, Nat.add_assoc]
  induction i with
  | zero => simp [completedTxBytes]
  | succ i ih =>
    have hLt : i < log.length := hi
    obtain ⟨r, hr⟩ : ∃ r, log[i]? = some r := ⟨_, List.getElem?_eq_getElem hLt⟩
    have hTake : log.take (i + 1) = log.take i ++ [r] := by rw [List.take_add_one, hr]; rfl
    have hKind := biasReadyRecord hp hX stage (List.mem_of_getElem? hr)
    have hCase : r.completedTxBytes = if completedAt log i then 16384 else 0 := by
      unfold completedAt
      simp only [hr, Option.some.injEq, exists_eq_left']
      cases hKind with
      | init h => obtain ⟨n, ha⟩ := h; simp [Record.completedTxBytes, ha]
      | poll h => obtain ⟨q, ok, ha⟩ := h; simp [Record.completedTxBytes, ha]
      | expect _ _ _ ha => simp [Record.completedTxBytes, ha]
      | notify _ _ _ _ _ _ ha => cases hf : r.fault <;> simp [Record.completedTxBytes, ha, hf]
    have hPrev := ih (by omega)
    change completedTxBytes (log.take i) = 16384 *
      ((Finset.range i).filter (completedAt log)).card at hPrev
    change completedTxBytes (log.take (i + 1)) =
      16384 * ((Finset.range (i + 1)).filter (completedAt log)).card
    rw [hTake, hAppend, hPrev, Finset.range_add_one, Finset.filter_insert]
    by_cases h : completedAt log i
    · have hNot : i ∉ (Finset.range i).filter (completedAt log) := by simp
      simp only [h, ↓reduceIte, Finset.card_insert_of_notMem hNot, completedTxBytes,
        hCase, Nat.add_zero, Nat.mul_add]
    · simp [h, completedTxBytes, hCase]

private theorem biasCompletedCard {cta i : Nat} (stage : Fin 2) {s : State}
    (hi : i ≤ (X.objects (biasReadyObject l cta stage)).length)
    (hs : stateBefore (X.objects (biasReadyObject l cta stage)) i = some s) :
    let log := X.objects (biasReadyObject l cta stage)
    have := Classical.propDecidable
    ((Finset.range i).filter (completedAt log)).card ≤ 2 * (s.phase + 1) := by
  classical
  dsimp
  let loc := biasReadyObject l cta stage
  let log := X.objects loc
  let eligible := (Finset.range i).filter (completedAt log)
  have hNo := objects_noInval hX.tma.2.2.1 (fun i _ => noMbarInval hX (i := i)) loc
  have hChecked := X.objects_checked hX loc
  have hLabel (k : Nat) (hk : k ∈ eligible) :
      ∃ (r : Record Ref) (e : EvId) (half : Fin 2) (box : TensorCopy.Spec),
        log[k]? = some r ∧ r.id = .async e (.notify .load) ∧
          e.1 / l.block = cta ∧ BiasSubbox p l X e stage half box ∧
          biasTensorOrdinal l X stage half e ≤ s.phase := by
    obtain ⟨hk, r, hr, ha, _⟩ := Finset.mem_filter.mp hk
    have hBefore := Finset.mem_range.mp hk
    cases biasReadyRecord hp hX stage (List.mem_of_getElem? hr) with
    | init h => obtain ⟨_, h⟩ := h; rw [h] at ha; cases ha
    | poll h => obtain ⟨_, _, h⟩ := h; rw [h] at ha; cases ha
    | expect _ _ _ h => rw [h] at ha; cases ha
    | notify e half box hId hOwner hBox _ =>
      obtain ⟨_, t, ht, _⟩ := PairTmaRing.state_of_init hX
        (biasReadyInit hp hX stage (List.mem_of_getElem? hr)) hNo hr
        (by intro n; rw [ha]; simp)
      have hLo := biasNotificationPhaseLower hp hX stage hr hId hOwner hBox ha ht
      obtain ⟨u, hu, hMono⟩ := hChecked.phase_mono hNo hBefore.le hi ht
      rw [hs] at hu
      obtain rfl := Option.some.inj hu
      exact ⟨r, e, half, box, hr, hId, hOwner, hBox, hLo.trans hMono⟩
  let target := (Finset.univ : Finset (Fin 2)) ×ˢ Finset.range (s.phase + 1)
  have hTarget : target.card = 2 * (s.phase + 1) := by simp [target]
  rw [← hTarget]
  change eligible.card ≤ target.card
  choose rr ee hh bb hhGet hhId hhOwner hhBox hhLower using hLabel
  let label (k : Nat) : Fin 2 × Nat :=
    if h : k ∈ eligible then (hh k h, biasTensorOrdinal l X stage (hh k h) (ee k h)) else (0, 0)
  apply Finset.card_le_card_of_injOn label
  · intro k hk
    have hk' : k ∈ eligible := hk
    change (if h : k ∈ eligible then (hh k h, _) else (0, 0)) ∈ target
    rw [dite_eq_left hk', Finset.mem_product, Finset.mem_range]
    exact ⟨Finset.mem_univ _, Nat.lt_succ_of_le (hhLower k hk')⟩
  · intro k hk k' hk' hEq
    have hK : k ∈ eligible := hk
    have hK' : k' ∈ eligible := hk'
    dsimp only [label] at hEq
    rw [dite_eq_left hK, dite_eq_left hK'] at hEq
    have hHalf : hh k hK = hh k' hK' := congrArg Prod.fst hEq
    have hOrdinal : biasTensorOrdinal l X stage (hh k hK) (ee k hK) =
        biasTensorOrdinal l X stage (hh k' hK') (ee k' hK') := congrArg Prod.snd hEq
    have hSame := biasTensorOrdinalInjective hp hX (hhBox k hK)
      (hHalf.symm ▸ hhBox k' hK') ((hhOwner k hK).trans (hhOwner k' hK').symm)
      (hOrdinal.trans (by rw [hHalf]))
    have hid := (hhId k hK).trans ((congrArg (fun a => Ref.async a (.notify .load)) hSame).trans
      (hhId k' hK').symm)
    exact ObjectInit.checked_record_index_eq hChecked (hhGet k hK) (hhGet k' hK') hid

/-- The actual notifications of each stage fit the signed transaction counter,
even when both halves finish ahead of their expectation. -/
theorem biasNotificationClean {cta i : Nat} (stage : Fin 2) {r : Record Ref}
    (hr : (X.objects (biasReadyObject l cta stage))[i]? = some r)
    (ha : r.action = .completeTx 16384) : r.fault = none := by
  classical
  let loc := biasReadyObject l cta stage
  let log := X.objects loc
  have hLen : i ≤ log.length := (List.getElem?_eq_some_iff.mp hr).1.le
  have hNo := objects_noInval hX.tma.2.2.1 (fun i _ => noMbarInval hX (i := i)) loc
  have hChecked := X.objects_checked hX loc
  have hInit := biasReadyInit hp hX stage (List.mem_of_getElem? hr)
  obtain ⟨_, s, hs, _⟩ := PairTmaRing.state_of_init hX hInit hNo hr
    (by intro n; rw [ha]; simp)
  have hExpected := PairTmaRing.expected_of_init hX hInit hNo hs
  obtain ⟨hBytes, hInc⟩ := biasExpectedUnits hp hX stage (log.take i)
    (fun _ h => List.mem_of_mem_take h)
  have hIncrements : incrementsBefore log i = 0 := hInc
  obtain ⟨hPending, hUnits⟩ := (hChecked.accounted hNo hLen).2 s hs
  change s.pending ≤ s.expected + incrementsBefore log i at hPending
  change unitsBefore log i + s.pending = s.expected * (s.phase + 1) +
    incrementsBefore log i at hUnits
  rw [hExpected, hIncrements] at hPending hUnits
  have hPositiveBytes : 32768 * s.phase ≤ expectedTxBytes (log.take i) := by
    change expectedTxBytes (log.take i) = 32768 * unitsBefore log i at hBytes
    omega
  have hCompleted := biasCompletedBytes hp hX stage hLen
  have hCard := biasCompletedCard hp hX stage hLen hs
  change completedTxBytes (log.take i) =
    16384 * ((Finset.range i).filter (completedAt log)).card at hCompleted
  change ((Finset.range i).filter (completedAt log)).card ≤ 2 * (s.phase + 1) at hCard
  have hNegBytes : completedTxBytes (log.take i) ≤ 32768 * (s.phase+1) := by omega
  have hBalance := hChecked.tx_balance hNo hLen hs
  change s.tx = (expectedTxBytes (log.take i) : Int) - completedTxBytes (log.take i)
    at hBalance
  have hValid := hChecked.txValid hLen hs
  have hWindow : validTx (s.tx - 16384) := by
    obtain ⟨_, _⟩ := hValid
    unfold validTx limit at *
    omega
  have hOK := hChecked.at hr
  rw [hs] at hOK
  exact PairTmaRing.complete_fault_free hOK ha (by decide) hWindow

/-- Both physical Bias-ready objects are free of faults in every consistent prefix. -/
theorem biasReadyHistoryClean {cta : Nat} (stage : Fin 2) {r : Record Ref}
    (hr : r ∈ X.objects (biasReadyObject l cta stage)) : r.fault = none := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
  cases biasReadyRecord hp hX stage hr with
  | init h => exact actualInitOrPollClean hp hX hr (.inl h)
  | poll h => exact actualInitOrPollClean hp hX hr (.inr h)
  | expect _ _ _ ha => exact biasExpectationClean hp hX stage hi ha
  | notify _ _ _ _ _ _ ha => exact biasNotificationClean hp hX stage hi ha

/-- An actual expectation and two distinct completions suffice to finish the opening
Bias-ready phase, regardless of later reuse. -/
theorem biasReadyAdvancedOfCredits {cta : Nat} (stage : Fin 2) {credit left right : Record Ref}
    (hCredit : credit ∈ X.objects (biasReadyObject l cta stage))
    (hExpected : credit.action = .arrive 1 32768)
    (hLeft : left ∈ X.objects (biasReadyObject l cta stage))
    (hRight : right ∈ X.objects (biasReadyObject l cta stage)) (hDifferent : left ≠ right)
    (hLeftTx : left.action = .completeTx 16384) (hRightTx : right.action = .completeTx 16384) :
    let log := X.objects (biasReadyObject l cta stage)
    ∃ s, stateBefore log log.length = some s ∧ 1 ≤ s.phase := by
  classical
  let loc := biasReadyObject l cta stage
  let log := X.objects loc
  have hChecked := X.objects_checked hX loc
  have hNo := objects_noInval hX.tma.2.2.1 (fun i _ => noMbarInval hX (i := i)) loc
  obtain ⟨init, hInit, hInitAct, hInitClean, _⟩ := biasReadyInit hp hX stage hCredit credit hCredit
  have hLength : 0 < log.length := (List.getElem?_eq_some_iff.mp hInit).1
  obtain ⟨s, hState, hCount⟩ := ObjectInit.checked_expected_after_init hChecked hNo
    hInit hInitAct hInitClean hLength (Nat.le_refl _)
  refine ⟨s, hState, ?_⟩
  by_contra! hZero
  have hz : s.phase = 0 := by omega
  have hUnits : 1 ≤ arrivalUnits log := by
    rw [arrivalUnits_eq_length]
    · apply List.length_pos_of_mem (a := credit)
      exact List.mem_filter.mpr ⟨hCredit, countedArrive_iff.mpr
        ⟨biasReadyHistoryClean hp hX stage hCredit, 1, 32768, hExpected⟩⟩
    · intro r hr c tx _ ha
      cases biasReadyRecord hp hX stage hr with
      | init h => obtain ⟨_, h⟩ := h; rw [h] at ha; cases ha
      | poll h => obtain ⟨_, _, h⟩ := h; rw [h] at ha; cases ha
      | expect _ _ _ h => exact (Action.arrive.inj (ha.symm.trans h)).1
      | notify _ _ _ _ _ _ h => rw [h] at ha; cases ha
  obtain ⟨hBytes, hInc⟩ := biasExpectedUnits hp hX stage log (fun _ hr => hr)
  have hBefore := ((hChecked.accounted hNo (Nat.le_refl _)).2 s hState).2
  change arrivalUnits (log.take log.length) + s.pending =
    s.expected*(s.phase+1) + incrementUnits (log.take log.length) at hBefore
  rw [List.take_length, hCount, hz, hInc] at hBefore
  have hOne : arrivalUnits log = 1 := by omega
  have hPending : s.pending = 0 := by omega
  let eligible := (Finset.range log.length).filter (completedAt log)
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hLeft
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hRight
  have hiEligible : i ∈ eligible := Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (List.getElem?_eq_some_iff.mp hi).1,
      left, hi, hLeftTx, biasReadyHistoryClean hp hX stage hLeft⟩
  have hjEligible : j ∈ eligible := Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (List.getElem?_eq_some_iff.mp hj).1,
      right, hj, hRightTx, biasReadyHistoryClean hp hX stage hRight⟩
  have hNe : i ≠ j := by
    intro h
    subst j
    exact hDifferent (Option.some.inj (hi.symm.trans hj))
  have hTwo := Finset.one_lt_card.mpr ⟨i, hiEligible, j, hjEligible, hNe⟩
  have hUpper : eligible.card ≤ 2 := by
    have hBound := biasCompletedCard hp hX stage (Nat.le_refl _) hState
    change eligible.card ≤ 2 * (s.phase + 1) at hBound
    omega
  have hNotes : eligible.card = 2 := by omega
  have hCompleted := biasCompletedBytes hp hX stage (Nat.le_refl log.length)
  change completedTxBytes (log.take log.length) = 16384 * eligible.card at hCompleted
  rw [List.take_length, hNotes] at hCompleted
  have hBalance := hChecked.tx_balance hNo (Nat.le_refl _) hState
  change s.tx = (expectedTxBytes (log.take log.length) : Int) -
    completedTxBytes (log.take log.length) at hBalance
  rw [List.take_length, hBytes, hOne, hCompleted] at hBalance
  have hPos := stateBefore_pending_pos hChecked hState (by omega : s.tx = 0)
  omega

end PTX.Kernels.TmlFa4Fwd.Protocol.Bias
