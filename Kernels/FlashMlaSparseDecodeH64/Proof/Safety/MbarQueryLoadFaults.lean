-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MbarSimpleFaults
public import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryTmaRecords
import Kernels.FlashMlaSparseDecodeH64.Proof.Protocol.QueryTmaCounts
import Lemmas.Protocol.MbarUnitTx

public section

/-! # Fault-free query tensor transfer barrier -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow AsyncCopy MBarrier

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private theorem query_load_clean_of_counts
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X) {cta : Nat}
    (hUnique : ∀ {r q : Record Ref} {n tx n' tx' : Nat},
      r ∈ X.objects (Protocol.QueryTmaRecords.object L cta) →
      q ∈ X.objects (Protocol.QueryTmaRecords.object L cta) →
      r.action = .arrive n tx → q.action = .arrive n' tx' → r.id = q.id)
    (hCount : ∀ k,
      completedTxCount ((X.objects (Protocol.QueryTmaRecords.object L cta)).take k) ≤ 8)
    {r : Record Ref} (hr : r ∈ X.objects (Protocol.QueryTmaRecords.object L cta)) :
    r.fault = none := by
  let sound := fun g hg => (hs g hg).machine
  let m := Protocol.QueryTmaRecords.object L cta
  let log := X.objects m
  have hFirst := Protocol.QueryTmaRecords.init_first (cta := cta) hpre hX sound ht
  have hNoInv := Protocol.objects_single_lifetime hX m
  have hLog := X.objects_checked hX m
  have hArr {q : Record Ref} {n tx : Nat} (hq : q ∈ log)
      (ha : q.action = .arrive n tx) : n = 1 ∧ tx = 65536 :=
    let h := Protocol.QueryTmaRecords.arrival_record hpre hX sound ht hq ha
    ⟨h.1, h.2.1⟩
  have hComp {q : Record Ref} {n : Nat} (hq : q ∈ log)
      (ha : q.action = .completeTx n) : n = 8192 :=
    (Protocol.QueryTmaRecords.completion_source hpre hX sound ht hq ha).1
  have hUnit (k : Nat) (q : Record Ref) (n tx : Nat)
      (hk : log[k]? = some q) (_ : q.fault = none) (ha : q.action = .arrive n tx) : n = 1 :=
    (hArr (List.mem_of_getElem? hk) ha).1
  have hUnits (k : Nat) : unitsBefore log k ≤ 1 := by
    by_cases hSome : ∃ (q : Record Ref), q ∈ log ∧ ∃ n tx, q.action = .arrive n tx
    · obtain ⟨q, hq, n, tx, ha⟩ := hSome
      simpa only [Finset.card_singleton] using hLog.unitsBefore_le_card (i := k) {q.id} hUnit
        (fun j _ q' n' tx' hj _ hb =>
          Finset.mem_singleton.mpr (hUnique (List.mem_of_getElem? hj) hq hb ha))
    · have h := hLog.unitsBefore_le_card (i := k) ∅ hUnit
        (fun j _ q' n' tx' hj _ hb => (hSome ⟨q', List.mem_of_getElem? hj, n', tx', hb⟩).elim)
      simpa using h.trans (by simp : (∅ : Finset Ref).card ≤ 1)
  have hTx {k : Nat} {st : State} (hk : k ≤ log.length)
      (hst : stateBefore log k = some st) : -(65536 : Int) ≤ st.tx ∧ st.tx ≤ 65536 := by
    have hexp : expectedTxBytes (log.take k) = 65536 * unitsBefore log k :=
      expectedTxBytes_unit (fun q hq _ _ _ ha => hArr (List.mem_of_mem_take hq) ha)
    have hcomp : completedTxBytes (log.take k) = 8192 * completedTxCount (log.take k) :=
      completedTxBytes_eq_unit_mul_count (fun q hq _ _ ha => hComp (List.mem_of_mem_take hq) ha)
    have hBalance := hLog.tx_balance hNoInv hk hst
    rw [hexp, hcomp] at hBalance
    have hBound := hUnits k
    have hCount : completedTxCount (log.take k) ≤ 8 := hCount k
    omega
  cases ha : r.action with
  | init n => exact mbar_init_clean hpre hX hs ht hr ha
  | pollParity p ok => exact mbar_poll_clean hpre hX hs ht hr ha
  | inval => exact (mbar_record_not_inval hX hr ha).elim
  | increment =>
    cases record_source hX.tma.2.2.1 hr with
    | increment _ he _ => exact (Protocol.no_async_arrive hX he rfl).elim
    | init _ _ h | arrive _ _ h | wait _ _ h | inval _ _ h | tensor _ _ _ h
    | arriveOn _ _ _ _ h | bulk _ _ _ _ h | commit _ _ _ h | clc _ _ _ _ h =>
      rw [ha] at h
      cases h
  | completeTx n =>
    obtain rfl := hComp hr ha
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
    obtain ⟨_, st, hSt, _⟩ := PairTmaRing.state_of_init hX hFirst hNoInv hk (by simp [ha])
    have hRange := hTx (List.getElem?_eq_some_iff.mp hk).1.le hSt
    have hOk := hLog.at hk
    rw [hSt] at hOk
    apply hOk.complete_fault_none ha (by decide)
    unfold validTx limit
    omega
  | arrive n tx =>
    obtain ⟨rfl, rfl⟩ := hArr hr ha
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
    obtain ⟨_, st, hSt, hExp⟩ := PairTmaRing.state_of_init hX hFirst hNoInv hk (by simp [ha])
    have hK := (List.getElem?_eq_some_iff.mp hk).1.le
    have hZero : unitsBefore log k = 0 := by
      apply Nat.eq_zero_of_le_zero
      simpa only [Finset.card_empty] using hLog.unitsBefore_le_card (i := k) ∅ hUnit
        (fun j hj q n tx hj' _ hb => by
          have hId := hUnique hr (List.mem_of_getElem? hj') ha hb
          exact (hj.ne (ObjectInit.checked_record_index_eq hLog hj' hk hId.symm)).elim)
    obtain ⟨hPending, hAccount⟩ := (hLog.accounted hNoInv hK).2 st hSt
    rw [hExp] at hPending hAccount
    change unitsBefore (X.objects m) k = 0 at hZero
    rw [hZero] at hAccount
    have hPhase : st.phase = 0 := by omega
    have hObserved := hLog.observed_of_poll hNoInv hSt (.inl hPhase)
    have hEnough : 1 ≤ st.pending := by omega
    have hRange := hTx hK hSt
    have hOk := hLog.at hk
    rw [hSt] at hOk
    apply hOk.arrive_fault_none ha (by decide) (by decide) hObserved hEnough
    unfold validTx limit
    omega

/-- The query tensor barrier never faults during its arrival, byte completions, or polls. -/
theorem mbar_query_load_clean
    (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.code P L g).Sound)
    (ht : Frame.Tracked (Machine.code P L) X)
    {cta : Nat} {r : Record Ref} (hr : r ∈ X.objects (Protocol.QueryTmaRecords.object L cta)) :
    r.fault = none := by
  let sound := fun g hg => (hs g hg).machine
  apply query_load_clean_of_counts hpre hX hs ht _ _ hr
  · intro r q n tx n' tx' hr hq ha hb
    exact Protocol.QueryTmaRecords.arrival_node_eq hpre hX sound ht hr hq ha hb
  · exact Protocol.QueryTmaRecords.completed_count_le hpre hX sound ht

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety
