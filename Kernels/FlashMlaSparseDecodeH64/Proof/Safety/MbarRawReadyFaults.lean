-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Safety.MbarRawFaults
import Lemmas.Protocol.PairTmaRing.Faults
import Lemmas.Protocol.GatedFaults

@[expose] public section

/-! # Transaction and generation bounds for the raw-ready objects -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow PTX.AsyncCopy PTX.MbarRing Protocol RawRing
open _root_.PTX.MBarrier hiding okPolls

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}
variable {cta issuer : Nat} {slot : Fin 2}

local notation "object" => ready L cta slot
local notation "log" => X.objects (ready L cta slot)

private theorem raw_ready_no_increment (hX : Consistent L kernel Assumptions.all mem0 X)
    {r : Record Ref} (hr : r ∈ log) : r.action ≠ .increment := by
  intro ha
  cases record_source hX.tma.2.2.1 hr with
  | increment _ he _ => exact no_async_arrive hX he rfl
  | init _ _ ha' | inval _ _ ha' | arrive _ _ ha' | wait _ _ ha'
  | tensor _ _ _ ha' | arriveOn _ _ _ _ ha' | bulk _ _ _ _ ha' | commit _ _ _ ha'
  | clc _ _ _ _ ha' =>
    rw [ha] at ha'
    cases ha'

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : ∀ g < L.threads, (Machine.machine P L g).Sound) (ht : Frame.Tracked (Machine.code P L) X)
include hpre hX hs ht

private theorem raw_ready_poll_parity {g i tag p : Nat} {acq : Bool} {scope : MbarScope}
    (he : X.get (g, i) = some ⟨tag, .wait object p true acq scope⟩) :
    p % 2 = (okPolls object ((X.tr g).take i) + 0) % 2 := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨_, _, hc, d, hb, hd, hp, hState⟩ :=
    await_ready_source hpre hX (hs g hg) ht he rfl
  have hCount := Wg2RawTrace.composed_raw_ready_count hpre
    ((hs g hg).produces (hX.thr g hg)) hState hd
  rw [hc, hb] at hCount
  change okPolls object ((X.tr g).take i) = _ at hCount
  rw [hCount, hp]
  omega

/-- Each successful raw-ready update has a unique gather or arrival item of the issuer. -/
theorem raw_ready_item_of_record (hIssuer : Issuer P L X cta issuer) {r : Record Ref} (hr : r ∈ log)
    (hf : r.fault = none) (ha : (∃ n tx, r.action = .arrive n tx) ∨ ∃ n, r.action = .completeTx n) :
    ∃ x ∈ countedFull X object issuer, r.id = itemFull X object issuer x.1 x.2 ∧
      r.action = actionFull x.1 := by
  classical
  obtain ⟨x, hx, hid⟩ := counted_of_record hpre hX hs ht hIssuer hr hf ha
  obtain ⟨_, r', hr', hid', _, hAct⟩ := Finset.mem_filter.mp hx
  have hSame := hX.record_eq hr' hr (hid'.trans hid.symm)
  exact ⟨x, hx, hid, hSame ▸ hAct⟩

private theorem raw_ready_poll_found (hIssuer : Issuer P L X cta issuer) {b : Fin 128} {j : Nat}
    (hj : j < okPolls object (X.tr (consumer L cta b))) :
    ∃ k w st, log[k]? = some w ∧
      w.id = .thread (consumer L cta b, Poll.nth X object (consumer L cta b) j) ∧
      w.reply.waited = some true ∧ stateBefore log k = some st ∧ st.phase = j + 1 := by
  classical
  let R := items (slot := slot) issuer hpre hX hs ht hIssuer
  let c := consumer L cta b
  have hInit := ready_init_first hpre hX hs ht (cta := cta) (slot := slot)
  have hn := objects_single_lifetime hX object
  have hClean := PairTmaRing.poll_clean hX hInit hn
  obtain ⟨k, w, _, hk, hid, _, hw, _, hCount⟩ := Poll.record hX hClean hj
  have hAlt := Poll.alternates hX hClean (g := c)
    (δ := 0) (fun _ _ _ _ _ he => raw_ready_poll_parity hpre hX hs ht he)
  have hSel : objectThreadSelected c w.id = true := objectThreadSelected_iff.mpr ⟨_, hid⟩
  obtain ⟨st, hSt, hPhase⟩ := R.full_poll_phase hX (b := b)
    ({0} : Finset Item) (by simp) hn (objectThreadSelected c) (by decide : 0 ≤ 1) hAlt
    (fun k r u tx hk hf ha => by
      have hr := List.mem_of_getElem? hk
      obtain ⟨rfl, rfl, _⟩ := ready_arrival_record hpre hX hs ht hr ha
      obtain ⟨x, hx, hid, hAct⟩ :=
        raw_ready_item_of_record hpre hX hs ht hIssuer hr hf (.inl ⟨1, 36864, ha⟩)
      have hx0 : x.1 = 0 := by
        unfold actionFull at hAct
        split at hAct
        · exact Fin.ext (by assumption)
        · rw [ha] at hAct
          cases hAct
      exact ⟨rfl, x, Finset.mem_filter.mpr ⟨hx, Finset.mem_singleton.mpr hx0⟩, hid⟩)
    (fun _ _ h => by simpa using PairTmaRing.expected_of_init hX hInit hn h)
    hk hid hw hSel (by simpa only [Nat.add_zero] using hCount)
  exact ⟨k, w, st, hk, hid, hw, hSt, hPhase⟩

private theorem raw_ready_poll_before_update (hIssuer : Issuer P L X cta issuer) {i j : Nat}
    {r : Record Ref} (hi : log[i]? = some r) (hr : CounterUpdate r.action)
    (hPresent : X.RefPresent (.thread (consumer L cta 0, Poll.nth X object (consumer L cta 0) j)))
    (hPath : Relation.TransGen (DepStep L kernel X)
      (.thread (consumer L cta 0, Poll.nth X object (consumer L cta 0) j), true)
      (r.id, false)) :
    ∃ k w st, k < i ∧ log[k]? = some w ∧
      w.reply.waited = some true ∧ stateBefore log k = some st ∧ st.phase = j + 1 := by
  obtain ⟨k, w, st, hk, hid, hw, hSt, hPhase⟩ :=
    raw_ready_poll_found hpre hX hs ht hIssuer (b := 0) (Poll.nth_present.mp hPresent)
  have hBefore : k < i := by
    rcases Nat.lt_trichotomy k i with h | rfl | h
    · exact h
    · rw [hi] at hk
      obtain rfl := Option.some.inj hk
      obtain ⟨_, _, _, hAct, _⟩ := (X.objects_checked hX object).okPoll hi hw
      rw [hAct] at hr
      exact hr.elim
    · exact (Round.Slot.not_before_of_reach (m := object) hX hPath
        ⟨i, k, r, w, hi, rfl, hk, hid, h⟩).elim
  exact ⟨k, w, st, hBefore, hk, hw, hSt, hPhase⟩

private theorem raw_ready_item_use_le (hIssuer : Issuer P L X cta issuer) {x : Item × Nat}
    (hx : x ∈ countedFull X object issuer) {i : Nat} {r : Record Ref} (hi : log[i]? = some r)
    (ha : CounterUpdate r.action) (hid : r.id = itemFull X object issuer x.1 x.2) {st : State}
    (hSt : stateBefore log i = some st) : x.2 ≤ st.phase := by
  rcases Nat.eq_zero_or_pos x.2 with hzero | hpos
  · exact hzero ▸ Nat.zero_le _
  let R := items (slot := slot) issuer hpre hX hs ht hIssuer
  have hPath : Relation.TransGen (DepStep L kernel X)
      (.thread (consumer L cta 0,
        Poll.nth X object (consumer L cta 0) (x.2 - 1)), true) (r.id, false) := by
    rw [hid]
    exact (R.reach hX.depAcyclic).1 0 x hx 0 (x.2 - 1) (by omega)
  obtain ⟨j, w, s, hji, _, _, hS, hPhase⟩ :=
    raw_ready_poll_before_update hpre hX hs ht hIssuer hi ha (present_of_path hPath) hPath
  obtain ⟨st', hEq, hMono⟩ := (X.objects_checked hX object).phase_mono
    (objects_single_lifetime hX object) hji.le (List.getElem?_eq_some_iff.mp hi).1.le hS
  rw [hSt] at hEq
  cases hEq
  omega

/-- Completed gather transactions cannot be more than one generation ahead of the phase. -/
theorem raw_ready_completion_count_le (hIssuer : Issuer P L X cta issuer) {i : Nat}
    (hi : i ≤ (log).length) {st : State} (hSt : stateBefore log i = some st) :
    completedTxCount ((log).take i) ≤ 16 * (st.phase + 1) := by
  classical
  let pred : Record Ref → Bool := fun r =>
    match r.action, r.fault with
    | .completeTx _, none => true
    | _, _ => false
  have hPred (r : Record Ref) :
      pred r = true ↔ (∃ n, r.action = .completeTx n) ∧ r.fault = none := by
    simp only [pred]
    cases r.action <;> cases r.fault <;> simp
  change ((log).take i).countP pred ≤ _
  rw [MbarRing.Slot.countP_take_card]
  let C : Finset Item := Finset.univ.filter (fun k : Item => k.val ≠ 0)
  let T := C ×ˢ Finset.range (st.phase + 1)
  have hT : T.card = 16 * (st.phase + 1) := by
    rw [Finset.card_product, Finset.card_range]
    have h : C.card = 16 := by decide
    rw [h]
  rw [← hT]
  refine PairTmaRing.card_le_of_rel _ T
    (fun k x => ∃ r, log[k]? = some r ∧ r.id = itemFull X object issuer x.1 x.2)
    (fun k hk => ?_) (fun k hk k' hk' x _ ⟨r, hr, hid⟩ ⟨r', hr', hid'⟩ =>
      ObjectInit.checked_record_index_eq (X.objects_checked hX object) hr hr' (hid.trans hid'.symm))
  obtain ⟨hki, hcheck⟩ := Finset.mem_filter.mp hk
  have hki' := Finset.mem_range.mp hki
  obtain ⟨r, hr⟩ : ∃ r, log[k]? = some r := by
    cases he : log[k]? with
    | none => rw [he] at hcheck; simp at hcheck
    | some r => exact ⟨r, rfl⟩
  rw [hr] at hcheck
  obtain ⟨⟨n, ha⟩, hf⟩ := (hPred r).mp hcheck
  obtain ⟨x, hx, hid, hAct⟩ :=
    raw_ready_item_of_record hpre hX hs ht hIssuer (List.mem_of_getElem? hr) hf (.inr ⟨n, ha⟩)
  have hNe : x.1.val ≠ 0 := by
    intro hz
    simp only [actionFull, hz, ite_true] at hAct
    rw [ha] at hAct
    cases hAct
  have hNo := objects_single_lifetime hX object
  have hInit := ready_init_first hpre hX hs ht (cta := cta) (slot := slot)
  obtain ⟨_, s, hS, _⟩ := PairTmaRing.state_of_init hX hInit hNo hr (by intro n; rw [ha]; simp)
  have hu := raw_ready_item_use_le hpre hX hs ht hIssuer hx hr (by rw [ha]; trivial) hid hS
  obtain ⟨st', hSt', hMono⟩ := (X.objects_checked hX object).phase_mono hNo hki'.le hi hS
  rw [hSt] at hSt'
  cases hSt'
  exact ⟨x, Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hNe⟩,
    Finset.mem_range.mpr (by omega)⟩, r, hr, hid⟩

/-- Each successful expectation arrival accounts for one full raw buffer. -/
theorem raw_ready_expected_bytes :
    ∀ rs : List (Record Ref), (∀ r ∈ rs, r ∈ log) →
      expectedTxBytes rs = 36864 * arrivalUnits rs := by
  intro rs hRs
  induction rs with
  | nil => rfl
  | cons r rest ih =>
    have hr := hRs r List.mem_cons_self
    rw [expectedTxBytes, arrivalUnits, ih (fun q hq => hRs q (List.mem_cons_of_mem _ hq))]
    unfold Record.expectedTxBytes
    cases ha : r.action with
    | arrive n tx =>
      obtain ⟨rfl, rfl, _⟩ := ready_arrival_record hpre hX hs ht hr ha
      cases r.fault
      · simp
        omega
      · simp
    | _ => cases r.fault <;> simp

private theorem raw_ready_tx_bounds (hIssuer : Issuer P L X cta issuer) {i : Nat}
    (hi : i ≤ (log).length) {st : State} (hSt : stateBefore log i = some st) :
    -36864 ≤ st.tx ∧ st.tx ≤ 36864 := by
  have hch := X.objects_checked hX object
  have hNo := objects_single_lifetime hX object
  have hInit := ready_init_first hpre hX hs ht (cta := cta) (slot := slot)
  have hExp := PairTmaRing.expected_of_init hX hInit hNo hSt
  constructor
  · have hBalance := hch.tx_balance hNo hi hSt
    have hExpected := raw_ready_expected_bytes (cta := cta) (slot := slot) hpre hX hs ht
      ((log).take i) (fun _ h => List.mem_of_mem_take h)
    have hUniform : UniformCompletedTx ((log).take i) 2304 := fun r hr _ n ha =>
      (gather_record hpre hX hs ht (List.mem_of_mem_take hr) ha).1
    have hCompleted := completedTxBytes_eq_unit_mul_count hUniform
    have hCount := raw_ready_completion_count_le hpre hX hs ht hIssuer hi hSt
    obtain ⟨hPending, hUnits⟩ := (hch.accounted hNo hi).2 st hSt
    rw [hExp] at hPending hUnits
    simp only [unitsBefore] at hUnits
    rw [hExpected, hCompleted] at hBalance
    push_cast at hBalance
    omega
  · have hTx := hch.tx_eq hNo hi hSt
    have hPending := hch.pending_eq hNo hi hSt
    rw [hExp, phaseIncrements_eq_zero (fun r hr => raw_ready_no_increment hX hr)] at hPending
    have hLe : phaseTx log i st.phase ≤ 36864 * (phaseUnits log i st.phase : Int) := by
      unfold phaseTx phaseUnits
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun k hk => ?_)
      split_ifs
      · unfold txDeltaAt unitsAt
        cases hr : log[k]? with
        | none => simp
        | some r =>
          simp only
          unfold Record.txDelta
          by_cases hf : r.fault = none
          · rw [ite_eq_left hf, ite_eq_left hf]
            cases ha : r.action with
            | arrive n tx =>
              obtain ⟨rfl, rfl, _⟩ :=
                ready_arrival_record hpre hX hs ht (List.mem_of_getElem? hr) ha
              simp [Action.txDelta, Action.units]
            | completeTx n => simp [Action.txDelta, Action.units]
            | init n => simp [Action.txDelta, Action.units]
            | pollParity p ok => simp [Action.txDelta, Action.units]
            | inval => exact (hNo r (List.mem_of_getElem? hr) ha).elim
            | increment => simp [Action.txDelta, Action.units]
          · rw [ite_eq_right hf, ite_eq_right hf]; simp
      · simp
    omega

private theorem raw_ready_arrival_clean (hIssuer : Issuer P L X cta issuer) {i : Nat}
    {r : Record Ref} (hi : log[i]? = some r) (ha : r.action = .arrive 1 36864) (hf : r.fault ≠ none)
    :
    r.fault ≠ some .arrivalUnderflow ∧ r.fault ≠ some .precedingPhaseNotObserved := by
  classical
  let R := items (slot := slot) issuer hpre hX hs ht hIssuer
  have hch := X.objects_checked hX object
  have hNo := objects_single_lifetime hX object
  have hInit := ready_init_first hpre hX hs ht (cta := cta) (slot := slot)
  have hr := List.mem_of_getElem? hi
  obtain ⟨_, _, g, j, e, d, hid, he, hk, hc, hSite, hSlot, hState⟩ :=
    ready_arrival_record hpre hX hs ht hr ha
  have hg := hIssuer g j d hc hState (.inl hSite)
  subst g
  let n := arrivals object ((X.tr issuer).take j)
  have hg := Frame.lt_of_get hX he
  obtain ⟨hn, hp⟩ := TmaRawTrace.composed_publish_counts hpre
    ((hs issuer hg).produces (hX.thr issuer hg)) hState hSite
  rw [hc, hSlot] at hn hp
  change n = d.block / 2 at hn
  change okPolls (free L cta slot) ((X.tr issuer).take j) = d.block / 2 + 1 at hp
  have hTick : arrivesOn object e = true := by simp [arrivesOn, sourceArrive, hk]
  have hItem : itemFull X object issuer (0 : Item) n = r.id := by
    rw [hid]
    change Ref.thread (issuer, nthEv X (arrivesOn object) issuer n) = .thread (issuer, j)
    rw [← nthEv_eq he hTick]
    rfl
  have hAbsent : (0, n) ∉ countedFull X object issuer := by
    intro h
    obtain ⟨_, r', hr', hid', hf', _⟩ := Finset.mem_filter.mp h
    exact hf (hX.record_eq hr' hr (hid'.trans hItem) ▸ hf')
  have hUse (x : Item × Nat) (hx : x ∈ countedFull X object issuer) : x.2 ≤ n := by
    by_contra! hlt
    have hPath := (R.reach hX.depAcyclic).1 0 x hx 0 n hlt
    have hPresent := present_of_path hPath
    exact hAbsent (R.observes_full hX.depAcyclic hPresent 0).1
  have hUnits : unitsBefore log i ≤ n := by
    let T : Finset (Item × Nat) := {0} ×ˢ Finset.range n
    have hCard : T.card = n := by simp [T]
    rw [← hCard]
    refine Round.units_le_of_uses hch (fun x => itemFull X object issuer x.1 x.2) T
      (fun k r c tx hk _ ha => (ready_arrival_record hpre hX hs ht (List.mem_of_getElem? hk) ha).1)
      (fun k _ r c tx hk hf ha => ?_)
    obtain ⟨rfl, rfl, _⟩ := ready_arrival_record hpre hX hs ht (List.mem_of_getElem? hk) ha
    obtain ⟨x, hx, hid, hAct⟩ := raw_ready_item_of_record hpre hX hs ht hIssuer
      (List.mem_of_getElem? hk) hf (.inl ⟨1, 36864, ha⟩)
    have hx0 : x.1 = 0 := by
      unfold actionFull at hAct
      split at hAct
      · exact Fin.ext (by assumption)
      · rw [ha] at hAct
        cases hAct
    have hn' : x.2 ≠ n := by
      intro hxN
      exact hAbsent ((Prod.ext hx0 hxN : x = (0, n)) ▸ hx)
    refine ⟨x, Finset.mem_product.mpr
      ⟨Finset.mem_singleton.mpr hx0, Finset.mem_range.mpr (lt_of_le_of_ne (hUse x hx) hn')⟩, hid⟩
  have hGuard (k : Nat) (_ : 1 ≤ k) (hK : k ≤ n) :
      Resumes kernel X (R.wE 0 k) (issuer, j) :=
    Poll.guard (fun _ _ _ _ _ _ hw => RingSpins.successful_poll hX hw) (PTX.len_of_get he)
      (by omega)
  apply hch.arrive_fault_free hNo (s := n) hi ha
  · intro st hSt
    rw [PairTmaRing.expected_of_init hX hInit hNo hSt]
    omega
  · intro q hq hqN
    obtain ⟨hPresent, hPath⟩ := R.reach_op hX.depAcyclic hGuard 0 (j := q - 1) (by omega)
    rw [← hid] at hPath
    obtain ⟨k, w, st, hLt, hk, hw, hSt, hPhase⟩ :=
      raw_ready_poll_before_update hpre hX hs ht hIssuer hi (by rw [ha]; trivial) hPresent hPath
    exact ⟨k, w, st, hLt, hk, hw, hSt, by omega⟩

/-- Every raw-ready expectation and gather completion fits the transaction counter and
occurs in its permitted barrier generation. -/
theorem raw_ready_fault_free :
    ∀ r ∈ log, r.fault = none := by
  obtain ⟨lane, _, hIssuer⟩ := selected_tma (cta := cta) hpre hX hs
  have hch := X.objects_checked hX object
  have hNo := objects_single_lifetime hX object
  have hInit := ready_init_first hpre hX hs ht (cta := cta) (slot := slot)
  intro r hr
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
  have hLt := (List.getElem?_eq_some_iff.mp hi).1.le
  cases ha : r.action with
  | init n => exact PairTmaRing.init_clean hInit hr ha
  | pollParity p ok => exact PairTmaRing.poll_clean hX hInit hNo r hr ⟨p, ok, ha⟩
  | inval => exact (hNo r hr ha).elim
  | increment => exact (raw_ready_no_increment hX hr ha).elim
  | completeTx n =>
    obtain ⟨rfl, _⟩ := gather_record hpre hX hs ht hr ha
    obtain ⟨_, st, hSt, _⟩ := PairTmaRing.state_of_init hX hInit hNo hi (by simp [ha])
    obtain ⟨hLo, hHi⟩ := raw_ready_tx_bounds hpre hX hs ht hIssuer hLt hSt
    have hOk := hch.at hi
    rw [hSt] at hOk
    exact PairTmaRing.complete_fault_free hOk ha (by decide) (by unfold validTx limit; omega)
  | arrive n tx =>
    obtain ⟨rfl, rfl, _⟩ := ready_arrival_record hpre hX hs ht hr ha
    obtain ⟨_, st, hSt, _⟩ := PairTmaRing.state_of_init hX hInit hNo hi (by simp [ha])
    obtain ⟨hLo, hHi⟩ := raw_ready_tx_bounds hpre hX hs ht hIssuer hLt hSt
    have hOk := hch.at hi
    rw [hSt] at hOk
    rcases PairTmaRing.arrive_fault_cases hOk ha (by decide) (by decide)
      (by unfold validTx limit; omega) with hClean | hOld | hUnder
    · exact hClean
    · have hBad : r.fault ≠ none := by simp [hOld]
      exact ((raw_ready_arrival_clean hpre hX hs ht hIssuer hi ha hBad).2 hOld).elim
    · have hBad : r.fault ≠ none := by simp [hUnder]
      exact ((raw_ready_arrival_clean hpre hX hs ht hIssuer hi ha hBad).1 hUnder).elim

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety
