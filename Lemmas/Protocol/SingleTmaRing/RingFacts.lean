-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.SingleTmaRing.Attribution
public import Lemmas.Protocol.PairTmaRing.Faults

@[expose] public section

/-! # What a single-CTA ring slot's attribution says about uses and transactions

A proof tool (generalized from the Inkling KV ring). From the ring of items (`ring`) and the
dependency order: a counted item of use `u ≥ 1` follows every consumer poll for a use below `u`
(`SF_reach`), so it lies in phase `u` or later (`use_le_phase`); the full barrier therefore has
at most `n` completions per phase reached (`completions_le`), and its transaction counter stays
within one use's `n · bytes` bytes (`full_tx_bounds`). The items of use 0 of a preloaded slot are
the preloading events, which no poll of `empty` guards (`SF_op`). -/

namespace PTX.SingleTmaRing
open PTX PTX.Flow AsyncCopy
open PTX.MBarrier hiding okPolls

noncomputable section


variable {X : Execution} {S : Slot} {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
  {sc : MbarScope}

theorem okPolls_take_le (m : Loc) (es : List Event) (k : Nat) :
    Flow.okPolls m (es.take k) ≤ Flow.okPolls m es := by
  unfold Flow.okPolls
  exact (List.take_sublist k es).countP_le

/-- A counted item of use `u ≥ 1` follows every consumer's poll for a use below `u`. -/
theorem SF_reach (hX : Consistent L K A mem0 X) (H : Hyp L K A X S sc) (hP : S.Fits)
    {x : Kind S × Nat}
    (hx : x ∈ SF X S) (b : Fin 1) {j : Nat} (hj : j < x.2) :
    X.RefPresent (.thread (wF X S b j)) ∧
      Relation.TransGen (DepStep L K X) (.thread (wF X S b j), true)
        (itF X S x.1 x.2, false) := by
  obtain ⟨hp, hpath⟩ := (ring hX H hP).reach_op hX.depAcyclic (a := kOwner x.1)
    (s := x.2) (op := opF X S x.1 x.2) (fun n h1 hn => guardP H hx h1 hn) b hj
  exact ⟨hp, hpath.trans_left (issueF hX H hx)⟩

/-- **An item lies in its use's phase or later.** -/
theorem use_le_phase (hX : Consistent L K A mem0 X) (H : Hyp L K A X S sc) (hP : S.Fits)
    {x : Kind S × Nat}
    (hx : x ∈ SF X S) {i : Nat} {r : Record Ref} (hi : (X.objects S.full)[i]? = some r)
    (hid : r.id = itF X S x.1 x.2) {st : State}
    (hst : stateBefore (X.objects S.full) i = some st) : x.2 ≤ st.phase := by
  rcases Nat.eq_zero_or_pos x.2 with h0 | hpos
  · omega
  have hch := X.objects_checked hX S.full
  have hni := H.full_noInval
  obtain ⟨hp, hpath⟩ := SF_reach hX H hP hx 0 (j := x.2 - 1) (by omega)
  obtain ⟨k, w, sk, hk, hwid, hww, hsk, hskp, -⟩ :=
    F_found hX H hP (b := 0) (MbarRing.Poll.nth_present.mp hp)
  have hnb := MbarRing.Round.Slot.not_before_of_reach (m := S.full) hX hpath
  obtain ⟨⟨i', r', hi', hid', -, h0, h1⟩, -⟩ := SF_op H hx
  have hii := ObjectInit.checked_record_index_eq hch hi hi' (hid.trans hid'.symm)
  subst hii
  rw [hi] at hi'
  cases hi'
  have hki : k < i := by
    rcases Nat.lt_trichotomy k i with h | rfl | h
    · exact h
    · rw [hi] at hk
      cases hk
      obtain ⟨-, p, -, hact, -⟩ := hch.okPoll hi hww
      by_cases hk0 : x.1.val = 0
      · rw [h0 hk0] at hact; cases hact
      · rw [h1 hk0] at hact; cases hact
    · exact absurd ⟨i, k, r, w, hi, hid, hk, hwid, h⟩ hnb
  have hil : i ≤ (X.objects S.full).length :=
    (List.getElem?_eq_some_iff.mp hi).1.le
  obtain ⟨t, ht', hle⟩ := hch.phase_mono hni hki.le hil hsk
  rw [hst] at ht'
  cases ht'
  omega

/-! ### The full barrier's transactions -/

/-- The fault-free completions of the full barrier before a position are at most eight per phase
reached. -/
theorem completions_le (hX : Consistent L K A mem0 X) (H : Hyp L K A X S sc) (hP : S.Fits) {j : Nat}
    (hj : j ≤ (X.objects S.full).length) {st : State}
    (hst : stateBefore (X.objects S.full) j = some st) :
    completedTxCount ((X.objects S.full).take j) ≤ S.n * (st.phase + 1) := by
  classical
  set log := X.objects S.full with hlog
  have hch : CheckedLog log := X.objects_checked hX S.full
  have hni := H.full_noInval
  let pred : Record Ref → Bool := fun r =>
    match r.action, r.fault with | .completeTx _, none => true | _, _ => false
  have hpred : ∀ r, pred r = true ↔ (∃ n, r.action = .completeTx n) ∧ r.fault = none := by
    intro r
    simp only [pred]
    cases r.action <;> cases r.fault <;> simp
  have hcnt : completedTxCount (log.take j) = (log.take j).countP pred := rfl
  rw [hcnt, MbarRing.Slot.countP_take_card]
  let T := (Finset.univ.filter (fun k : Kind S => k.val ≠ 0)) ×ˢ Finset.range (st.phase + 1)
  have hT : T.card = S.n * (st.phase + 1) := by
    have h8 : (Finset.univ.filter (fun k : Kind S => k.val ≠ 0)).card = S.n := by
      have he : Finset.univ.filter (fun k : Kind S => k.val ≠ 0) =
          Finset.univ.map (Fin.succEmb S.n) := by
        ext k
        refine Fin.cases ?_ (fun i => ?_) k
        · simp
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
            Fin.coe_succEmb, Fin.val_succ]
          exact ⟨fun _ => ⟨i, rfl⟩, fun _ => by omega⟩
      rw [he, Finset.card_map, Finset.card_univ, Fintype.card_fin]
    rw [Finset.card_product, Finset.card_range, h8]
  rw [← hT]
  refine PairTmaRing.card_le_of_rel _ T
    (fun k x => ∃ r, log[k]? = some r ∧ r.id = itF X S x.1 x.2)
    (fun k hk => ?_) (fun k hk k' hk' x _ ⟨r, hr, hrid⟩ ⟨r', hr', hrid'⟩ =>
      ObjectInit.checked_record_index_eq hch hr hr' (hrid.trans hrid'.symm))
  obtain ⟨hkj, hpk⟩ := Finset.mem_filter.mp hk
  have hkj' := Finset.mem_range.mp hkj
  obtain ⟨r, hr⟩ : ∃ r, log[k]? = some r := by
    cases h : log[k]? with
    | none => rw [h] at hpk; simp at hpk
    | some r => exact ⟨r, rfl⟩
  rw [hr] at hpk
  obtain ⟨⟨n, ha⟩, hf⟩ := (hpred r).mp hpk
  obtain ⟨x, hx, hid, hk0⟩ := full_item H (List.mem_of_getElem? hr) hf (.inr ⟨n, ha⟩)
  have hx0 : x.1.val ≠ 0 := fun h => by
    obtain ⟨n', tx', ha'⟩ := hk0.mpr h
    rw [ha] at ha'; cases ha'
  obtain ⟨-, sk, hsk, -⟩ := PairTmaRing.state_of_init hX H.full_init H.full_noInval hr
      (by intro n'; rw [ha]; simp)
  have hle := use_le_phase hX H hP hx hr hid hsk
  obtain ⟨t, ht', hph⟩ := hch.phase_mono hni hkj'.le hj hsk
  rw [hst] at ht'
  cases ht'
  exact ⟨x, Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx0⟩,
    Finset.mem_range.mpr (by omega)⟩, r, hr, hid⟩

/-- The full barrier's expected bytes are one use's per arrival unit. -/
theorem full_expected_bytes (H : Hyp L K A X S sc) :
    ∀ xs : List (Record Ref), (∀ r ∈ xs, r ∈ X.objects S.full) →
      expectedTxBytes xs = S.tx * arrivalUnits xs := by
  intro xs hxs
  induction xs with
  | nil => rfl
  | cons r rest ih =>
    have hr := hxs r List.mem_cons_self
    rw [expectedTxBytes, arrivalUnits, ih (fun q hq => hxs q (List.mem_cons_of_mem _ hq))]
    unfold Record.expectedTxBytes
    cases ha : r.action with
    | arrive n tx =>
      obtain ⟨rfl, rfl, -⟩ := arrival_source H hr ha
      cases r.fault
      · simp only; ring
      · simp
    | _ => cases r.fault <;> simp

/-- The full barrier's completed bytes are one copy per completion. -/
theorem full_uniform (H : Hyp L K A X S sc) : ∀ q ∈ X.objects S.full, ∀ n,
    q.action = .completeTx n → q.fault = none → n = S.bytes :=
  fun _ hq _ hn _ => (completion_source H hq hn).1

/-- **The full barrier's transaction counter** stays within one use's bytes. -/
theorem full_tx_bounds (hX : Consistent L K A mem0 X) (H : Hyp L K A X S sc) (hP : S.Fits) {j : Nat}
    (hj : j ≤ (X.objects S.full).length) {st : State}
    (hst : stateBefore (X.objects S.full) j = some st) :
    -(S.tx : Int) ≤ st.tx ∧ st.tx ≤ S.tx := by
  classical
  set log := X.objects S.full with hlog
  have hch : CheckedLog log := X.objects_checked hX S.full
  have hni := H.full_noInval
  have hexp := PairTmaRing.expected_of_init hX H.full_init H.full_noInval hst
  have htx : (S.tx : Int) = S.n * S.bytes := by simp [Slot.tx]
  constructor
  · have hbal := hch.tx_balance hni hj hst
    have he := full_expected_bytes H (log.take j) (fun q hq => List.mem_of_mem_take hq)
    have hu : UniformCompletedTx (log.take j) S.bytes := fun q hq hf n hn =>
      full_uniform H q (List.mem_of_mem_take hq) n hn hf
    have hc := completedTxBytes_eq_unit_mul_count hu
    obtain ⟨-, hacc⟩ := (hch.accounted hni hj).2 st hst
    have hcl := completions_le hX H hP hj hst
    simp only [unitsBefore] at hacc
    rw [he, hc] at hbal
    rw [hexp] at hacc
    have hu' : (st.phase : Int) ≤ (arrivalUnits (log.take j) : Int) := by
      have : st.phase ≤ arrivalUnits (log.take j) := by
        have := (hch.accounted hni hj).2 st hst
        rw [hexp] at this
        omega
      exact_mod_cast this
    have hcl' : ((completedTxCount (log.take j) : Nat) : Int) ≤ S.n *
        ((st.phase : Int) + 1) := by
      exact_mod_cast hcl
    have h1 : (S.bytes : Int) * (completedTxCount (log.take j) : Nat) ≤
        S.bytes * (S.n * ((st.phase : Int) + 1)) :=
      mul_le_mul_of_nonneg_left hcl' (by positivity)
    have h2 : (S.tx : Int) * ((st.phase : Int) + 1) ≤ S.tx * ((arrivalUnits
        (log.take j) : Int) + 1) :=
      mul_le_mul_of_nonneg_left (by omega) (by positivity)
    rw [htx] at h2
    rw [hbal]
    push_cast
    rw [htx]
    nlinarith
  · have htx' := hch.tx_eq hni hj hst
    have hpe := hch.pending_eq hni hj hst
    rw [hexp, phaseIncrements_eq_zero (fun r hr hi => by
      cases H.full_src r hr with
      | init ha | poll _ _ ha | arrive _ _ ha _ | preArrive _ _ _ ha | copy _ _ _ ha _
      | preCopy _ _ _ _ ha => rw [hi] at ha; cases ha)]
      at hpe
    have hle : phaseTx log j st.phase ≤ S.tx * (phaseUnits log j st.phase : Int) := by
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
              obtain ⟨rfl, rfl, -⟩ := arrival_source H (List.mem_of_getElem? hr) ha
              simp [Action.txDelta, Action.units]
            | completeTx n => simp [Action.txDelta, Action.units]
            | init n => simp [Action.txDelta, Action.units]
            | pollParity p ok => simp [Action.txDelta, Action.units]
            | inval => exact (hni r (List.mem_of_getElem? hr) ha).elim
            | increment => simp [Action.txDelta, Action.units]
          · rw [ite_eq_right hf, ite_eq_right hf]; simp
      · simp
    have : (phaseUnits log j st.phase : Int) ≤ 1 := by exact_mod_cast (by omega : _ ≤ 1)
    have h1 := mul_le_mul_of_nonneg_left this (by positivity : (0 : Int) ≤ S.tx)
    omega

/-- An empty barrier's transaction counter is zero: only unit notifications arrive on it, and
nothing completes on it. -/
theorem empty_tx_zero (hX : Consistent L K A mem0 X) (H : Hyp L K A X S sc) {j : Nat}
    (hj : j ≤ (X.objects S.empty).length) {st : State}
    (hst : stateBefore (X.objects S.empty) j = some st) : st.tx = 0 := by
  have hbal := (X.objects_checked hX _).tx_balance H.empty_noInval hj hst
  have hz : ∀ xs : List (Record Ref), (∀ r ∈ xs, r ∈ X.objects S.empty) →
      expectedTxBytes xs = 0 ∧ completedTxBytes xs = 0 := by
    intro xs hxs
    induction xs with
    | nil => exact ⟨rfl, rfl⟩
    | cons r rest ih =>
      have hr := hxs r List.mem_cons_self
      obtain ⟨h1, h2⟩ := ih (fun q hq => hxs q (List.mem_cons_of_mem _ hq))
      rw [expectedTxBytes, completedTxBytes, h1, h2]
      unfold Record.expectedTxBytes Record.completedTxBytes
      cases ha : r.action with
      | arrive n tx =>
        obtain ⟨-, rfl, -⟩ := notify_source H hr ha
        cases r.fault <;> simp
      | completeTx n =>
        exfalso
        cases H.empty_src r hr with
        | init ha' => rw [ha] at ha'; cases ha'
        | poll _ _ ha' => rw [ha] at ha'; cases ha'
        | notify _ _ _ _ ha' _ => rw [ha] at ha'; cases ha'
      | _ => cases r.fault <;> simp
  obtain ⟨h1, h2⟩ := hz _ (fun q hq => List.mem_of_mem_take hq)
  rw [hbal, h1, h2]
  rfl

end
end PTX.SingleTmaRing
