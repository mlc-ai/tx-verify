-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.TmaUnits
import Lemmas.Protocol.GatedFaults
import Lemmas.Protocol.SingleTmaRing.Faults

@[expose] public section

/-! # A full barrier fed by one thread's TMA copies is fault-free

A proof tool. For the object of `TmaUnits.Obj` (one thread's expect-tx arrivals and tensor copies),
when an item of use `u ≥ 1` follows in the history a successful poll that found a phase of at least
`u` (`hgate`) and a use whose arrival is not counted has no counted item of a later use (`hle`):
the completions before a position are at most `n` per phase reached, so the transaction counter
stays within one use's bytes (`tx_bounds`), and an arrival finds its phase observed and pending
(`fault_free`). -/

namespace PTX.MbarRing.TmaUnits
open PTX PTX.Proof PTX.Flow AsyncCopy
open PTX.MBarrier hiding okPolls

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {m : Loc} {y n bytes : Nat}

/-- An item of use `u ≥ 1` follows, in the history, a successful poll that found phase `u` or a
later one. -/
def Gated (X : Execution) (m : Loc) (y n : Nat) : Prop :=
  ∀ {k : Nat} {r : Record Ref} (x : Fin (n + 1) × Nat), (X.objects m)[k]? = some r →
    r.id = it X m y n x.1 x.2 →
    ((∃ c tx, r.action = .arrive c tx) ∨ ∃ b, r.action = .completeTx b) →
    1 ≤ x.2 → ∃ kw w sw, kw < k ∧ (X.objects m)[kw]? = some w ∧
      w.reply.waited = some true ∧ stateBefore (X.objects m) kw = some sw ∧ x.2 ≤ sw.phase

namespace Obj

theorem use_le (hX : Consistent L K A mem0 X) (o : Obj X m y n bytes) (hg : Gated X m y n)
    {k j : Nat} {r : Record Ref} (x : Fin (n + 1) × Nat) (hr : (X.objects m)[k]? = some r)
    (hid : r.id = it X m y n x.1 x.2)
    (hact : (∃ c tx, r.action = .arrive c tx) ∨ ∃ b, r.action = .completeTx b) (hkj : k ≤ j)
    (hj : j ≤ (X.objects m).length) {st : State}
    (hst : stateBefore (X.objects m) j = some st) : x.2 ≤ st.phase := by
  rcases Nat.eq_zero_or_pos x.2 with h0 | hpos
  · omega
  · obtain ⟨kw, w, sw, hkw, -, -, hsw, hle⟩ := hg x hr hid hact hpos
    obtain ⟨t, ht, hph⟩ := (X.objects_checked hX m).phase_mono o.noInval (by omega) hj hsw
    rw [hst] at ht
    cases ht
    omega

theorem completions_le (hX : Consistent L K A mem0 X) (o : Obj X m y n bytes) (hn : 0 < n)
    (hg : Gated X m y n) {j : Nat} (hj : j ≤ (X.objects m).length) {st : State}
    (hst : stateBefore (X.objects m) j = some st) :
    completedTxCount ((X.objects m).take j) ≤ n * (st.phase + 1) := by
  classical
  set log := X.objects m with hlog
  have hch : CheckedLog log := X.objects_checked hX m
  let pred : Record Ref → Bool := fun r =>
    match r.action, r.fault with | .completeTx _, none => true | _, _ => false
  have hpred : ∀ r, pred r = true ↔ (∃ n, r.action = .completeTx n) ∧ r.fault = none := by
    intro r
    simp only [pred]
    cases r.action <;> cases r.fault <;> simp
  have hcnt : completedTxCount (log.take j) = (log.take j).countP pred := rfl
  rw [hcnt, MbarRing.Slot.countP_take_card]
  let T := (Finset.univ.filter (fun k : Fin (n + 1) => k.val ≠ 0)) ×ˢ Finset.range (st.phase + 1)
  have hT : T.card = n * (st.phase + 1) := by
    have h8 : (Finset.univ.filter (fun k : Fin (n + 1) => k.val ≠ 0)).card = n := by
      have he : Finset.univ.filter (fun k : Fin (n + 1) => k.val ≠ 0) =
          Finset.univ.map (Fin.succEmb n) := by
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
    (fun k x => ∃ r, log[k]? = some r ∧ r.id = it X m y n x.1 x.2)
    (fun k hk => ?_) (fun k hk k' hk' x _ ⟨r, hr, hrid⟩ ⟨r', hr', hrid'⟩ =>
      ObjectInit.checked_record_index_eq hch hr hr' (hrid.trans hrid'.symm))
  obtain ⟨hkj, hpk⟩ := Finset.mem_filter.mp hk
  have hkj' := Finset.mem_range.mp hkj
  obtain ⟨r, hr⟩ : ∃ r, log[k]? = some r := by
    cases h : log[k]? with
    | none => rw [h] at hpk; simp at hpk
    | some r => exact ⟨r, rfl⟩
  rw [hr] at hpk
  obtain ⟨⟨b, ha⟩, hf⟩ := (hpred r).mp hpk
  obtain ⟨x, hx, hid⟩ := o.item hr hf (.inr ⟨b, ha⟩) hn
  have hx0 : x.1.val ≠ 0 := fun h => by
    obtain ⟨-, i, pc, al, sp, hid', -⟩ := o.copy hr ha
    rw [hid'] at hid
    simp [it, h] at hid
  have hle := o.use_le hX hg x hr hid (.inr ⟨b, ha⟩) hkj'.le hj hst
  exact ⟨x, Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx0⟩,
    Finset.mem_range.mpr (by omega)⟩, r, hr, hid⟩

theorem expected_bytes (o : Obj X m y n bytes) :
    ∀ xs : List (Record Ref), (∀ r ∈ xs, r ∈ X.objects m) →
      expectedTxBytes xs = n * bytes * arrivalUnits xs := by
  intro xs hxs
  induction xs with
  | nil => rfl
  | cons r rest ih =>
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp (hxs r List.mem_cons_self)
    rw [expectedTxBytes, arrivalUnits, ih (fun q hq => hxs q (List.mem_cons_of_mem _ hq))]
    unfold Record.expectedTxBytes
    cases ha : r.action with
    | arrive c tx =>
      obtain ⟨rfl, rfl, -⟩ := o.arrive hk ha
      cases r.fault
      · simp only; ring
      · simp
    | _ => cases r.fault <;> simp

/-- **The transaction counter stays within one use's bytes.** -/
theorem tx_bounds (hX : Consistent L K A mem0 X) (o : Obj X m y n bytes) (hn : 0 < n)
    (hg : Gated X m y n) {j : Nat} (hj : j ≤ (X.objects m).length) {st : State}
    (hst : stateBefore (X.objects m) j = some st) :
    -((n * bytes : Nat) : Int) ≤ st.tx ∧ st.tx ≤ ((n * bytes : Nat) : Int) := by
  classical
  set log := X.objects m with hlog
  have hch : CheckedLog log := X.objects_checked hX m
  have hni := o.noInval
  have hexp := PairTmaRing.expected_of_init hX o.init o.noInval hst
  constructor
  · have hbal := hch.tx_balance hni hj hst
    have he := o.expected_bytes (log.take j) (fun q hq => List.mem_of_mem_take hq)
    have hu : UniformCompletedTx (log.take j) bytes := fun q hq hf b hb => by
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take hq)
      exact (o.copy hk hb).1
    have hc := completedTxBytes_eq_unit_mul_count hu
    have hcl := o.completions_le hX hn hg hj hst
    rw [he, hc] at hbal
    have hu' : st.phase ≤ arrivalUnits (log.take j) := by
      have := (hch.accounted hni hj).2 st hst
      rw [hexp] at this
      simp only [unitsBefore] at this
      omega
    have h1 : bytes * completedTxCount (log.take j) ≤ bytes * (n * (st.phase + 1)) :=
      Nat.mul_le_mul_left _ hcl
    have h2 : n * bytes * (st.phase + 1) ≤ n * bytes * (arrivalUnits (log.take j) + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have h3 : bytes * completedTxCount (log.take j) ≤
        n * bytes * arrivalUnits (log.take j) + n * bytes := by nlinarith
    rw [hbal]
    have h3' : ((bytes * completedTxCount (log.take j) : Nat) : Int) ≤
        ((n * bytes * arrivalUnits (log.take j) + n * bytes : Nat) : Int) := by exact_mod_cast h3
    push_cast at h3' ⊢
    linarith
  · have htx' := hch.tx_eq hni hj hst
    have hpe := hch.pending_eq hni hj hst
    rw [hexp, phaseIncrements_eq_zero (fun r hr hi => o.incr r hr hi)] at hpe
    have hle : phaseTx log j st.phase ≤
        ((n * bytes : Nat) : Int) * (phaseUnits log j st.phase : Int) := by
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
            | arrive c tx =>
              obtain ⟨rfl, rfl, -⟩ := o.arrive hr ha
              simp [Action.txDelta, Action.units]
            | completeTx b => simp [Action.txDelta, Action.units]
            | init b => simp [Action.txDelta, Action.units]
            | pollParity p ok => simp [Action.txDelta, Action.units]
            | inval => exact (hni r (List.mem_of_getElem? hr) ha).elim
            | increment => simp [Action.txDelta, Action.units]
          · rw [ite_eq_right hf, ite_eq_right hf]; simp
      · simp
    have h1' : (phaseUnits log j st.phase : Int) ≤ 1 := by
      exact_mod_cast (by omega : phaseUnits log j st.phase ≤ 1)
    have h1 := mul_le_mul_of_nonneg_left h1' (by positivity : (0 : Int) ≤ ((n * bytes : Nat) : Int))
    omega

/-- **Fault freedom of a full barrier of one thread's tensor copies.** -/
theorem fault_free (hX : Consistent L K A mem0 X) (o : Obj X m y n bytes) (hn : 0 < n)
    (hfit : 2 * (n * bytes) ≤ limit) (hg : Gated X m y n)
    (hle : ∀ t, ((⟨0, Nat.succ_pos n⟩ : Fin (n + 1)), t) ∉ S X m y n bytes →
      ∀ x ∈ S X m y n bytes, x.2 ≤ t) : ∀ r ∈ X.objects m, r.fault = none := by
  classical
  intro r hr
  set log := X.objects m with hlog
  have hch : CheckedLog log := X.objects_checked hX m
  have hni := o.noInval
  have hlim : limit = 1048575 := rfl
  have hbn : bytes ≤ n * bytes := Nat.le_mul_of_pos_left _ hn
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
  have hil : i ≤ log.length := (List.getElem?_eq_some_iff.mp hi).1.le
  cases ha : r.action with
  | inval => exact (hni r hr ha).elim
  | increment => exact (o.incr r hr ha).elim
  | init b => exact PairTmaRing.init_clean o.init hr ha
  | pollParity p ok => exact PairTmaRing.poll_clean hX o.init hni r hr ⟨p, ok, ha⟩
  | completeTx b =>
    obtain ⟨rfl, -⟩ := o.copy hi ha
    obtain ⟨-, st, hst, -⟩ := PairTmaRing.state_of_init hX o.init hni hi
      (by intro n; rw [ha]; simp)
    obtain ⟨hlo, hhi⟩ := o.tx_bounds hX hn hg hil hst
    have hok := hch.at hi
    rw [show stateBefore log i = some st from hst] at hok
    exact PairTmaRing.complete_fault_free hok ha (by unfold validTxOperand; omega)
      (by unfold validTx; omega)
  | arrive c tx =>
    obtain ⟨rfl, rfl, j, pc, rel, sc, hid, he⟩ := o.arrive hi ha
    obtain ⟨-, st, hst, -⟩ := PairTmaRing.state_of_init hX o.init hni hi
      (by intro n; rw [ha]; simp)
    have hst' : stateBefore log i = some st := hst
    obtain ⟨hlo, hhi⟩ := o.tx_bounds hX hn hg hil hst
    have hok := hch.at hi
    rw [hst'] at hok
    have hexp := PairTmaRing.expected_of_init hX o.init hni hst
    -- the arrival's use
    set u := arrivals m ((X.tr y).take j) with hu
    have hp : arrivesOn m ⟨pc, .arrive m (n * bytes) 1 rel sc⟩ = true := by
      simp [arrivesOn, sourceArrive]
    have hit : r.id = it X m y n (⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) u := by
      rw [hid]
      simp only [it, op, ↓reduceIte, hu]
      unfold arrivals
      rw [nthEv_eq he hp]
    by_contra hf
    have hnot : ((⟨0, Nat.succ_pos n⟩ : Fin (n + 1)), u) ∉ S X m y n bytes := by
      intro hx
      obtain ⟨-, r', hr', hid', hf', -⟩ := Finset.mem_filter.mp hx
      rw [hX.record_eq hr' hr (hid'.trans hit.symm)] at hf'
      exact hf hf'
    have huses := hle u hnot
    have hunits : unitsBefore log i ≤ u := by
      have h := MbarRing.Round.units_le_of_uses hch
        (fun z : _root_.Unit × Nat => it X m y n (⟨0, Nat.succ_pos n⟩ : Fin (n + 1)) z.2)
        (Finset.univ ×ˢ Finset.range u) (i := i)
        (fun k r c' tx hr _ ha => (o.arrive hr ha).1)
        (fun k _ r' c' tx hr' hf' ha' => by
          obtain ⟨x, hx, hid'⟩ := o.item hr' hf' (.inl ⟨_, _, ha'⟩) hn
          obtain ⟨-, -, j', pc', rel', sc', hidr, -⟩ := o.arrive hr' ha'
          have hx0 : x.1 = ⟨0, Nat.succ_pos n⟩ := by
            apply Fin.ext
            by_contra hne
            rw [hidr] at hid'
            simp only [it] at hid'
            rw [ite_eq_right hne] at hid'
            cases hid'
          have hxu : x.2 ≠ u := fun h => hnot (by rw [← hx0, ← h]; exact hx)
          exact ⟨((), x.2), Finset.mem_product.mpr ⟨Finset.mem_univ _,
            Finset.mem_range.mpr (by have := huses x hx; omega)⟩, by rw [hid', hx0]⟩)
      simpa using h
    have hph := o.use_le hX hg ((⟨0, Nat.succ_pos n⟩ : Fin (n + 1)), u) hi hit
      (.inl ⟨_, _, ha⟩) le_rfl hil hst
    simp only at hph
    have hacc := (hch.accounted hni hil).2 st hst
    rw [hexp] at hacc
    have hobs : st.observed = true := by
      refine hch.observed_of_poll hni hst ?_
      rcases Nat.eq_zero_or_pos u with h0 | hpos
      · exact .inl (by omega)
      · obtain ⟨kw, w, sw, hkw, hw, hww, hsw, h1⟩ :=
          hg ((⟨0, Nat.succ_pos n⟩ : Fin (n + 1)), u) hi hit (.inl ⟨_, _, ha⟩)
            hpos
        simp only at h1
        obtain ⟨t, ht, hmono⟩ := hch.phase_mono hni hkw.le hil hsw
        rw [hst'] at ht
        cases ht
        exact .inr ⟨kw, w, sw, hkw, hw, hww, hsw, by omega⟩
    rcases PairTmaRing.arrive_fault_cases hok ha (by unfold validCount limit; omega)
      (by unfold validTxOperand; omega) (by unfold validTx; push_cast; omega) with h | h | h
    · exact hf h
    · exfalso
      unfold RecordOk at hok
      rw [ha] at hok
      simp only [perform, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, hobs] at hok
      split_ifs at hok <;> simp_all
    · exfalso
      unfold RecordOk at hok
      rw [ha] at hok
      simp only [perform, bind, Except.bind, pure, Except.pure, throw, throwThe,
        MonadExceptOf.throw, hobs] at hok
      split_ifs at hok <;> simp_all
      omega

end Obj

end
end PTX.MbarRing.TmaUnits
