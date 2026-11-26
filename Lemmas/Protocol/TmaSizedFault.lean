-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.TmaSized
public import Lemmas.Protocol.TmaUnitsFault

@[expose] public section

/-! # A full barrier fed by one thread's TMA copies of several sizes is fault-free

A proof tool, the analog of `TmaUnitsFault` (`Lemmas/Protocol/TmaUnitsFault.lean`) for the object
of `TmaSized.Obj`. When an item of use `u ≥ 1` follows in the history a successful poll that
found a phase of at least `u` (`Gated`), and a use whose arrival is not counted has no counted
item of a later use (`hle`):

* the completions before a position are items of the uses up to the phase reached, and each
  kind of each use is counted once, so they move at most `U · W` bytes per phase reached
  (`Obj.completed_le`; in `TmaUnitsFault` this is a count of copies, here a count of units);
* so the transaction counter stays within one use's bytes (`Obj.tx_bounds`);
* so a completion keeps the counter in range and an arrival finds its phase observed and
  pending (`Obj.fault_free`).

`completedTxBytes_eq_sum` and `completedTxBytes_take` express the completed bytes of a history
as a sum over its positions. -/

namespace PTX.MbarRing.TmaSized
open PTX PTX.Proof PTX.Flow AsyncCopy
open PTX.MBarrier hiding okPolls

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {m : Loc} {y n W U : Nat} {cp : Fin W → Nat}

/-- The completed bytes of a history are the sum of the completed bytes of its positions. -/
theorem completedTxBytes_eq_sum (log : List (Record Ref)) :
    completedTxBytes log = ∑ k ∈ Finset.range log.length, cbAt log k := by
  induction log with
  | nil => simp [completedTxBytes]
  | cons r rest ih =>
    rw [completedTxBytes, List.length_cons, Finset.sum_range_succ', ih, Nat.add_comm]
    congr 1

/-- The completed bytes of a prefix of a history. -/
theorem completedTxBytes_take (log : List (Record Ref)) {j : Nat} (hj : j ≤ log.length) :
    completedTxBytes (log.take j) = ∑ k ∈ Finset.range j, cbAt log k := by
  rw [completedTxBytes_eq_sum, List.length_take, Nat.min_eq_left hj]
  refine Finset.sum_congr rfl fun k hk => ?_
  unfold cbAt
  rw [List.getElem?_take, ite_eq_left (Finset.mem_range.mp hk)]

/-- An item of use `u ≥ 1` follows, in the history, a successful poll that found phase `u` or a
later one. -/
def Gated (X : Execution) (m : Loc) (y n : Nat) (cp : Fin W → Nat) : Prop :=
  ∀ {k : Nat} {r : Record Ref} (x : Fin (W + 1) × Nat), (X.objects m)[k]? = some r →
    r.id = it X m y n cp x.1 x.2 →
    ((∃ c tx, r.action = .arrive c tx) ∨ ∃ b, r.action = .completeTx b) →
    1 ≤ x.2 → ∃ kw w sw, kw < k ∧ (X.objects m)[kw]? = some w ∧
      w.reply.waited = some true ∧ stateBefore (X.objects m) kw = some sw ∧ x.2 ≤ sw.phase

namespace Obj

theorem use_le (hX : Consistent L K A mem0 X) (o : Obj X m y n U cp) (hg : Gated X m y n cp)
    {k j : Nat} {r : Record Ref} (x : Fin (W + 1) × Nat) (hr : (X.objects m)[k]? = some r)
    (hid : r.id = it X m y n cp x.1 x.2)
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

/-- **The completions before a position move at most `U · W` bytes per phase reached.** -/
theorem completed_le (hX : Consistent L K A mem0 X) (o : Obj X m y n U cp) (hU : 0 < U)
    (hg : Gated X m y n cp) {j : Nat} (hj : j ≤ (X.objects m).length) {st : State}
    (hst : stateBefore (X.objects m) j = some st) :
    completedTxBytes ((X.objects m).take j) ≤ U * W * (st.phase + 1) := by
  classical
  rw [completedTxBytes_take _ hj]
  have hdiv : ∑ k ∈ Finset.range j, cbAt (X.objects m) k =
      U * ∑ k ∈ Finset.range j, cbAt (X.objects m) k / U := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => (Nat.mul_div_cancel' (o.cb_dvd k)).symm
  rw [hdiv, Nat.mul_assoc]
  refine Nat.mul_le_mul_left U ?_
  have hT : ((Finset.univ.erase (0 : Fin (W + 1))) ×ˢ Finset.range (st.phase + 1)).card =
      W * (st.phase + 1) := by simp
  rw [← hT]
  calc ∑ k ∈ Finset.range j, cbAt (X.objects m) k / U
      ≤ ∑ k ∈ Finset.range j, ((itemsAt X m y n U cp k).filter fun x => x.1 ≠ 0).card :=
        Finset.sum_le_sum fun k _ => o.cb_le hU k
    _ = ((Finset.range j).biUnion fun k =>
          (itemsAt X m y n U cp k).filter fun x => x.1 ≠ 0).card :=
        (Finset.card_biUnion fun k _ k' _ h =>
          Finset.disjoint_filter_filter (itemsAt_disjoint hX h)).symm
    _ ≤ _ := Finset.card_le_card (Finset.biUnion_subset.mpr fun k hk x hx => by
        obtain ⟨hxI, hx0⟩ := Finset.mem_filter.mp hx
        obtain ⟨r, hr, hid, -, -, h1⟩ := itemsAt_rec hX hxI
        have hle := o.use_le hX hg x hr hid (.inr (h1 hx0)) (Finset.mem_range.mp hk).le hj hst
        exact Finset.mem_product.mpr ⟨Finset.mem_erase.mpr ⟨hx0, Finset.mem_univ _⟩,
          Finset.mem_range.mpr (by omega)⟩)

theorem expected_bytes (o : Obj X m y n U cp) :
    ∀ xs : List (Record Ref), (∀ r ∈ xs, r ∈ X.objects m) →
      expectedTxBytes xs = U * W * arrivalUnits xs := by
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
theorem tx_bounds (hX : Consistent L K A mem0 X) (o : Obj X m y n U cp) (hU : 0 < U)
    (hg : Gated X m y n cp) {j : Nat} (hj : j ≤ (X.objects m).length) {st : State}
    (hst : stateBefore (X.objects m) j = some st) :
    -((U * W : Nat) : Int) ≤ st.tx ∧ st.tx ≤ ((U * W : Nat) : Int) := by
  classical
  set log := X.objects m with hlog
  have hch : CheckedLog log := X.objects_checked hX m
  have hni := o.noInval
  have hexp := PairTmaRing.expected_of_init hX o.init o.noInval hst
  constructor
  · have hbal := hch.tx_balance hni hj hst
    have he := o.expected_bytes (log.take j) (fun q hq => List.mem_of_mem_take hq)
    have hcl := o.completed_le hX hU hg hj hst
    rw [he] at hbal
    have hu' : st.phase ≤ arrivalUnits (log.take j) := by
      have := (hch.accounted hni hj).2 st hst
      rw [hexp] at this
      simp only [unitsBefore] at this
      omega
    have h2 : U * W * (st.phase + 1) ≤ U * W * (arrivalUnits (log.take j) + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have h3 : completedTxBytes (log.take j) ≤
        U * W * arrivalUnits (log.take j) + U * W := by
      have := hcl.trans h2
      rwa [Nat.mul_add, Nat.mul_one] at this
    rw [hbal]
    have h3' : ((completedTxBytes (log.take j) : Nat) : Int) ≤
        ((U * W * arrivalUnits (log.take j) + U * W : Nat) : Int) := by exact_mod_cast h3
    push_cast at h3' ⊢
    linarith
  · have htx' := hch.tx_eq hni hj hst
    have hpe := hch.pending_eq hni hj hst
    rw [hexp, phaseIncrements_eq_zero (fun r hr hi => o.incr r hr hi)] at hpe
    have hle : phaseTx log j st.phase ≤
        ((U * W : Nat) : Int) * (phaseUnits log j st.phase : Int) := by
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
    have h1 := mul_le_mul_of_nonneg_left h1' (by positivity : (0 : Int) ≤ ((U * W : Nat) : Int))
    omega

/-- **Fault freedom of a full barrier of one thread's tensor copies of several sizes.** -/
theorem fault_free (hX : Consistent L K A mem0 X) (o : Obj X m y n U cp) (hU : 0 < U)
    (hW : 0 < W) (hfit : 2 * (U * W) ≤ limit) (hg : Gated X m y n cp)
    (hle : ∀ t, ((0 : Fin (W + 1)), t) ∉ S X m y n U cp →
      ∀ x ∈ S X m y n U cp, x.2 ≤ t) : ∀ r ∈ X.objects m, r.fault = none := by
  classical
  intro r hr
  set log := X.objects m with hlog
  have hch : CheckedLog log := X.objects_checked hX m
  have hni := o.noInval
  have hlim : limit = 1048575 := rfl
  have hUW : 0 < U * W := Nat.mul_pos hU hW
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
  have hil : i ≤ log.length := (List.getElem?_eq_some_iff.mp hi).1.le
  cases ha : r.action with
  | inval => exact (hni r hr ha).elim
  | increment => exact (o.incr r hr ha).elim
  | init b => exact PairTmaRing.init_clean o.init hr ha
  | pollParity p ok => exact PairTmaRing.poll_clean hX o.init hni r hr ⟨p, ok, ha⟩
  | completeTx b =>
    obtain ⟨j, pc, al, sp, -, -, -, rfl⟩ := o.copy hi ha
    have hb : U * wt cp (((X.tr y).take j).countP (issuesTo m) % n) ≤ U * W :=
      Nat.mul_le_mul_left _ (wt_le cp _)
    obtain ⟨-, st, hst, -⟩ := PairTmaRing.state_of_init hX o.init hni hi
      (by intro n; rw [ha]; simp)
    obtain ⟨hlo, hhi⟩ := o.tx_bounds hX hU hg hil hst
    have hok := hch.at hi
    rw [show stateBefore log i = some st from hst] at hok
    exact PairTmaRing.complete_fault_free hok ha (by unfold validTxOperand; omega)
      (by unfold validTx; omega)
  | arrive c tx =>
    obtain ⟨rfl, rfl, j, pc, rel, sc, hid, he⟩ := o.arrive hi ha
    obtain ⟨-, st, hst, -⟩ := PairTmaRing.state_of_init hX o.init hni hi
      (by intro n; rw [ha]; simp)
    have hst' : stateBefore log i = some st := hst
    obtain ⟨hlo, hhi⟩ := o.tx_bounds hX hU hg hil hst
    have hok := hch.at hi
    rw [hst'] at hok
    have hexp := PairTmaRing.expected_of_init hX o.init hni hst
    -- the arrival's use
    set u := arrivals m ((X.tr y).take j) with hu
    have hp : arrivesOn m ⟨pc, .arrive m (U * W) 1 rel sc⟩ = true := by
      simp [arrivesOn, sourceArrive]
    have hit : r.id = it X m y n cp 0 u := by
      rw [hid, it_zero, hu]
      unfold arrivals
      rw [nthEv_eq he hp]
    by_contra hf
    have hnot : ((0 : Fin (W + 1)), u) ∉ S X m y n U cp := by
      intro hx
      obtain ⟨-, r', hr', hid', hf', -⟩ := Finset.mem_filter.mp hx
      rw [hX.record_eq hr' hr (hid'.trans hit.symm)] at hf'
      exact hf hf'
    have huses := hle u hnot
    have hunits : unitsBefore log i ≤ u := by
      have h := MbarRing.Round.units_le_of_uses hch
        (fun z : _root_.Unit × Nat => it X m y n cp 0 z.2)
        (Finset.univ ×ˢ Finset.range u) (i := i)
        (fun k r c' tx hr _ ha => (o.arrive hr ha).1)
        (fun k _ r' c' tx hr' hf' ha' => by
          obtain ⟨t, hS, hid'⟩ := o.arrive_item hr' hf' ha'
          have htu : t ≠ u := fun h => hnot (h ▸ hS)
          exact ⟨((), t), Finset.mem_product.mpr ⟨Finset.mem_univ _,
            Finset.mem_range.mpr (by have := huses _ hS; simp only at this; omega)⟩, hid'⟩)
      simpa using h
    have hph := o.use_le hX hg ((0 : Fin (W + 1)), u) hi hit (.inl ⟨_, _, ha⟩) le_rfl hil hst
    simp only at hph
    have hacc := (hch.accounted hni hil).2 st hst
    rw [hexp] at hacc
    have hobs : st.observed = true := by
      refine hch.observed_of_poll hni hst ?_
      rcases Nat.eq_zero_or_pos u with h0 | hpos
      · exact .inl (by omega)
      · obtain ⟨kw, w, sw, hkw, hw, hww, hsw, h1⟩ :=
          hg ((0 : Fin (W + 1)), u) hi hit (.inl ⟨_, _, ha⟩) hpos
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
end PTX.MbarRing.TmaSized
