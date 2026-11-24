-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.UnitObjBlocker
public import Lemmas.Protocol.CpAsyncPhase
public import Lemmas.Protocol.NoIncRing
public import Lemmas.Kernel.Obligation
public import Lemmas.Protocol.RecordCount

@[expose] public section

/-! # Who blocks an object of no-increment arrive-ons

The counterpart of `MbarRing.Unit.Obj.blocked` for an object whose counter updates are the
arrive-ons of `cp.async.mbarrier.arrive.noinc` (`MbarRing.NoIncObject`): an arrive-on record is
labeled by its issuing thread (`onRec`); the producers' records sum to at most the history's
arrival units (`sum_onRec_le_units`); a blocked object has no outstanding transaction bytes and
its expected count is the number of producers, so some producer has no more recorded arrive-ons
than the object's phase number (`NoIncObject.blocked`). With no open arrive-on obligation, a
thread's no-increment arrive-ons on a fault-free object are recorded as its arrivals
(`arr_recorded`). A proof tool, promoted from tml-fa4's `Proof2/Lib/NoIncBlocker.lean`. -/

namespace PTX.MbarRing

open AsyncCopy MBarrier

/-- Record `r` is a fault-free arrival issued by thread `g`. -/
def onRec (g : Nat) (r : Record Ref) : Bool :=
  decide (r.id.issuer.1 = g) && r.fault.isNone &&
    (match r.action with | .arrive .. => true | _ => false)

/-- **The producers' recorded arrive-ons are at most the history's arrival units.** -/
theorem sum_onRec_le_units {N : Nat} {prod : Fin N → Nat} (hinj : Function.Injective prod) :
    ∀ log : List (Record Ref),
      (∀ r ∈ log, r.fault = none → ∀ c tx, r.action = .arrive c tx → c = 1) →
      ∑ a, log.countP (onRec (prod a)) ≤ arrivalUnits log
  | [], _ => by simp
  | r :: rest, h => by
    have ih := sum_onRec_le_units hinj rest (fun r hr => h r (List.mem_cons_of_mem _ hr))
    simp only [List.countP_cons, Finset.sum_add_distrib]
    have hle : ∑ a : Fin N, (if onRec (prod a) r = true then 1 else 0) ≤
        (match r.action, r.fault with | .arrive n _, none => n | _, _ => 0) := by
      rw [Finset.sum_boole]
      by_cases hex : ∃ a, onRec (prod a) r = true
      · obtain ⟨a0, ha0⟩ := hex
        simp only [onRec, Bool.and_eq_true, Option.isNone_iff_eq_none, decide_eq_true_eq] at ha0
        obtain ⟨⟨-, hf⟩, hact⟩ := ha0
        obtain ⟨c, tx, hac⟩ : ∃ c tx, r.action = .arrive c tx := by
          revert hact
          cases r.action <;> simp
        have hc := h r List.mem_cons_self hf c tx hac
        rw [hac, hf, hc]
        refine Finset.card_le_one.mpr fun a ha b hb => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, onRec, Bool.and_eq_true,
          decide_eq_true_eq] at ha hb
        exact hinj (ha.1.1.symm.trans hb.1.1)
      · push Not at hex
        have : (Finset.univ.filter fun a => onRec (prod a) r = true) = ∅ :=
          Finset.filter_false_of_mem fun a _ => by simp [hex a]
        rw [this]
        simp
    have hu : arrivalUnits (r :: rest) =
        (match r.action, r.fault with | .arrive n _, none => n | _, _ => 0) +
          arrivalUnits rest := rfl
    omega

namespace NoIncObject

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {m : Loc} {N : Nat}

/-- **A blocked object of no-increment arrive-ons has a short producer**: with `N` producers
(the expected count), some producer's recorded arrive-ons are no more than the object's phase
number. -/
theorem blocked (hX : Consistent L K A mem0 X) (O : NoIncObject X m N) {prod : Fin N → Nat}
    (hinj : Function.Injective prod) {st : State}
    (hs : stateBefore (X.objects m) (X.objects m).length = some st) :
    ∃ a, (X.objects m).countP (onRec (prod a)) ≤ st.phase := by
  have hch := X.objects_checked hX m
  have hunit : ∀ r ∈ X.objects m, r.fault = none → ∀ c tx, r.action = .arrive c tx →
      c = 1 ∧ tx = 0 := by
    intro r hr _ c tx ha
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hr
    obtain ⟨h1, h2, -⟩ := O.arrive_source hk ha
    exact ⟨h1, h2⟩
  have hnc : UniformCompletedTx ((X.objects m).take (X.objects m).length) 0 := by
    intro r hr _ n ha
    cases O.source r (List.mem_of_mem_take hr) with
    | init ha' | poll ha' | arriveOn _ _ _ ha' => rw [ha] at ha'; cases ha'
  have htx : st.tx = 0 := by
    have hb := hch.tx_balance O.noInval le_rfl hs
    rw [expectedTxBytes_unit (T := 0) (fun r hr hf c tx ha =>
      hunit r (List.mem_of_mem_take hr) hf c tx ha), completedTxBytes_eq_unit_mul_count hnc] at hb
    simp only [Nat.zero_mul, Nat.cast_zero, sub_zero] at hb
    exact_mod_cast hb
  have hexp : st.expected = ∑ _a : Fin N, 1 := by
    rw [PairTmaRing.expected_of_init hX O.init O.noInval hs]
    simp
  obtain ⟨a, -, ha⟩ := Blocker.exists_short hch O.noInval hs htx (fun _ => 1)
    (fun a => (X.objects m).countP (onRec (prod a))) hexp (by
      simpa using sum_onRec_le_units hinj (X.objects m) fun r hr hf c tx ha =>
        (hunit r hr hf c tx ha).1) O.noIncrement
  exact ⟨a, ha⟩

end NoIncObject

open Flow in
/-- **With no open arrive-on, a thread's arrive-ons are recorded**, as fault-free arrivals of the
thread in the object's history. -/
theorem arr_recorded {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
    {X : Execution} (hX : Consistent L K A mem0 X) (hno : ¬ Descent.Obl L X .arriveOn) {F : Loc}
    (hfree : ∀ r ∈ X.objects F, r.fault = none) (y : Nat) :
    (X.tr y).countP (arriveOnTo F) ≤ (X.objects F).countP (onRec y) := by
  classical
  simp only [Descent.Obl, not_not] at hno
  refine MBarrier.countP_le_of_records (fun j => Ref.async (y, j) .arriveOn)
    (fun i j _ _ h => by simpa using h) (fun i hi => ?_)
  obtain ⟨⟨pc, kind⟩, he, hp⟩ := (MBarrier.mem_indicesP_iff _ _ i).mp hi
  cases kind with
  | asyncArrive l ni =>
    cases ni <;> simp [arriveOnTo] at hp
    subst hp
    have hget : X.get (y, i) = some ⟨pc, .asyncArrive l true⟩ := he
    have harr := hno (y, i) l true ⟨pc, hget⟩
    have hact : objectAction X X.async l (Ref.async (y, i) .arriveOn) = some (.arrive 1 0) := by
      simp [objectAction, hget, harr]
    obtain ⟨r, hr, hid⟩ := (hX.tma.2.2.1 l).2.2 _ _ hact
    have hact' := ((hX.tma.2.2.1 l).2.1 r hr).1
    rw [hid, hact] at hact'
    refine ⟨r, hr, hid, ?_⟩
    simp only [onRec, hid, Ref.issuer, hfree r hr, Option.isNone_none, Bool.and_true,
      decide_true, Bool.true_and]
    rw [← Option.some.inj hact']
  | _ => simp [arriveOnTo] at hp

end PTX.MbarRing
