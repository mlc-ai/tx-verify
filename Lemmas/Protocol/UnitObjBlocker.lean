-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.UnitObject
public import Lemmas.Protocol.MbarRingBlocker
public import Lemmas.Protocol.MbarUnitTx
public import Lemmas.Order.CausalObjectWaitCount

@[expose] public section

/-! # Who blocks a unit object

A proof tool for the progress of a unit object (`MbarRing.Unit.Obj`: `N` producers, one release
arrival without bytes per use, count `N`; FA4's P-ready objects). Producer `a`'s recorded arrivals
are the fault-free arrival records of its thread (`unitRec`). Their sum over the producers is at
most the history's arrival units (`sum_count_le_units`: each such record is one unit, and is of
one producer). A blocked object has no outstanding transaction bytes and its expected count is
`N`, so some producer has recorded no more arrivals than the object's phase number
(`Obj.blocked`, by pigeonhole, `MbarRing.Blocker.exists_short`). -/

namespace PTX.MbarRing.Unit

open AsyncCopy MBarrier

/-- Record `r` is a fault-free arrival of thread `g`. -/
def unitRec (g : Nat) (r : Record Ref) : Bool :=
  objectThreadSelected g r.id && r.fault.isNone &&
    (match r.action with | .arrive .. => true | _ => false)

/-- **The producers' recorded arrivals are at most the history's arrival units.** -/
theorem sum_count_le_units {N : Nat} {prod : Fin N → Nat} (hinj : Function.Injective prod) :
    ∀ log : List (Record Ref),
      (∀ r ∈ log, r.fault = none → ∀ c tx, r.action = .arrive c tx → c = 1) →
      ∑ a, log.countP (unitRec (prod a)) ≤ arrivalUnits log
  | [], _ => by simp
  | r :: rest, h => by
    have ih := sum_count_le_units hinj rest (fun r hr => h r (List.mem_cons_of_mem _ hr))
    simp only [List.countP_cons, Finset.sum_add_distrib]
    have hle : ∑ a : Fin N, (if unitRec (prod a) r = true then 1 else 0) ≤
        (match r.action, r.fault with | .arrive n _, none => n | _, _ => 0) := by
      rw [Finset.sum_boole]
      by_cases hex : ∃ a, unitRec (prod a) r = true
      · obtain ⟨a0, ha0⟩ := hex
        simp only [unitRec, Bool.and_eq_true, Option.isNone_iff_eq_none] at ha0
        obtain ⟨⟨hsel, hf⟩, hact⟩ := ha0
        obtain ⟨c, tx, hac⟩ : ∃ c tx, r.action = .arrive c tx := by
          revert hact
          cases r.action <;> simp
        have hc := h r List.mem_cons_self hf c tx hac
        rw [hac, hf, hc]
        refine Finset.card_le_one.mpr fun a ha b hb => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, unitRec, Bool.and_eq_true] at ha hb
        obtain ⟨j, hj⟩ := objectThreadSelected_iff.mp ha.1.1
        obtain ⟨j', hj'⟩ := objectThreadSelected_iff.mp hb.1.1
        rw [hj] at hj'
        exact hinj (congrArg (fun e : EvId => e.1) (Ref.thread.inj hj'))
      · push Not at hex
        have : (Finset.univ.filter fun a => unitRec (prod a) r = true) = ∅ :=
          Finset.filter_false_of_mem fun a _ => by simp [hex a]
        rw [this]
        simp
    have hu : arrivalUnits (r :: rest) =
        (match r.action, r.fault with | .arrive n _, none => n | _, _ => 0) +
          arrivalUnits rest := rfl
    omega

namespace Obj

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}
  {m : Loc} {N δ : Nat} {prod : Fin N → Nat}

/-- **A blocked unit object has a short producer**: some producer's recorded arrivals are no
more than the object's phase number. -/
theorem blocked (hX : Consistent L K A mem0 X) (O : Obj X m N prod δ) {st : State}
    (hs : stateBefore (X.objects m) (X.objects m).length = some st) :
    ∃ a, (X.objects m).countP (unitRec (prod a)) ≤ st.phase := by
  have hch := X.objects_checked hX m
  have hunit : ∀ r ∈ X.objects m, r.fault = none → ∀ c tx, r.action = .arrive c tx →
      c = 1 ∧ tx = 0 := by
    intro r hr _ c tx ha
    cases O.src r hr with
    | init ha' | poll _ _ ha' => rw [ha] at ha'; cases ha'
    | arrive _ _ _ ha' => rw [ha] at ha'; cases ha'; exact ⟨rfl, rfl⟩
  have hnc : UniformCompletedTx ((X.objects m).take (X.objects m).length) 0 := by
    intro r hr _ n ha
    cases O.src r (List.mem_of_mem_take hr) with
    | init ha' | poll _ _ ha' | arrive _ _ _ ha' => rw [ha] at ha'; cases ha'
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
    (fun a => (X.objects m).countP (unitRec (prod a))) hexp (by
      simpa using sum_count_le_units O.inj (X.objects m) fun r hr hf c tx ha =>
        (hunit r hr hf c tx ha).1) O.noIncrement
  exact ⟨a, ha⟩

end Obj
end PTX.MbarRing.Unit
