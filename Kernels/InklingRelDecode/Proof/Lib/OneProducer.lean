-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.UnitReachBlocker
public import Lemmas.Protocol.UnitsTrace

@[expose] public section
namespace PTX.Kernels.InklingRelDecode.Proof.Lib
open PTX PTX.Flow PTX.MBarrier PTX.MbarRing

/-- A single producer's arrival events cover every completed phase. This needs
only its unit-object history and fault-free records, independently of its consumers. -/
theorem unit_phase_le {K A L m X l g δ st} (hX : Consistent L K A m X)
    (o : Unit.Obj X l 1 (fun _ => g) δ) (free : ∀ r ∈ X.objects l, r.fault=none)
    (hs : stateBefore (X.objects l) (X.objects l).length=some st) :
    st.phase≤arrivals l (X.tr g) := by
  have units : arrivalUnits (X.objects l) = (X.objects l).countP (Unit.unitsOf g) := by
    rw [arrivalUnits_eq_length (fun r hr c tx _ ha =>
      (o.arrive_rec (List.mem_iff_getElem?.mp hr).choose_spec ha).1),
      ←List.countP_eq_length_filter]
    apply List.countP_congr
    intro r hr
    by_cases counted : countedArrive r=true
    · obtain ⟨_,c,tx,act⟩ := countedArrive_iff.mp counted
      obtain ⟨_,_,_,j,_,_,id,_⟩ := o.arrive_rec (List.mem_iff_getElem?.mp hr).choose_spec act
      simp only [Unit.unitsOf,counted,objectThreadSelected_iff.mpr ⟨j,id⟩,Bool.true_and]
    · simp [Unit.unitsOf,Bool.eq_false_iff.mpr counted]
  have ⟨pending,account⟩ := ((X.objects_checked hX l).accounted o.noInval le_rfl).2 st hs
  rw [PairTmaRing.expected_of_init hX o.init o.noInval hs] at pending account
  rw [unitsBefore,List.take_length,units,Unit.unitsOf_eq_arrivals hX free] at account
  omega

end PTX.Kernels.InklingRelDecode.Proof.Lib
