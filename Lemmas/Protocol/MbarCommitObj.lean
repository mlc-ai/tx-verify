-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.MbarRingBlocker
public import Lemmas.Protocol.MbarUnitTx
public import Lemmas.Protocol.ObjectSource
public import Lemmas.Protocol.PairTmaRing.ItemFacts

@[expose] public section

/-! # An object completed by Tensor Core commits alone

A proof tool for an mbarrier object of count 1 that only Tensor Core commits arrive on (FA4's
S-full and O-full objects: the MMA thread's commit, multicast to both CTAs of the pair). No thread
arrives on it and no tensor copy, linear copy, `cp.async.mbarrier.arrive` or cancellation request
completes on it, nothing invalidates
it, and its history starts with its only initialization (`PairTmaRing.InitFirst`, count 1).

Its history is a unit-transaction history without bytes (`commitObj_unitTx`: every fault-free
arrival is a commit's `arrive 1 0`, there are no completions, the expected count is 1). So when
it is blocked, its arrival units are its phase number (`commitObj_blocked`,
`MbarRing.Blocker.units_eq_phase`): its current phase awaits the next commit's notification. -/

namespace PTX.MbarRing.Blocker

open MBarrier AsyncCopy

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- An object that no `cp.async.mbarrier.arrive` names has no pending-count increment. -/
theorem noIncrement_of_no_cpAsyncArrive (hX : Consistent L K A mem0 X) {m : Loc}
    (hcpa : ∀ {i : EvId} {pc : Nat} {m' : Loc} {noinc : Bool},
      X.get i = some ⟨pc, .asyncArrive m' noinc⟩ → m' ≠ m) :
    incrementsBefore (X.objects m) (X.objects m).length = 0 :=
  incrementsBefore_length_of _ fun r hr hi => by
    cases record_source hX.tma.2.2.1 hr with
    | increment _ he _ => exact hcpa he rfl
    | init _ _ ha | inval _ _ ha | arrive _ _ ha | wait _ _ ha | tensor _ _ _ ha
    | commit _ _ _ ha | clc _ _ _ _ ha | arriveOn _ _ _ _ ha | bulk _ _ _ _ ha =>
      rw [hi] at ha; cases ha

/-- **An object completed by commits alone is a unit-transaction history without bytes.** -/
theorem commitObj_unitTx (hX : Consistent L K A mem0 X) {m : Loc}
    (hinit : PairTmaRing.InitFirst X m 1)
    (harr : ∀ {g i pc tx cnt : Nat} {rel : Bool} {sc : MbarScope},
      X.get (g, i) ≠ some ⟨pc, .arrive m tx cnt rel sc⟩)
    (hten : ∀ {i : EvId} {pc a : Nat} {sp : TensorCopy.Spec},
      X.get i = some ⟨pc, .tensorIssue a sp⟩ → sp.mbar ≠ m)
    (hcopy : ∀ {i : EvId} {pc : Nat} {s : AsyncCopy.Spec},
      X.get i = some ⟨pc, .copy s⟩ → s.completion ≠ .mbarrier m)
    (hcpa : ∀ {i : EvId} {pc : Nat} {m' : Loc} {noinc : Bool},
      X.get i = some ⟨pc, .asyncArrive m' noinc⟩ → m' ≠ m)
    (hclc : ∀ {i : EvId} {pc : Nat} {sp : Clc.Spec} {tg : List Nat},
      X.get i ≠ some ⟨pc, .clcIssue sp tg⟩)
    (hinv : ∀ {i : EvId} {pc : Nat} {m' : Loc}, X.get i ≠ some ⟨pc, .mbInval m'⟩) :
    UnitTx (X.objects m) 0 := by
  have hni : NoInval (X.objects m) := objects_noInval hX.tma.2.2.1 (fun _ _ ⟨_, he⟩ => hinv he) _
  refine ⟨fun r hr _ c tx ha => ?_, fun r hr _ n ha => ?_,
    fun _ _ hs => PairTmaRing.expected_of_init hX hinit hni hs⟩
  · cases record_source hX.tma.2.2.1 hr with
    | arrive _ he _ => exact (harr he).elim
    | commit _ _ _ ha' =>
      rw [ha] at ha'
      cases ha'
      exact ⟨rfl, rfl⟩
    | init _ _ ha' | inval _ _ ha' | wait _ _ ha' | tensor _ _ _ ha' | clc _ _ _ _ ha' =>
      rw [ha] at ha'
      cases ha'
    | bulk _ he hc _ _ => exact (hcopy he hc).elim
    | increment _ he _ => exact (hcpa he rfl).elim
    | arriveOn _ he hm _ _ => exact (hcpa he hm).elim
  · cases record_source hX.tma.2.2.1 hr with
    | tensor _ he hm _ => exact (hten he hm).elim
    | bulk _ he hc _ _ => exact (hcopy he hc).elim
    | increment _ he _ => exact (hcpa he rfl).elim
    | arriveOn _ he hm _ _ => exact (hcpa he hm).elim
    | clc _ he _ _ _ => exact (hclc he).elim
    | init _ _ ha' | inval _ _ ha' | arrive _ _ ha' | wait _ _ ha' | commit _ _ _ ha' =>
      rw [ha] at ha'
      cases ha'

/-- **A blocked object completed by commits alone awaits its next commit**: its arrival units
are its phase number. -/
theorem commitObj_blocked (hX : Consistent L K A mem0 X) {m : Loc}
    (hu : UnitTx (X.objects m) 0) {st : State}
    (hs : stateBefore (X.objects m) (X.objects m).length = some st)
    (hinv : ∀ {i : EvId} {pc : Nat} {m' : Loc}, X.get i ≠ some ⟨pc, .mbInval m'⟩)
    (hcpa : ∀ {i : EvId} {pc : Nat} {m' : Loc} {noinc : Bool},
      X.get i = some ⟨pc, .asyncArrive m' noinc⟩ → m' ≠ m) :
    arrivalUnits (X.objects m) = st.phase := by
  have hch := X.objects_checked hX m
  have hni : NoInval (X.objects m) := objects_noInval hX.tma.2.2.1 (fun _ _ ⟨_, he⟩ => hinv he) _
  have htx := hu.tx hch hni le_rfl hs
  simp only [Nat.zero_mul] at htx
  exact units_eq_phase hch hni hs htx (hu.expected _ _ hs)
    (noIncrement_of_no_cpAsyncArrive hX hcpa)

end PTX.MbarRing.Blocker
