-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.CpAsync
public import Lemmas.Protocol.ObservedSync
public import Lemmas.Protocol.ObjectSource

@[expose] public section

namespace PTX.MbarRing

open AsyncCopy MBarrier

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
  {X : Execution} {m : Loc}

/-- The provenance of a record on an mbarrier whose only counter updates are
`cp.async.mbarrier.arrive.noinc` arrive-ons. -/
inductive NoIncSource (X : Execution) (m : Loc) (r : Record Ref) : Prop where
  | init {count : Nat} (h : r.action = .init count)
  | poll {parity : Nat} {ok : Bool} (h : r.action = .pollParity parity ok)
  | arriveOn {i : EvId} (hid : r.id = .async i .arriveOn)
      (hi : X.AsyncArrive i m true) (harr : X.async.arrived i = true)
      (ha : r.action = .arrive 1 0)

/-- An initialized mbarrier with a fixed expected count and only ordinary no-increment
asynchronous arrivals. -/
structure NoIncObject (X : Execution) (m : Loc) (n : Nat) : Prop where
  source : ∀ r ∈ X.objects m, NoIncSource X m r
  init : PairTmaRing.InitFirst X m n

namespace NoIncObject

variable {n : Nat}

theorem noInval (o : NoIncObject X m n) : NoInval (X.objects m) := by
  intro r hr h
  cases o.source r hr with
  | init ha | poll ha | arriveOn _ _ _ ha => rw [h] at ha; cases ha

/-- Excluding other issue forms gives the source classification of the object's checked records. -/
theorem of_issues (hX : Consistent L K A mem0 X) (init : PairTmaRing.InitFirst X m n)
    (hinval : ∀ i, ¬ X.MbInval i m)
    (harr : ∀ i tx c rel sc, ¬ X.Arrive i m tx c rel sc)
    (hinc : ∀ i, ¬ X.AsyncArrive i m false)
    (hten : ∀ i addr sp, X.TensorIssue i addr sp → sp.mbar ≠ m)
    (hcopy : ∀ i s, X.Copy i s → s.completion ≠ .mbarrier m)
    (hcommit : ∀ i s rank, X.Commit i s → TcCommit.target s rank ≠ some m)
    (hclc : ∀ i sp targets c, X.ClcIssue i sp targets →
      m ≠ { sp.mbar with cta := c }) :
    NoIncObject X m n where
  init := init
  source r hr := by
    cases record_source hX.tma.2.2.1 hr with
    | init _ _ ha => exact .init ha
    | inval _ he _ => exact (hinval _ ⟨_, he⟩).elim
    | arrive _ he _ => exact (harr _ _ _ _ _ ⟨_, he⟩).elim
    | wait _ _ ha => exact .poll ha
    | increment _ he _ => exact (hinc _ ⟨_, he⟩).elim
    | tensor _ he hm _ => exact (hten _ _ _ ⟨_, he⟩ hm).elim
    | bulk _ he hm _ _ => exact (hcopy _ _ ⟨_, he⟩ hm).elim
    | commit _ he hm _ => exact (hcommit _ _ _ ⟨_, he⟩ hm).elim
    | clc _ he hm _ _ => exact (hclc _ _ _ _ ⟨_, he⟩ hm).elim
    | arriveOn hid he hm hn ha =>
      subst hm
      rename_i noinc
      cases noinc
      · exact (hinc _ ⟨_, he⟩).elim
      · exact .arriveOn hid ⟨_, he⟩ hn ha

/-- Every arrive action is the associated unit of an actual completed no-increment issue. -/
theorem arrive_source (o : NoIncObject X m n)
    {r : Record Ref} {i c tx : Nat} (hi : (X.objects m)[i]? = some r)
    (ha : r.action = .arrive c tx) :
    c = 1 ∧ tx = 0 ∧ ∃ j, r.id = .async j .arriveOn ∧ X.AsyncArrive j m true ∧
      X.async.arrived j = true := by
  cases o.source r (List.mem_of_getElem? hi) with
  | init h | poll h => rw [ha] at h; cases h
  | arriveOn h j hn ha' =>
    rw [ha] at ha'
    cases ha'
    exact ⟨rfl, rfl, _, h, j, hn⟩

theorem noIncrement (o : NoIncObject X m n) :
    incrementsBefore (X.objects m) (X.objects m).length = 0 :=
  incrementsBefore_length_of _ fun r hr hi => by
    cases o.source r hr with
    | init ha | poll ha | arriveOn _ _ _ ha => rw [hi] at ha; cases ha

open Classical in
/-- Each completed phase contains exactly the initialized count of arrive-on records. -/
theorem completed_count (hX : Consistent L K A mem0 X) (o : NoIncObject X m n)
    {j q : Nat} {s : State} (hj : j ≤ (X.objects m).length)
    (hs : stateBefore (X.objects m) j = some s) (hq : q < s.phase) :
    ((Finset.range (X.objects m).length).filter (UnitArrivalIn (X.objects m) q)).card = n :=
  (X.objects_checked hX m).card_unit_arrivals_phase o.noInval
    (fun _ _ _ _ hk _ ha => (o.arrive_source hk ha).1)
    (fun _ _ _ hstate => PairTmaRing.expected_of_init hX o.init o.noInval hstate)
    o.noIncrement hj hs hq

/-- A successful acquire poll sees the writes tracked by each no-increment arrive-on
from the phase it observes, provided the copy issuer and the waiter meet in scope. -/
theorem observes_copy (hX : Consistent L K A mem0 X) (o : NoIncObject X m n)
    {u v phase pc parity : Nat} {r poll : Record Ref} {copy i w : EvId} {sc : MbarScope}
    (hr : (X.objects m)[u]? = some r) (hclean : r.fault = none) (ha : r.action = .arrive 1 0)
    (hid : r.id = .async i .arriveOn) (hp : (X.objects m)[v]? = some poll)
    (hpid : poll.id = .thread w) (hsucc : poll.reply.waited = some true)
    (hphase : phaseAt (X.objects m) u = some phase) (hobs : observedAt (X.objects m) v = some phase)
    (hw : X.get w = some ⟨pc, .wait m parity true true sc⟩)
    (ht : TracksCpAsync X copy i) (hsc : ScopesMeet L .cluster copy.1 sc w.1) :
    AsyncFinished L X copy (.write .copy) w := by
  obtain ⟨_, _, j, hji, hj, harr⟩ := o.arrive_source hr ha
  have he : j = i := Ref.async.inj (hji.symm.trans hid) |>.1
  subst j
  have hcounter : CounterUpdate r.action := by rw [ha]; trivial
  have hob := Consistent.observed_of_phase hX o.noInval hr hclean hcounter hp hsucc hphase hobs
  rw [hid, hpid] at hob
  obtain ⟨_, w', m', acq, sc', he, ⟨⟨pc', parity', hget⟩, hbefore⟩, _⟩ := hob
  have hww := Ref.thread.inj he
  subst w'
  rw [hw] at hget
  cases hget
  exact asyncFinished_of_arriveOn ht hj harr ⟨⟨pc, parity, hw⟩, hbefore⟩ hsc

end NoIncObject

end

end PTX.MbarRing
