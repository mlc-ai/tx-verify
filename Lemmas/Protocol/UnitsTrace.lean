-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.UnitBlocker
public import Lemmas.Order.CausalThreadCount
public import Lemmas.Async.AsyncOrigins

@[expose] public section

/-! # A thread's counted arrivals on an object are its arrivals in its trace

A proof tool. In a consistent execution, every record of an object with a thread's identity is of
an event in that thread's trace, and every arrival event on the object has its record
(`Consistent.object_thread_arrival_count_window`). When no record of the object's history faults,
the thread's counted arrival records there (`MbarRing.Unit.unitsOf`) are exactly its arrival
events on the object (`unitsOf_eq_arrivals`). -/

namespace PTX.MbarRing.Unit

open AsyncCopy MBarrier

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0} {X : Execution}

/-- **Counted arrival records are trace arrivals.** In a consistent execution whose history of
`m` has no faulting record, thread `g`'s counted arrival records on `m` are its arrival events on
`m`. -/
theorem unitsOf_eq_arrivals (hX : Consistent L K A mem0 X) {m : Loc}
    (hf : ∀ r ∈ X.objects m, r.fault = none) (g : Nat) :
    (X.objects m).countP (unitsOf g) = Flow.arrivals m (X.tr g) := by
  have hcongr : (X.objects m).countP (unitsOf g) = (X.objects m).countP (threadArrival g) := by
    refine List.countP_congr fun r hr => ?_
    simp only [unitsOf, Bool.and_eq_true, threadArrival_iff, countedArrive_iff, hf r hr,
      true_and]
    exact and_comm
  have hwin : ∀ q j, q ∈ X.objects m → q.id = .thread (g, j) →
      (q ∈ X.objects m ↔ j < (X.tr g).length) := by
    intro q j hq hid
    refine ⟨fun _ => ?_, fun _ => hq⟩
    have ha := ((hX.tma.2.2.1 m).2.1 q hq).1
    rw [hid] at ha
    obtain ⟨ev, hev⟩ := objectAction_present ha
    exact (List.getElem?_eq_some_iff.mp hev).1
  rw [hcongr, hX.object_thread_arrival_count_window (X.objects m) (fun _ hq => hq)
    (hX.tma.2.2.1 m).1.1 hwin, List.take_length]
  rfl

end PTX.MbarRing.Unit
