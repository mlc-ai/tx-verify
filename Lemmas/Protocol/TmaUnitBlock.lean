-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.TmaUnit
public import Lemmas.Protocol.MbarRingBlocker
public import Lemmas.Protocol.PairTmaRing.ItemFacts
public import Lemmas.Protocol.PairTmaRing.Blocker
public import Lemmas.Kernel.Obligation

@[expose] public section

/-! # When a one-CTA TMA unit object is blocked

The library's `MbarRing.TmaUnitObject` (`Lemmas/Protocol/TmaUnit.lean`) with the facts the
progress argument uses (a proof tool, promoted from tml-fa4's `Proof2/Lib/TmaUnitBlock.lean`):

* no record is a pending-count increment (`noIncrement`); with no outstanding transaction bytes
  the arrival units are at most the phase number (`blocked`);
* a thread's arrivals on a fault-free object are at most its arrival units
  (`arrivals_le_units`); with no open tensor-copy obligation, every copy completing on the object
  has a notification record (`notified_rec`), so a thread's copies on it are at most its completed
  transactions (`issues_le_completions`);
* **the final phase is short** (`short`, by `MbarRing.Blocker.tx_short`): when each arrival
  expects `n` copies of `B` bytes and the completions do not run ahead of the phase, the final
  phase awaits its arrival, or it has fewer than `n` completed copies per phase reached. -/

namespace PTX.MbarRing

open AsyncCopy MBarrier

noncomputable section

variable {L : Launch} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
  {X : Execution} {m : Loc}

namespace TmaUnitObject

/-- No record of such an object is a pending-count increment. -/
theorem noIncrement {prod : Nat → Prop} (o : TmaUnitObject X m prod) :
    incrementsBefore (X.objects m) (X.objects m).length = 0 :=
  incrementsBefore_length_of _ fun r hr hi => by
    cases o.source r hr with
    | init ha | poll ha | arrive _ _ _ ha | tensor _ _ _ ha => rw [hi] at ha; cases ha

/-- **A blocked one-CTA TMA unit object**: when its transaction counter is zero, its arrival
units are at most its phase number (the phase's arrival is missing). -/
theorem blocked {prod : Nat → Prop} (hX : Consistent L K A mem0 X) (o : TmaUnitObject X m prod)
    {st : State} (hs : stateBefore (X.objects m) (X.objects m).length = some st)
    (htx : st.tx = 0) : arrivalUnits (X.objects m) ≤ st.phase := by
  have hlt := Blocker.units_lt (X.objects_checked hX m) o.noInval hs htx o.noIncrement
  rw [PairTmaRing.expected_of_init hX o.init o.noInval hs] at hlt
  omega

/-- **A thread's arrivals on a fault-free one-CTA TMA unit object are at most its arrival
units.** -/
theorem arrivals_le_units {prod : Nat → Prop} (hX : Consistent L K A mem0 X)
    (o : TmaUnitObject X m prod) (hff : ∀ r ∈ X.objects m, r.fault = none) (h : Nat) :
    Flow.arrivals m (X.tr h) ≤ arrivalUnits (X.objects m) := by
  classical
  rw [arrivalUnits_eq_length (fun r hr c' tx _ ha => by
      cases o.source r hr with
      | init h | poll h | tensor _ _ _ h => rw [ha] at h; cases h
      | arrive _ _ _ h => rw [ha] at h; cases h; rfl),
    ← List.countP_eq_length_filter]
  unfold Flow.arrivals
  refine countP_le_of_records (fun j => Ref.thread (h, j))
    (fun i j _ _ hf => by simpa using hf) (fun i hi => ?_)
  obtain ⟨⟨pc, kind⟩, he, hp⟩ := (mem_indicesP_iff _ _ i).mp hi
  cases kind with
  | arrive m' tx cnt rel sc =>
    have hm : m' = m := by simpa [Flow.arrivesOn, sourceArrive] using hp
    subst hm
    have hget : X.get (h, i) = some ⟨pc, .arrive m' tx cnt rel sc⟩ := he
    have hact : objectAction X X.async m' (Ref.thread (h, i)) = some (.arrive cnt tx) := by
      simp [objectAction, hget]
    obtain ⟨r, hr, hid⟩ := (hX.tma.2.2.1 m').2.2 (Ref.thread (h, i)) _ hact
    have hact' := ((hX.tma.2.2.1 m').2.1 r hr).1
    rw [hid, hact] at hact'
    exact ⟨r, hr, hid, countedArrive_iff.mpr ⟨hff r hr, cnt, tx,
      (Option.some.inj hact').symm⟩⟩
  | _ => simp [Flow.arrivesOn, sourceArrive] at hp

/-- **With no open tensor-copy obligation, a copy completing on an object has a notification
record there.** -/
theorem notified_rec (hX : Consistent L K A mem0 X) (hno : ¬ Descent.Obl L X .tensor) :
    ∀ i ma s, X.TensorIssue i ma s → s.mbar = m →
      ∃ r ∈ X.objects m, r.id = .async i (.notify .load) := by
  intro i ma s hT hmb
  simp only [Descent.Obl, not_not] at hno
  by_contra hnr
  push Not at hnr
  exact PairTmaRing.unnotified hX hT hmb hnr (hno i ma s hT)

/-- **A thread's copies on a fault-free one-CTA TMA unit object are at most its completed
transactions**, when every such copy has a notification record. -/
theorem issues_le_completions {prod : Nat → Prop} (hX : Consistent L K A mem0 X)
    (hff : ∀ r ∈ X.objects m, r.fault = none) (h : Nat)
    (hM : ∀ i ma s, X.TensorIssue i ma s → s.mbar = m →
      ∃ r ∈ X.objects m, r.id = .async i (.notify .load)) (_o : TmaUnitObject X m prod) :
    (X.tr h).countP (Flow.issuesTo m) ≤ completedTxCount (X.objects m) := by
  classical
  unfold completedTxCount
  refine countP_le_of_records (fun k => Ref.async (h, k) (Part.notify .load))
    (fun i j _ _ hf => by simpa using hf) (fun i hi => ?_)
  obtain ⟨⟨pc, kind⟩, he, hp⟩ := (mem_indicesP_iff _ _ i).mp hi
  cases kind with
  | tensorIssue ma s =>
    have hmb : s.mbar = m := by simpa [Flow.issuesTo] using hp
    obtain ⟨r, hr, hid⟩ := hM (h, i) ma s ⟨pc, he⟩ hmb
    have hact := ((hX.tma.2.2.1 m).2.1 r hr).1
    rw [hid] at hact
    obtain ⟨n, hn⟩ := PairTmaRing.action_completeTx hact
    refine ⟨r, hr, hid, ?_⟩
    rw [hn, hff r hr]
  | _ => simp [Flow.issuesTo] at hp

/-- **The final phase of a one-CTA TMA unit object is short**: when every arrival expects `n`
copies of `B` bytes and the completions do not run ahead of the phase, the final phase awaits its
arrival (the arrival units are the phase number), or it has fewer than `n` completed copies per
phase reached. -/
theorem short {prod : Nat → Prop} (hX : Consistent L K A mem0 X) (o : TmaUnitObject X m prod)
    {st : State} (hs : stateBefore (X.objects m) (X.objects m).length = some st) {n B : Nat}
    (hbytes : expectedTxBytes (X.objects m) = n * B * arrivalUnits (X.objects m))
    (hu : UniformCompletedTx (X.objects m) B)
    (hle : completedTxCount (X.objects m) ≤ n * (st.phase + 1)) :
    arrivalUnits (X.objects m) = st.phase ∨
      (arrivalUnits (X.objects m) = st.phase + 1 ∧
        completedTxCount (X.objects m) < n * (st.phase + 1)) :=
  Blocker.tx_short (X.objects_checked hX m) o.noInval hs
    (PairTmaRing.expected_of_init hX o.init o.noInval hs) hbytes hu hle o.noIncrement

end TmaUnitObject

end
end PTX.MbarRing
