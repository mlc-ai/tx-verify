-- SPDX-License-Identifier: Apache-2.0
module

public import Core.MBarrier.AsyncMBarrier
public import Lemmas.Async.AsyncCopy

@[expose] public section

namespace PTX.AsyncCopy
noncomputable section

/-- Copy specifications are exactly the footprint of their issuing instruction. -/
theorem issuedBy_some {X : Execution} {i : EvId} {s : Spec} :
    issuedBy X i = some s ↔ X.Copy i s := by
  constructor
  · intro hs
    unfold issuedBy at hs
    cases he : X.get i with
    | none => simp [he] at hs
    | some ev =>
      obtain ⟨pc, kind⟩ := ev
      cases kind <;> simp only [he] at hs
      all_goals try contradiction
      case copy s' => cases hs; exact ⟨pc, he⟩
  · rintro ⟨pc, hi⟩
    simp [issuedBy, hi]

/-- An observed notification guarantees effects of the actual issuing copy, not a
standalone counter update or an effect borrowed from another copy. The copy has to write its
whole destination from memory with source and destination of one size: that is the form whose
completion notification determines the bytes it read and wrote (`CopyOk.completed`). -/
theorem AsyncObserved.completed {X : Execution} {c w : EvId} {acq : Bool} {ws : MbarScope}
    (ha : WellFormed (issuedBy X) X.async) (h : AsyncObserved X c (.notify .copy) w acq ws)
    (hform : ∀ s, issuedBy X c = some s → s.data = none ∧ s.writes = .whole ∧
      s.src.size = s.dst.size) :
    ∃ s bs, issuedBy X c = some s ∧ (X.async.copies c).readBytes = some bs ∧
      (X.async.copies c).writeBytes = some bs ∧ bs.length = s.dst.size := by
  obtain ⟨_, _, hn, -⟩ := h
  simp only [Notifies, Part.target, NotifyOn, Notification] at hn
  obtain ⟨-, -, s, hs, hnotified, -, -⟩ := hn
  obtain ⟨hd, hw, hsz⟩ := hform s hs
  have hp : nonempty (X.async.copies c) := ⟨.notify .copy, by simpa [present] using hnotified⟩
  obtain ⟨s', hs', hc⟩ := ha c hp
  rw [hs] at hs'; cases hs'
  obtain ⟨bs, hr, hw', hlen⟩ := hc.completed hnotified hd hw hsz
  exact ⟨s, bs, hs, hr, hw', hlen⟩

/-- No amount of object counter manipulation can replace this copy's notification. -/
theorem no_notification_not_observed {X : Execution} {c w : EvId} {acq : Bool} {ws : MbarScope}
    (h : ∀ m r, r ∈ X.objects m → r.id ≠ .async c (.notify .copy)) :
    ¬ AsyncObserved X c (.notify .copy) w acq ws := by
  rintro ⟨-, m, ⟨rfl, -⟩, -, i, j, r, s, p, hi, hr, _⟩
  exact h m r (List.mem_of_getElem? hi) hr

/-- An acquire observation is made by an acquire wait. -/
theorem WaitObserves.acquireWait {X : Execution} {x : Ref} {w : EvId} {m : Loc}
    {ws : MbarScope} (h : WaitObserves X x w m true ws) : X.AcquireWait w m := by
  obtain ⟨⟨pc, parity, hw⟩, -⟩ := h
  exact ⟨pc, parity, ws, hw⟩

/-- The observed notification is recorded before the wait in the object's history. -/
theorem WaitObserves.before {X : Execution} {x : Ref} {w : EvId} {m : Loc} {acq : Bool}
    {ws : MbarScope} (h : WaitObserves X x w m acq ws) :
    MBarrier.Before (X.objects m) x (.thread w) := by
  obtain ⟨-, i, j, r, s, -, hi, hr, -, hj, hs, -, -, hij, -⟩ := h
  exact ⟨i, j, r, s, hi, hr, hj, hs, hij⟩

/-- The copy case of an observation. -/
theorem AsyncObserved.copy {X : Execution} {i w : EvId} {acq : Bool} {ws : MbarScope}
    (h : AsyncObserved X i (.notify .copy) w acq ws) :
    ∃ m bytes, Notification (issuedBy X) X.async i m bytes ∧
      WaitObserves X (.async i (.notify .copy)) w m acq ws := by
  obtain ⟨n, m, ⟨rfl, bytes, hn⟩, hw⟩ := h
  exact ⟨m, bytes, hn, hw⟩

/-- The tensor case of an observation. -/
theorem AsyncObserved.tensor {X : Execution} {i w : EvId} {acq : Bool} {ws : MbarScope}
    (h : AsyncObserved X i (.notify .load) w acq ws) :
    ∃ o a, X.tensor i = some o ∧ X.TensorIssue i a o.spec ∧ o.effects.notified = true ∧
      WaitObserves X (.async i (.notify .load)) w o.spec.mbar acq ws := by
  obtain ⟨n, m, ⟨rfl, o, a, ho, hi, rfl, hn⟩, hw⟩ := h
  exact ⟨o, a, ho, hi, hn, hw⟩

/-- The CLC case of an observation. -/
theorem AsyncObserved.clc {X : Execution} {i w : EvId} {c : Nat} {acq : Bool}
    {ws : MbarScope} (h : AsyncObserved X i (.notify (.cta c)) w acq ws) :
    ∃ s targets, X.ClcIssue i s targets ∧ c ∈ targets ∧ c ∈ (X.clc i).notified ∧
      WaitObserves X (.async i (.notify (.cta c))) w { s.mbar with cta := c } acq ws := by
  obtain ⟨n, m, ⟨rfl, s, targets, hi, hc, hn, rfl⟩, hw⟩ := h
  exact ⟨s, targets, hi, hc, hn, hw⟩

/-- The MMA case of an observation. -/
theorem AsyncObserved.mma {X : Execution} {i w : EvId} {acq : Bool} {ws : MbarScope}
    (h : AsyncObserved X i .mmaDone w acq ws) :
    ∃ commit s rank m, TracksMma X i commit ∧ X.Commit commit s ∧
      TcCommit.target s rank = some m ∧ rank ∈ X.tcNotified commit ∧
      WaitObserves X (.async commit (.tcNotify rank)) w m acq ws := by
  obtain ⟨n, m, ⟨commit, s, rank, rfl, ht, hc, htg, hn⟩, hw⟩ := h
  exact ⟨commit, s, rank, m, ht, hc, htg, hn, hw⟩

end
end PTX.AsyncCopy
