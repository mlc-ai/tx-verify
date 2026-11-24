-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.CpAsync
public import Lemmas.Snoc.ObjectAppend

@[expose] public section

namespace PTX

open AsyncCopy MBarrier

noncomputable section

/-- Mark the separately performed stage of a `cp.async.mbarrier.arrive` instruction. -/
def Execution.markCpAsyncArrived (X : Execution) (i : EvId) : Execution :=
  { X with async := { X.async with arrived := fun j => if j = i then true else X.async.arrived j } }

/-- Perform one asynchronous arrive-on and append its record to the mbarrier history. -/
def Execution.finishCpAsyncArrive (X : Execution) (i : EvId) (m : Loc) (rec : Record Ref) :
    Execution :=
  (X.markCpAsyncArrived i).appendObject m rec

variable {X : Execution} {i : EvId} {m : Loc} {rec : Record Ref}

theorem Execution.le_finishCpAsyncArrive : X.le (X.finishCpAsyncArrive i m rec) := by
  apply Execution.le_trans ?_ (Execution.le_appendObject _ _ _)
  refine ⟨fun _ => List.prefix_refl _, fun _ _ _ => rfl, ?_, (X.le_refl).2.2.2⟩
  refine ⟨fun _ _ h => h, fun _ _ h => h, fun _ h => h, fun _ _ h => h,
    fun _ h => h, ?_, fun _ _ _ h => h, fun _ _ _ h => h⟩
  intro j hj
  simp [Execution.markCpAsyncArrived, hj]

theorem finishCpAsyncArrive_arriveOk (ho : ArriveOk X) (hi : X.AsyncArrive i m true)
    (hw : ∀ j, TracksCpAsync X j i → (X.async.copies j).writeBytes.isSome) :
    ArriveOk (X.finishCpAsyncArrive i m rec) := by
  intro j hj
  by_cases he : j = i
  · subst j
    exact ⟨⟨m, true, hi⟩, hw⟩
  · apply ho j
    simpa [Execution.finishCpAsyncArrive, Execution.markCpAsyncArrived,
        Execution.appendObject, he] using hj

theorem finishCpAsyncArrive_action_old {loc : Loc} {ref : Ref} (h : ref ≠ .async i .arriveOn) :
    objectAction (X.finishCpAsyncArrive i m rec) (X.finishCpAsyncArrive i m rec).async loc ref =
      objectAction X X.async loc ref := by
  cases ref with
  | thread j => rfl
  | async j p =>
    cases p <;> try rfl
    case arriveOn =>
      have hj : j ≠ i := fun e => h (congrArg (fun k => Ref.async k .arriveOn) e)
      simp only [objectAction, Execution.finishCpAsyncArrive, Execution.markCpAsyncArrived,
        Execution.appendObject,
        ite_eq_right hj]
      rfl

theorem finishCpAsyncArrive_action_new (hi : X.AsyncArrive i m true) (loc : Loc) :
    objectAction (X.finishCpAsyncArrive i m rec) (X.finishCpAsyncArrive i m rec).async loc
      (.async i .arriveOn) =
      if m = loc then some (.arrive 1 0) else none := by
  obtain ⟨pc, hp⟩ := hi
  change (match X.get i with
    | some ⟨_, .asyncArrive m' _⟩ =>
      if m' = loc ∧ (X.markCpAsyncArrived i).async.arrived i = true then
        some (MBarrier.Action.arrive 1 0) else none
    | _ => none) = _
  simp [hp, Execution.markCpAsyncArrived]

theorem no_arriveOn_record (ho : ObjectsOk X) (hn : X.async.arrived i = false)
    {loc : Loc} {r : Record Ref} (hr : r ∈ X.objects loc) : r.id ≠ .async i .arriveOn := by
  intro he
  have ha := ((ho loc).2.1 r hr).1
  rw [he] at ha
  change (match X.get i with
    | some ⟨_, .asyncArrive m' _⟩ =>
      if m' = loc ∧ X.async.arrived i = true then some (.arrive 1 0) else none
    | _ => none) = some r.action at ha
  split at ha <;> simp [hn] at ha

/-- A checked arrive-on extends only its issuing mbarrier's history. -/
theorem finishCpAsyncArrive_objects (ho : ObjectsOk X) (hi : X.AsyncArrive i m true)
    (hn : X.async.arrived i = false) (hid : rec.id = .async i .arriveOn)
    (ha : rec.action = .arrive 1 0) (hc : CheckedLog (X.objects m ++ [rec])) :
    ObjectsOk (X.finishCpAsyncArrive i m rec) := by
  intro loc
  by_cases hm : loc = m
  · subst loc
    refine ⟨?_, ?_, ?_⟩
    · simpa [Execution.finishCpAsyncArrive, Execution.markCpAsyncArrived, Execution.appendObject]
        using hc
    · intro r hr
      have hr' : r ∈ X.objects m ++ [rec] := by
        simpa [Execution.finishCpAsyncArrive, Execution.markCpAsyncArrived, Execution.appendObject]
          using hr
      rcases List.mem_append.mp hr' with hold | hnew
      · obtain ⟨ha', hp⟩ := (ho m).2.1 r hold
        exact ⟨(finishCpAsyncArrive_action_old (no_arriveOn_record ho hn hold)).trans ha', hp⟩
      · obtain rfl := List.mem_singleton.mp hnew
        refine ⟨?_, ?_⟩
        · rw [hid, ha, finishCpAsyncArrive_action_new hi, ite_eq_left rfl]
        · intro p ok hp
          rw [ha] at hp
          cases hp
    · intro id act hact
      by_cases he : id = .async i .arriveOn
      · exact ⟨rec, by simp [Execution.finishCpAsyncArrive, Execution.appendObject],
          hid.trans he.symm⟩
      · rw [finishCpAsyncArrive_action_old he] at hact
        obtain ⟨r, hr, hrid⟩ := (ho m).2.2 id act hact
        exact ⟨r, by simp [Execution.finishCpAsyncArrive, Execution.markCpAsyncArrived,
        Execution.appendObject, hr], hrid⟩
  · have hlog : (X.finishCpAsyncArrive i m rec).objects loc = X.objects loc := by
      simp [Execution.finishCpAsyncArrive, Execution.markCpAsyncArrived,
        Execution.appendObject, hm]
    refine ⟨by rw [hlog]; exact (ho loc).1, ?_, ?_⟩
    · intro r hr
      rw [hlog] at hr
      obtain ⟨ha', hp⟩ := (ho loc).2.1 r hr
      exact ⟨(finishCpAsyncArrive_action_old (no_arriveOn_record ho hn hr)).trans ha', hp⟩
    · intro id act hact
      by_cases he : id = .async i .arriveOn
      · subst id
        rw [finishCpAsyncArrive_action_new hi, ite_eq_right (Ne.symm hm)] at hact
        cases hact
      · rw [finishCpAsyncArrive_action_old he] at hact
        obtain ⟨r, hr, hrid⟩ := (ho loc).2.2 id act hact
        exact ⟨r, hlog ▸ hr, hrid⟩

/-- The new arrival and its checked object record preserve the asynchronous effect invariants. -/
theorem finishCpAsyncArrive_tmaOk (ho : TmaOk X) (hi : X.AsyncArrive i m true)
    (hn : X.async.arrived i = false)
    (hw : ∀ j, TracksCpAsync X j i → (X.async.copies j).writeBytes.isSome)
    (hid : rec.id = .async i .arriveOn) (ha : rec.action = .arrive 1 0)
    (hc : CheckedLog (X.objects m ++ [rec])) :
    TmaOk (X.finishCpAsyncArrive i m rec) :=
  ⟨ho.1, ho.2.1, finishCpAsyncArrive_objects ho.2.2.1 hi hn hid ha hc,
    finishCpAsyncArrive_arriveOk ho.2.2.2 hi hw⟩

end

end PTX
