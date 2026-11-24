-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Async.AsyncExecution
public import Lemmas.Snoc.ObjectAppend

@[expose] public section

/-! Notifying a completed tcgen05 commit and recording its arrival in a checked object history.
The object transition is a proof obligation, not an assumed phase or counter update. -/
namespace PTX
open AsyncCopy MBarrier
noncomputable section

/-- Deliver commit `i`'s notification to target rank `rank`. -/
def Execution.notifyTc (X : Execution) (i : EvId) (rank : Fin 16) : Execution :=
  { X with tcNotified := fun j => if j = i then insert rank (X.tcNotified j) else X.tcNotified j }

def Execution.notifyTcRecord (X : Execution) (i : EvId) (rank : Fin 16)
    (mb : Loc) (rec : Record Ref) : Execution :=
  (X.notifyTc i rank).appendObject mb rec

variable {X : Execution} {i : EvId} {rank : Fin 16} {mb : Loc} {rec : Record Ref}

theorem notifyTcRecord_action_old {loc : Loc} {id : Ref} (hid : id ≠ .async i (.tcNotify rank)) :
    objectAction (X.notifyTcRecord i rank mb rec)
      (X.notifyTcRecord i rank mb rec).async loc id = objectAction X X.async loc id := by
  cases id with
  | thread j => rfl
  | async j p =>
    cases p <;> try rfl
    rename_i r
    simp only [objectAction, Execution.notifyTcRecord, Execution.appendObject, Execution.notifyTc]
    by_cases hj : j = i
    · subst hj
      have hr : r ≠ rank := fun h => hid (by rw [h])
      simp [Finset.mem_insert, hr]
      rfl
    · simp [hj]
      rfl

theorem notifyTcRecord_action_notify {s : TcCommit.Spec} (hi : X.Commit i s) (loc : Loc) :
    objectAction (X.notifyTcRecord i rank mb rec)
      (X.notifyTcRecord i rank mb rec).async loc (.async i (.tcNotify rank)) =
      if TcCommit.target s rank = some loc then some (.arrive 1 0) else none := by
  obtain ⟨pc, hi⟩ := hi
  simp only [objectAction, Execution.notifyTcRecord, Execution.appendObject,
    Execution.notifyTc, Execution.get] at *
  rw [hi]
  simp

theorem no_tc_notification_record (ho : ObjectsOk X) (hn : rank ∉ X.tcNotified i)
    {loc : Loc} {r : Record Ref} (hr : r ∈ X.objects loc) :
    r.id ≠ .async i (.tcNotify rank) := by
  intro heq
  have ha := ((ho loc).2.1 r hr).1
  rw [heq] at ha
  cases hi : X.get i with
  | none => simp [objectAction, hi] at ha
  | some ev =>
    cases ev with
    | mk pc kind =>
      cases kind <;> simp only [objectAction, hi] at ha
      all_goals try contradiction
      case tc op => cases op <;> simp [hn] at ha

/-- Provenance and coverage survive the completion. The checked transition explicitly
belongs to the supplied mbarrier; no notification can be redirected to another object. -/
theorem notifyTcRecord_objects (ho : ObjectsOk X) {s : TcCommit.Spec}
    (hi : X.Commit i s) (hmb : TcCommit.target s rank = some mb)
    (hn : rank ∉ X.tcNotified i)
    (hid : rec.id = .async i (.tcNotify rank)) (ha : rec.action = .arrive 1 0)
    (hc : CheckedLog (X.objects mb ++ [rec])) :
    ObjectsOk (X.notifyTcRecord i rank mb rec) := by
  intro loc
  by_cases hm : loc = mb
  · subst loc
    refine ⟨by simpa [Execution.notifyTcRecord, Execution.appendObject, Execution.notifyTc]
      using hc, ?_, ?_⟩
    · intro r hr
      have hr' : r ∈ X.objects mb ++ [rec] := by
        simpa [Execution.notifyTcRecord, Execution.appendObject, Execution.notifyTc] using hr
      rcases List.mem_append.mp hr' with hold | hnew
      · obtain ⟨ha', hp⟩ := (ho mb).2.1 r hold
        refine ⟨?_, hp⟩
        rw [notifyTcRecord_action_old (no_tc_notification_record ho hn hold)]
        exact ha'
      · have he := List.mem_singleton.mp hnew
        subst r
        refine ⟨?_, ?_⟩
        · rw [hid, notifyTcRecord_action_notify hi, ite_eq_left hmb, ha]
        · intro p ok hp; rw [ha] at hp; cases hp
    · intro id act hact
      by_cases he : id = .async i (.tcNotify rank)
      · exact ⟨rec, by simp [Execution.notifyTcRecord, Execution.appendObject,
          Execution.notifyTc], hid.trans he.symm⟩
      · rw [notifyTcRecord_action_old he] at hact
        obtain ⟨r, hr, hrid⟩ := (ho mb).2.2 id act hact
        exact ⟨r, by simp [Execution.notifyTcRecord, Execution.appendObject,
          Execution.notifyTc, hr], hrid⟩
  · have hlog : (X.notifyTcRecord i rank mb rec).objects loc = X.objects loc := by
      simp [Execution.notifyTcRecord, Execution.appendObject, Execution.notifyTc, hm]
    refine ⟨by rw [hlog]; exact (ho loc).1, ?_, ?_⟩
    · intro r hr
      rw [hlog] at hr
      obtain ⟨ha', hp⟩ := (ho loc).2.1 r hr
      refine ⟨?_, hp⟩
      rw [notifyTcRecord_action_old (no_tc_notification_record ho hn hr)]
      exact ha'
    · intro id act hact
      by_cases he : id = .async i (.tcNotify rank)
      · subst id
        rw [notifyTcRecord_action_notify hi, hmb,
          ite_eq_right (by simpa [eq_comm] using hm)] at hact
        cases hact
      · rw [notifyTcRecord_action_old he] at hact
        obtain ⟨r, hr, hrid⟩ := (ho loc).2.2 id act hact
        exact ⟨r, hlog ▸ hr, hrid⟩

end
end PTX
