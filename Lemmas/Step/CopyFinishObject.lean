-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.CopyFinish
public import Lemmas.Snoc.ObjectAppend

@[expose] public section

/-! Completing one copy and recording its notification in a checked object history.
The object transition is a proof obligation, not an assumed phase or counter update. -/
namespace PTX
open AsyncCopy MBarrier
noncomputable section

def Execution.finishCopyRecord (X : Execution) (i : EvId) (bs : List Byte)
    (src : Nat → Option Ref) (mb : Loc) (rec : Record Ref) : Execution :=
  (X.finishCopy i bs src).appendObject mb rec

variable {X : Execution} {i : EvId} {bs : List Byte} {src : Nat → Option Ref}
  {mb : Loc} {rec : Record Ref}

theorem finishCopyRecord_action_old {loc : Loc} {id : Ref} (hid : id ≠ .async i (.notify .copy)) :
    objectAction (X.finishCopyRecord i bs src mb rec)
      (X.finishCopyRecord i bs src mb rec).async loc id = objectAction X X.async loc id := by
  cases id with
  | thread j => rfl
  | async j p =>
    cases p <;> try rfl
    have hj : j ≠ i := fun h => hid (congrArg (fun k => Ref.async k (.notify .copy)) h)
    simp only [objectAction, Execution.finishCopyRecord, Execution.appendObject,
      Execution.finishCopy, ite_eq_right hj]
    rfl

theorem finishCopyRecord_action_notify {spec : Spec} (hi : issuedBy X i = some spec)
    (loc : Loc) :
    objectAction (X.finishCopyRecord i bs src mb rec)
      (X.finishCopyRecord i bs src mb rec).async loc (.async i (.notify .copy)) =
      if spec.completion = .mbarrier loc then some (.completeTx spec.dst.size) else none := by
  change (do
    let s ← issuedBy X i
    if s.completion = Completion.mbarrier loc ∧
        ((X.finishCopy i bs src).async.copies i).notified = true then
      some (MBarrier.Action.completeTx s.dst.size) else none) = _
  rw [hi]
  simp [Execution.finishCopy]

theorem no_copy_notification_record (ho : ObjectsOk X)
    (hn : (X.async.copies i).notified = false)
    {loc : Loc} {r : Record Ref} (hr : r ∈ X.objects loc) : r.id ≠ .async i (.notify .copy) := by
  intro heq
  have ha := ((ho loc).2.1 r hr).1
  rw [heq] at ha
  cases hi : issuedBy X i <;> simp [objectAction, hi, hn] at ha

/-- Provenance and coverage survive the completion. The checked transition explicitly
belongs to the supplied mbarrier; no notification can be redirected to another object. -/
theorem finishCopyRecord_objects (ho : ObjectsOk X) {spec : Spec}
    (hi : issuedBy X i = some spec) (hmb : spec.completion = .mbarrier mb)
    (hn : (X.async.copies i).notified = false)
    (hid : rec.id = .async i (.notify .copy)) (ha : rec.action = .completeTx spec.dst.size)
    (hc : CheckedLog (X.objects mb ++ [rec])) :
    ObjectsOk (X.finishCopyRecord i bs src mb rec) := by
  intro loc
  by_cases hm : loc = mb
  · subst loc
    refine ⟨by simpa [Execution.finishCopyRecord, Execution.appendObject,
      Execution.finishCopy] using hc,
      ?_, ?_⟩
    · intro r hr
      have hr' : r ∈ X.objects mb ++ [rec] := by
        simpa [Execution.finishCopyRecord, Execution.appendObject, Execution.finishCopy] using hr
      rcases List.mem_append.mp hr' with hold | hnew
      · obtain ⟨ha', hp⟩ := (ho mb).2.1 r hold
        refine ⟨?_, hp⟩
        rw [finishCopyRecord_action_old (no_copy_notification_record ho hn hold)]
        exact ha'
      · have he := List.mem_singleton.mp hnew
        subst r
        refine ⟨?_, ?_⟩
        · rw [hid, finishCopyRecord_action_notify hi, ite_eq_left hmb, ha]
        · intro p ok hp; rw [ha] at hp; cases hp
    · intro id act hact
      by_cases he : id = .async i (.notify .copy)
      · exact ⟨rec, by simp [Execution.finishCopyRecord, Execution.appendObject,
          Execution.finishCopy], hid.trans he.symm⟩
      · rw [finishCopyRecord_action_old he] at hact
        obtain ⟨r, hr, hrid⟩ := (ho mb).2.2 id act hact
        exact ⟨r, by simp [Execution.finishCopyRecord, Execution.appendObject,
          Execution.finishCopy, hr], hrid⟩
  · have hlog : (X.finishCopyRecord i bs src mb rec).objects loc = X.objects loc := by
      simp [Execution.finishCopyRecord, Execution.appendObject, Execution.finishCopy, hm]
    refine ⟨by rw [hlog]; exact (ho loc).1, ?_, ?_⟩
    · intro r hr
      rw [hlog] at hr
      obtain ⟨ha', hp⟩ := (ho loc).2.1 r hr
      refine ⟨?_, hp⟩
      rw [finishCopyRecord_action_old (no_copy_notification_record ho hn hr)]
      exact ha'
    · intro id act hact
      by_cases he : id = .async i (.notify .copy)
      · subst id
        rw [finishCopyRecord_action_notify hi,
          ite_eq_right fun h => hm (Completion.mbarrier.inj (hmb.symm.trans h)).symm] at hact
        cases hact
      · rw [finishCopyRecord_action_old he] at hact
        obtain ⟨r, hr, hrid⟩ := (ho loc).2.2 id act hact
        exact ⟨r, hlog ▸ hr, hrid⟩

end
end PTX
