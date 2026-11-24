-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.MBarrier.MBarrierHistory
public import Lemmas.Execution.ExecutionGrowth

@[expose] public section

/-! Object-history extension tools. Appending a record alone does not assert that the
resulting execution is consistent: provenance, the transition, coverage and dependencies
must still be proved by the caller. Earlier waits cannot gain new observations. -/
namespace PTX
open AsyncCopy MBarrier
noncomputable section

def Execution.appendObject (X : Execution) (m : Loc) (r : Record Ref) : Execution :=
  { X with objects := fun l => if l = m then X.objects m ++ [r] else X.objects l }

theorem Execution.le_appendObject (X : Execution) (m : Loc) (r : Record Ref) :
    X.le (X.appendObject m r) := by
  refine ⟨fun _ => List.prefix_refl _, fun _ _ _ => rfl, Extends.refl _, ?_, (X.le_refl).2.2.2.2⟩
  intro l
  by_cases hm : l = m
  · subst l
    exact ⟨[r], by simp [Execution.appendObject]⟩
  · simp [Execution.appendObject, hm]

theorem appendObject_update_iff {X : Execution} {m l : Loc} {r : Record Ref}
    {u w : Ref} (hnw : r.id ≠ w) :
    UpdateBeforeWait ((X.appendObject m r).objects l) u w ↔
      UpdateBeforeWait (X.objects l) u w := by
  by_cases hm : l = m
  · subst l
    simpa only [Execution.appendObject, ↓reduceIte] using UpdateBeforeWait.snoc_iff hnw
  · simp only [Execution.appendObject, ite_eq_right hm]

theorem appendObject_waitObserves_iff {X : Execution} {m l : Loc} {r : Record Ref}
    {x : Ref} {w : EvId} {acq : Bool} {ws : MbarScope} (hnw : r.id ≠ .thread w) :
    WaitObserves (X.appendObject m r) x w l acq ws ↔ WaitObserves X x w l acq ws := by
  unfold WaitObserves
  rw [appendObject_update_iff hnw]
  rfl

theorem appendObject_asyncObserved_iff {X : Execution} {m : Loc} {r : Record Ref}
    {i w : EvId} {p : Part} {acq : Bool} {ws : MbarScope} (hnw : r.id ≠ .thread w) :
    AsyncObserved (X.appendObject m r) i p w acq ws ↔ AsyncObserved X i p w acq ws := by
  unfold AsyncObserved
  simp only [appendObject_waitObserves_iff hnw]
  rfl

/-- A new record cannot change synchronization into already-recorded waits. -/
theorem appendObject_msync_iff {L : Launch} {X : Execution} {m : Loc} {r : Record Ref}
    {e f : EvId} (hnw : ∀ w mb, X.AcquireWait w mb → r.id ≠ .thread w) :
    MSync L (X.appendObject m r) e f ↔ MSync L X e f := by
  constructor <;> rintro ⟨x, w, mb, rs, ws, hr, hw, h1, h3, h4, h5, h6, h7⟩
  · have hn := hnw w mb hw.acquireWait
    exact ⟨x, w, mb, rs, ws, hr, (appendObject_waitObserves_iff hn).mp hw, h1, h3, h4, h5, h6, h7⟩
  · have hn := hnw w mb hw.acquireWait
    exact ⟨x, w, mb, rs, ws, hr, (appendObject_waitObserves_iff hn).mpr hw, h1, h3, h4, h5, h6, h7⟩

theorem appendObject_baseCausality_iff {L : Launch} {X : Execution} {m : Loc} {r : Record Ref}
    {e f : EvId} (hnw : ∀ w mb, X.AcquireWait w mb → r.id ≠ .thread w) :
    baseCausality L (X.appendObject m r) e f ↔ baseCausality L X e f := by
  have hm : ∀ e f, MSync L (X.appendObject m r) e f ↔ MSync L X e f :=
    fun _ _ => appendObject_msync_iff hnw
  have hbase : ∀ e f,
      (po (X.appendObject m r) e f ∨ CtaBarSync L (X.appendObject m r) e f ∨
        MSync L (X.appendObject m r) e f ∨ ClusterSync L (X.appendObject m r) e f ∨
        WarpBarSync L (X.appendObject m r) e f ∨
        synchronizesWith L (X.appendObject m r) e f ∨ FenceSync L (X.appendObject m r) e f) ↔
      (po X e f ∨ CtaBarSync L X e f ∨ MSync L X e f ∨ ClusterSync L X e f ∨
        WarpBarSync L X e f ∨ synchronizesWith L X e f ∨ FenceSync L X e f) := by
    intro e f
    rw [hm]
    rfl
  constructor <;> intro h
  · induction h with
    | single h => exact .single ((hbase _ _).mp h)
    | tail _ h ih => exact ih.tail ((hbase _ _).mp h)
  · induction h with
    | single h => exact .single ((hbase _ _).mpr h)
    | tail _ h ih => exact ih.tail ((hbase _ _).mpr h)

/-- Object histories do not create or erase independent memory effects. -/
theorem appendObject_asyncPresent {X : Execution} {mb : Loc} {rec : Record Ref}
    {i : EvId} {p : Part} :
    (X.appendObject mb rec).AsyncPresent i p ↔ X.AsyncPresent i p := by
  cases p <;> rfl

end
/-- An appended record of another operation changes no observation between old operations
(MEM-OBJECT-ORDER-CAUSALITY `MbarObserved`). -/
theorem appendObject_mbarObserved_iff {X : Execution} {m : Loc} {r : Record Ref}
    {x w : Ref} (hx : r.id ≠ x) (hw : r.id ≠ w) :
    MbarObserved (X.appendObject m r) x w ↔ MbarObserved X x w := by
  unfold MbarObserved
  refine and_congr Iff.rfl ?_
  constructor
  · rintro ⟨j, l, acq, ws, rfl, hwo, hc⟩
    refine ⟨j, l, acq, ws, rfl, (appendObject_waitObserves_iff hw).mp hwo, fun q hq hqx => ?_⟩
    apply hc q _ hqx
    by_cases hm : l = m
    · subst l
      simp only [Execution.appendObject, ↓reduceIte, List.mem_append]
      exact .inl hq
    · simpa only [Execution.appendObject, hm, ↓reduceIte] using hq
  · rintro ⟨j, l, acq, ws, rfl, hwo, hc⟩
    refine ⟨j, l, acq, ws, rfl, (appendObject_waitObserves_iff hw).mpr hwo, fun q hq hqx => ?_⟩
    by_cases hm : l = m
    · subst l
      simp only [Execution.appendObject, ↓reduceIte, List.mem_append, List.mem_singleton] at hq
      rcases hq with hq | rfl
      · exact hc q hq hqx
      · exact (hx hqx).elim
    · simp only [Execution.appendObject, hm, ↓reduceIte] at hq
      exact hc q hq hqx

/-- An appended record of another operation adds no object order into an old operation. -/
theorem appendObject_objectOrder_iff {L : Launch} {X : Execution} {m : Loc} {r : Record Ref}
    {o : OrderObject} {u v : Ref × Bool} (hv : r.id ≠ v.1) :
    ObjectOrder L (X.appendObject m r) o u v ↔ ObjectOrder L X o u v := by
  obtain ⟨e, b⟩ := u
  obtain ⟨f, b'⟩ := v
  cases o with
  | mbar l =>
    simp only [ObjectOrder]
    refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
    by_cases hm : l = m
    · subst l
      simpa only [Execution.appendObject, ↓reduceIte] using Before.snoc_iff hv
    · simp only [Execution.appendObject, ite_eq_right hm]
  | _ => exact Iff.rfl

end PTX
