-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Snoc.SnocObjectMemory

@[expose] public section

/-! Mbarrier instruction extension. Every new record is checked against the general
object interpreter; no phase, number of writers, or producer role is assumed. -/
namespace PTX
open AsyncCopy MBarrier
noncomputable section
section
variable {L : Launch} {X : Execution} {g : Nat} {e : Event} {r : Nat → Option Ref}

theorem snoc_copy_wellFormed (ht : TmaOk X) :
    WellFormed (issuedBy (X.snoc g e r)) X.async := by
  intro i hi
  obtain ⟨s, hs, hc⟩ := ht.1 i hi
  obtain ⟨pc, he⟩ := issuedBy_some.mp hs
  refine ⟨s, issuedBy_some.mpr ⟨pc, ?_⟩, hc⟩
  rw [snoc_get_old (len_of_get he)]
  exact he

/-- New source instructions cannot change the meaning of an existing object operation. -/
theorem snoc_objectAction_old (hv : EffectValidity L X) (_hk : ∀ k, e.kind ≠ .tc k)
    (m : Loc) {id : Ref} (hid : id ≠ .thread (g, (X.tr g).length)) :
    objectAction (X.snoc g e r) X.async m id = objectAction X X.async m id := by
  cases id with
  | thread i =>
    have hi : i ≠ (g,(X.tr g).length) := fun h => hid (congrArg Ref.thread h)
    simp only [objectAction,snoc_get,ite_eq_right hi]
  | async i p =>
    by_cases hi : i = (g,(X.tr g).length)
    · subst i
      have hget : X.get (g,(X.tr g).length) = none := List.getElem?_eq_none (le_refl _)
      have hcn : (X.async.copies (g,(X.tr g).length)).notified = false := by
        cases hn : (X.async.copies (g,(X.tr g).length)).notified with
        | false => rfl
        | true =>
          obtain ⟨spec,hs,_⟩ := hv.tma.1 _ ⟨.notify .copy,hn⟩
          obtain ⟨pc,hp⟩ := issuedBy_some.mp hs
          rw [hget] at hp; cases hp
      have htn : X.tensor (g,(X.tr g).length) = none := by
        cases ho : X.tensor (g,(X.tr g).length) with
        | none => rfl
        | some o =>
          obtain ⟨addr,pc,hp⟩ := (hv.tensor _ o ho).1
          rw [hget] at hp; cases hp
      have hcl : (X.clc (g,(X.tr g).length)).notified = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro c hc
        obtain ⟨spec,targets,pc,hp⟩ := hv.clc.2.2.1 _ (.inr (.inr ⟨c,hc⟩))
        rw [hget] at hp; cases hp
      have hmc : X.tcNotified (g,(X.tr g).length) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro rank hr
        obtain ⟨⟨spec,m,⟨pc,hp⟩,_⟩,_⟩ := hv.tcCommit _ rank hr
        rw [hget] at hp; cases hp
      have har : X.async.arrived (g,(X.tr g).length) = false := by
        cases ha : X.async.arrived (g,(X.tr g).length) with
        | false => rfl
        | true =>
          obtain ⟨⟨m', noinc, pc, hp⟩, -⟩ := hv.tma.2.2.2 _ ha
          rw [hget] at hp; cases hp
      cases p <;> first
        | rfl
        | (simp only [objectAction,issuedBy,snoc_get_new,hget]
           cases e with | mk pc kind =>
             cases kind <;> first
               | (simp [hcn,htn,hcl,hmc,har,Execution.snoc]; done)
               | (rename_i k; cases k <;> simp [hmc,Execution.snoc]))
    · cases p <;> first
        | rfl
        | (simp only [objectAction,issuedBy,snoc_get,ite_eq_right hi]; try rfl)

theorem snoc_objects_checked (hv : EffectValidity L X) (hk : ∀ k, e.kind ≠ .tc k)
    (m : Loc) (rec : Record Ref) (hid : rec.id = .thread (g, (X.tr g).length))
    (ha : ∀ l, objectAction (X.snoc g e r) X.async l (.thread (g, (X.tr g).length)) =
      if l = m then some rec.action else none)
    (hlog : CheckedLog (X.objects m ++ [rec]))
    (hpoll : ∀ p ok, rec.action = .pollParity p ok → rec.fault = none → rec.reply.waited =
      some ok) :
    ObjectsOk ((X.snoc g e r).appendObject m rec) := by
  have ht := hv.tma
  have old_id {l : Loc} {q : Record Ref} (hq : q ∈ X.objects l) :
      q.id ≠ .thread (g, (X.tr g).length) := snoc_fresh_object_id ht hq
  intro l
  by_cases hl : l = m
  · subst l
    refine ⟨by simpa [Execution.appendObject, snoc_objects] using hlog, ?_, ?_⟩
    · intro q hq
      change q ∈ (if m = m then X.objects m ++ [rec] else X.objects m) at hq
      simp only [↓reduceIte, List.mem_append, List.mem_singleton] at hq
      rcases hq with hold | hnew
      · obtain ⟨hact, hp⟩ := (ht.2.2.1 m).2.1 q hold
        refine ⟨?_, hp⟩
        change objectAction (X.snoc g e r) X.async m q.id = some q.action
        rw [snoc_objectAction_old hv hk m (old_id hold)]
        exact hact
      · subst q
        refine ⟨?_, hpoll⟩
        change objectAction (X.snoc g e r) X.async m rec.id = some rec.action
        rw [hid, ha, ite_eq_left rfl]
    · intro id act hact
      change objectAction (X.snoc g e r) X.async m id = some act at hact
      by_cases hi : id = .thread (g, (X.tr g).length)
      · exact ⟨rec, by simp [Execution.appendObject], hid.trans hi.symm⟩
      · rw [snoc_objectAction_old hv hk m hi] at hact
        obtain ⟨q, hq, hqid⟩ := (ht.2.2.1 m).2.2 id act hact
        exact ⟨q, by simp [Execution.appendObject, snoc_objects, hq], hqid⟩
  · refine ⟨by simpa [Execution.appendObject, snoc_objects, hl] using (ht.2.2.1 l).1, ?_, ?_⟩
    · intro q hq
      have hqX : q ∈ X.objects l := by simpa [Execution.appendObject, snoc_objects, hl] using hq
      obtain ⟨hact, hp⟩ := (ht.2.2.1 l).2.1 q hqX
      refine ⟨?_, hp⟩
      change objectAction (X.snoc g e r) X.async l q.id = some q.action
      rw [snoc_objectAction_old hv hk l (old_id hqX)]
      exact hact
    · intro id act hact
      change objectAction (X.snoc g e r) X.async l id = some act at hact
      by_cases hi : id = .thread (g, (X.tr g).length)
      · rw [hi, ha, ite_eq_right hl] at hact
        cases hact
      · rw [snoc_objectAction_old hv hk l hi] at hact
        obtain ⟨q, hq, hqid⟩ := (ht.2.2.1 l).2.2 id act hact
        exact ⟨q, by simpa [Execution.appendObject, snoc_objects, hl] using hq, hqid⟩

/-- A non-object instruction keeps the histories and their coverage intact. -/
theorem snoc_objects_unchanged (hv : EffectValidity L X) (hk : ∀ k, e.kind ≠ .tc k)
    (ha : ∀ l, objectAction (X.snoc g e r) X.async l (.thread (g, (X.tr g).length)) = none) :
    ObjectsOk (X.snoc g e r) := by
  have ht := hv.tma
  intro l
  refine ⟨(ht.2.2.1 l).1, ?_, ?_⟩
  · intro q hq
    obtain ⟨hact, hp⟩ := (ht.2.2.1 l).2.1 q hq
    refine ⟨?_, hp⟩
    change objectAction (X.snoc g e r) X.async l q.id = some q.action
    rw [snoc_objectAction_old hv hk l (snoc_fresh_object_id ht hq)]
    exact hact
  · intro id act hact
    change objectAction (X.snoc g e r) X.async l id = some act at hact
    by_cases hi : id = .thread (g, (X.tr g).length)
    · rw [hi, ha] at hact
      cases hact
    · rw [snoc_objectAction_old hv hk l hi] at hact
      exact (ht.2.2.1 l).2.2 id act hact

/-- Extending object histories preserves established thread causality. -/
theorem baseCausality_snoc_history {records : Loc → List (Record Ref)}
    (ho : ∀ m, List.IsPrefix (X.objects m) (records m)) {a b : EvId} (h : baseCausality L X a b) :
    baseCausality L (X.snocHistory g e r records) a b := by
  have hs : baseCausality L (X.snoc g e r) a b := baseCausality_snoc h
  clear h
  have lift : ∀ a b, (po (X.snoc g e r) a b ∨ CtaBarSync L (X.snoc g e r) a b ∨
      MSync L (X.snoc g e r) a b ∨ ClusterSync L (X.snoc g e r) a b ∨
      WarpBarSync L (X.snoc g e r) a b ∨ synchronizesWith L (X.snoc g e r) a b ∨
      FenceSync L (X.snoc g e r) a b) →
      po (X.snocHistory g e r records) a b ∨ CtaBarSync L (X.snocHistory g e r records) a b ∨
      MSync L (X.snocHistory g e r records) a b ∨ ClusterSync L (X.snocHistory g e r records) a b ∨
      WarpBarSync L (X.snocHistory g e r records) a b ∨
      synchronizesWith L (X.snocHistory g e r records) a b ∨
      FenceSync L (X.snocHistory g e r records) a b := by
    intro a b h
    rcases h with hp | hs | hm | hc | hw | hmem | hf
    · exact .inl hp
    · exact .inr (.inl hs)
    · obtain ⟨x,w,m,rs,ws,hr,⟨ha,hu⟩,hsc,hwt,hwi,hf,hxt,hxi⟩ := hm
      exact .inr (.inr (.inl
        ⟨x,w,m,rs,ws,hr,⟨ha,hu.extends (ho m)⟩,hsc,hwt,hwi,hf,hxt,hxi⟩))
    · exact .inr (.inr (.inr (.inl hc)))
    · exact .inr (.inr (.inr (.inr (.inl hw))))
    · exact .inr (.inr (.inr (.inr (.inr (.inl hmem)))))
    · exact .inr (.inr (.inr (.inr (.inr (.inr hf)))))
  induction hs with
  | single h => exact .single (lift _ _ h)
  | tail _ h ih => exact ih.tail (lift _ _ h)

end
end
end PTX
