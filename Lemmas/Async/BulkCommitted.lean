-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.BulkExecution
public import Lemmas.Async.BulkGroup

@[expose] public section

/-! # A bulk-group wait covers every operation committed before it

A wait that leaves out no group covers the operations its thread issued before one of its commits
before the wait (`bulkWaitsFor_of_commit`). -/

namespace PTX
open BulkGroup

/-- A step keeps the committed operations. -/
theorem BulkGroup.foldl_groups {ι : Type} (id : ι) (as : List (Action ι)) (s : State ι)
    (h : ∃ group ∈ s.groups, id ∈ group) : ∃ group ∈ (as.foldl step s).groups, id ∈ group := by
  induction as generalizing s with
  | nil => exact h
  | cons a as ih =>
    refine ih _ ?_
    obtain ⟨group, hg, hi⟩ := h
    cases a with
    | commit => exact ⟨group, List.mem_append_left _ hg, hi⟩
    | _ => exact ⟨group, hg, hi⟩

/-- A step keeps the issued operations. -/
theorem BulkGroup.foldl_issued {ι : Type} (id : ι) (as : List (Action ι)) (s : State ι)
    (h : (∃ group ∈ s.groups, id ∈ group) ∨ id ∈ s.pending) :
    (∃ group ∈ (as.foldl step s).groups, id ∈ group) ∨ id ∈ (as.foldl step s).pending := by
  induction as generalizing s with
  | nil => exact h
  | cons a as ih =>
    refine ih _ ?_
    cases a with
    | commit =>
      refine .inl ?_
      rcases h with ⟨group, hg, hi⟩ | h
      · exact ⟨group, List.mem_append_left _ hg, hi⟩
      · exact ⟨s.pending, List.mem_append_right _ (List.mem_singleton_self _), h⟩
    | issue id' => exact h.imp_right fun h => List.mem_append_left _ h
    | wait _ _ => exact h

/-- An operation issued before a commit is committed. -/
theorem BulkGroup.run_committed {ι : Type} (id : ι) (a b c : List (Action ι)) :
    ∃ group ∈ (run (a ++ .issue id :: (b ++ .commit :: c))).groups, id ∈ group := by
  unfold run
  rw [List.foldl_append, List.foldl_cons, List.foldl_append, List.foldl_cons]
  refine foldl_groups id c _ ?_
  have h := foldl_issued id b (step (a.foldl step {}) (.issue id))
    (.inr (List.mem_append_right _ (List.mem_singleton_self _)))
  rcases h with ⟨group, hg, hi⟩ | h
  · exact ⟨group, List.mem_append_left _ hg, hi⟩
  · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), h⟩

/-- **A wait that leaves out no group covers a tensor store committed before it.** -/
theorem bulkWaitsFor_of_commit {X : Execution} {g k c w pc pcc pcw addr : Nat}
    {spec : TensorStore.Spec} {mode : WaitMode}
    (hk : X.get (g, k) = some ⟨pc, .tensorStore addr spec⟩)
    (hc : X.get (g, c) = some ⟨pcc, .bulkCommit⟩) (hw : X.get (g, w) = some ⟨pcw, .bulkWait mode 0⟩)
    (hkc : k < c) (hcw : c < w) : BulkWaitsFor X mode (g, k) (g, w) := by
  refine ⟨pcw, 0, hw, ?_⟩
  rw [observes_zero]
  unfold bulkStateBefore bulkActions
  have hk' : (X.tr g)[k]? = some ⟨pc, .tensorStore addr spec⟩ := hk
  have hc' : (X.tr g)[c]? = some ⟨pcc, .bulkCommit⟩ := hc
  obtain ⟨hkl, hke⟩ := List.getElem?_eq_some_iff.mp hk'
  obtain ⟨hcl, hce⟩ := List.getElem?_eq_some_iff.mp hc'
  have hsplit : ∀ {l : List (Event × Nat)} {i : Nat} (h : i < l.length),
      l = l.take i ++ l[i] :: l.drop (i + 1) := fun h => by
    rw [List.getElem_cons_drop, List.take_append_drop]
  set l := ((X.tr g).take w).zipIdx with hl
  have hlen : l.length = min w (X.tr g).length := by simp [hl]
  have hkl' : k < l.length := by omega
  have hd : c - (k + 1) < (l.drop (k + 1)).length := by rw [List.length_drop]; omega
  have e1 : l[k] = (⟨pc, .tensorStore addr spec⟩, k) := by simp [hl, hke]
  have e2 : (l.drop (k + 1))[c - (k + 1)] = (⟨pcc, .bulkCommit⟩, c) := by
    rw [List.getElem_drop]
    simp only [hl, List.getElem_zipIdx, List.getElem_take, show k + 1 + (c - (k + 1)) = c by omega,
      hce, Nat.zero_add]
  have h1 := hsplit hkl'
  have h2 := hsplit hd
  rw [e1] at h1
  rw [e2] at h2
  rw [h2] at h1
  show ∃ group ∈ (run (l.filterMap _)).groups, _
  rw [h1, List.filterMap_append, List.filterMap_cons, List.filterMap_append, List.filterMap_cons]
  simp only [bulkAction]
  exact run_committed _ _ _ _

end PTX
