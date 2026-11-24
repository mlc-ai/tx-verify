-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Async.BulkExecution
public import Lemmas.Async.BulkGroup

@[expose] public section

/-! # Bulk groups by counting commits

A proof tool. Along a thread's trace, its bulk-group state has one committed group per commit
event, and a tensor store issued after `m` commits belongs to group `m` once the next commit
follows, and is pending until then (`members`). So a wait that retains `r` groups and follows
more than `m + r` commits observes that store (`observes_of_commits`). -/

namespace PTX.Flow

open BulkGroup

/-- A bulk commit event. -/
def isCommit (e : Event) : Bool := match e.kind with | .bulkCommit => true | _ => false

/-- The commits of a trace. -/
def commits (es : List Event) : Nat := es.countP isCommit

/-- A tensor store event. -/
def isTensorStore (e : Event) : Bool := match e.kind with | .tensorStore _ _ => true | _ => false

/-- The tensor stores of a trace. -/
def storeIssues (es : List Event) : Nat := es.countP isTensorStore

theorem storeIssues_snoc (es : List Event) (e : Event) :
    storeIssues (es ++ [e]) = storeIssues es + if isTensorStore e then 1 else 0 := by
  simp [storeIssues, List.countP_append]

theorem bulkActions_snoc (g : Nat) (es : List Event) (e : Event) :
    bulkActions g (es ++ [e]) = bulkActions g es ++ (bulkAction g es.length e.kind).toList := by
  simp only [bulkActions, List.zipIdx_append, List.filterMap_append]
  congr 1
  simp only [List.zipIdx_singleton, Nat.zero_add, List.filterMap_cons, List.filterMap_nil]
  cases bulkAction g es.length e.kind <;> rfl

/-- The groups of a thread's trace: one per commit, and each tensor store in the group numbered
by the commits before it, or pending. -/
theorem members (g : Nat) (es : List Event) :
    (run (bulkActions g es)).groups.length = commits es ∧
    ∀ i pc a sp, es[i]? = some ⟨pc, .tensorStore a sp⟩ →
      (commits (es.take i) < commits es →
        (g, i) ∈ (run (bulkActions g es)).groups.getD (commits (es.take i)) []) ∧
      (commits (es.take i) = commits es → (g, i) ∈ (run (bulkActions g es)).pending) := by
  induction es using List.reverseRecOn with
  | nil => simp [run, bulkActions, commits]
  | append_singleton es e ih =>
    obtain ⟨hlen, hmem⟩ := ih
    have hrun : run (bulkActions g (es ++ [e])) =
        (bulkAction g es.length e.kind).toList.foldl step (run (bulkActions g es)) := by
      rw [bulkActions_snoc]
      simp only [run, List.foldl_append]
    have hc : commits (es ++ [e]) = commits es + (if isCommit e then 1 else 0) := by
      simp [commits, List.countP_append]
    have htake : ∀ i, i < es.length → (es ++ [e]).take i = es.take i := fun i hi => by
      rw [List.take_append_of_le_length hi.le]
    have hold : ∀ i pc a sp, i < es.length → (es ++ [e])[i]? = some ⟨pc, .tensorStore a sp⟩ →
        es[i]? = some ⟨pc, .tensorStore a sp⟩ := fun i pc a sp hi h => by
      rwa [List.getElem?_append_left hi] at h
    have hlast : ∀ i, (es ++ [e])[i]?.isSome → i < es.length ∨ i = es.length := fun i h => by
      have := (Option.isSome_iff_exists.mp h)
      obtain ⟨x, hx⟩ := this
      have := (List.getElem?_eq_some_iff.mp hx).1
      simp at this
      omega
    -- a step that adds no group member and no commit
    have hkeep : ∀ (hs : run (bulkActions g (es ++ [e])) = run (bulkActions g es))
        (hce : isCommit e = false) (hne : ∀ pc a sp, e ≠ ⟨pc, .tensorStore a sp⟩),
        (run (bulkActions g (es ++ [e]))).groups.length = commits (es ++ [e]) ∧
        ∀ i pc a sp, (es ++ [e])[i]? = some ⟨pc, .tensorStore a sp⟩ →
          (commits ((es ++ [e]).take i) < commits (es ++ [e]) →
            (g, i) ∈ (run (bulkActions g (es ++ [e]))).groups.getD
              (commits ((es ++ [e]).take i)) []) ∧
          (commits ((es ++ [e]).take i) = commits (es ++ [e]) →
            (g, i) ∈ (run (bulkActions g (es ++ [e]))).pending) := by
      intro hs hce hne
      have hc' : commits (es ++ [e]) = commits es := by rw [hc, hce]; rfl
      rw [hs, hc']
      refine ⟨hlen, fun i pc a sp hi => ?_⟩
      rcases hlast i (by rw [hi]; rfl) with hlt | rfl
      · rw [htake i hlt]
        exact hmem i pc a sp (hold i pc a sp hlt hi)
      · simp at hi
        exact absurd hi (hne pc a sp)
    obtain ⟨epc, ek⟩ := e
    cases ek
    case tensorStore a sp =>
      have hs : run (bulkActions g (es ++ [⟨epc, .tensorStore a sp⟩])) =
          { run (bulkActions g es) with
            pending := (run (bulkActions g es)).pending ++ [(g, es.length)] } := by
        rw [hrun]; rfl
      have hc' : commits (es ++ [⟨epc, .tensorStore a sp⟩]) = commits es := by
        rw [hc]; rfl
      rw [hs, hc']
      refine ⟨hlen, fun i pc a' sp' hi => ?_⟩
      rcases hlast i (by rw [hi]; rfl) with hlt | rfl
      · rw [htake i hlt]
        obtain ⟨h1, h2⟩ := hmem i pc a' sp' (hold i pc a' sp' hlt hi)
        exact ⟨h1, fun h => List.mem_append_left _ (h2 h)⟩
      · rw [List.take_left' rfl]
        exact ⟨fun h => absurd h (Nat.lt_irrefl _), fun _ => by simp⟩
    case bulkCommit =>
      have hs : run (bulkActions g (es ++ [⟨epc, .bulkCommit⟩])) =
          ⟨[], (run (bulkActions g es)).groups ++ [(run (bulkActions g es)).pending]⟩ := by
        rw [hrun]; rfl
      have hc' : commits (es ++ [⟨epc, .bulkCommit⟩]) = commits es + 1 := by
        rw [hc]; rfl
      rw [hs, hc']
      refine ⟨by simp [hlen], fun i pc a' sp' hi => ?_⟩
      rcases hlast i (by rw [hi]; rfl) with hlt | rfl
      · rw [htake i hlt]
        obtain ⟨h1, h2⟩ := hmem i pc a' sp' (hold i pc a' sp' hlt hi)
        have hle : commits (es.take i) ≤ commits es :=
          (List.take_sublist i es).countP_le
        refine ⟨fun _ => ?_, fun h => by omega⟩
        rcases Nat.lt_or_ge (commits (es.take i)) (commits es) with h3 | h3
        · have := h1 h3
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega)]
          rwa [List.getD_eq_getElem?_getD] at this
        · have heq : commits (es.take i) = commits es := by omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), heq, hlen]
          simpa using h2 heq
      · simp at hi
    case bulkWait mode n =>
      exact hkeep (by rw [hrun]; rfl) rfl (fun _ _ _ h => by cases h)
    case copy s =>
      by_cases hBulk : s.completion = .bulkGroup
      · have hs : run (bulkActions g (es ++ [⟨epc, .copy s⟩])) =
            { run (bulkActions g es) with
              pending := (run (bulkActions g es)).pending ++ [(g, es.length)] } := by
          rw [hrun]
          simp [bulkAction, hBulk, step]
        have hcc : commits (es ++ [⟨epc, .copy s⟩]) = commits es := by rw [hc]; rfl
        rw [hs, hcc]
        refine ⟨hlen, fun i pc a' sp' hi => ?_⟩
        rcases hlast i (by rw [hi]; rfl) with hlt | rfl
        · rw [htake i hlt]
          obtain ⟨h1, h2⟩ := hmem i pc a' sp' (hold i pc a' sp' hlt hi)
          exact ⟨h1, fun h => List.mem_append_left _ (h2 h)⟩
        · rw [List.take_left' rfl]
          exact ⟨fun h => absurd h (Nat.lt_irrefl _), fun _ => by simp⟩
      · exact hkeep (by rw [hrun]; simp [bulkAction, hBulk]) rfl (fun _ _ _ h => by cases h)
    all_goals exact hkeep (by rw [hrun]; rfl) rfl (fun _ _ _ h => by cases h)

/-- A wait that retains `r` groups observes a tensor store of its thread issued after `m`
commits when more than `m + r` commits precede the wait. -/
theorem observes_of_commits {X : Execution} {g i w pc : Nat} {a : Nat} {sp : TensorStore.Spec}
    (hi : X.get (g, i) = some ⟨pc, .tensorStore a sp⟩) (hiw : i < w) {r : Nat}
    (hm : commits ((X.tr g).take i) + r < commits ((X.tr g).take w)) :
    Observes (bulkStateBefore X (g, w)) r (g, i) := by
  obtain ⟨hlen, hmem⟩ := members g ((X.tr g).take w)
  have hi' : ((X.tr g).take w)[i]? = some ⟨pc, .tensorStore a sp⟩ := by
    rw [List.getElem?_take_of_lt hiw]; exact hi
  have hti : ((X.tr g).take w).take i = (X.tr g).take i := by
    rw [List.take_take, Nat.min_eq_left hiw.le]
  obtain ⟨h1, -⟩ := hmem i pc a sp hi'
  rw [hti] at h1
  have hin := h1 (by omega)
  rw [List.getD_eq_getElem?_getD] at hin
  rcases hg : (run (bulkActions g ((X.tr g).take w))).groups[commits ((X.tr g).take i)]? with
    _ | grp
  · rw [hg] at hin; simp at hin
  · rw [hg] at hin
    simp only [Option.getD_some] at hin
    refine ⟨grp, ?_, hin⟩
    unfold required
    simp only [bulkStateBefore]
    apply List.mem_iff_getElem?.mpr
    refine ⟨commits ((X.tr g).take i), ?_⟩
    rw [List.getElem?_take_of_lt (by omega), hg]

end PTX.Flow
