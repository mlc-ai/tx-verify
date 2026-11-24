-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Sync.ClusterBarrierObject
public import Core.Sync.ClusterBarrierHistory
public import Lemmas.Order.JointWaits
public import Core.Sync.ClusterBarrierExecution

@[expose] public section

section
namespace PTX.ClusterBarrier

/-- Completing a phase does not replace the per-thread arrival token. -/
theorem finish_lastArrival (threads : Nat) (s : State) :
    (finish threads s).lastArrival = s.lastArrival := by
  unfold finish
  split <;> rfl

/-- A wait is for the caller's own preceding arrival, not the currently filling phase. -/
theorem wait_completed {threads g phase : Nat} {s : State}
    (hg : g < threads) (he : g ∉ s.exited)
    (ha : s.lastArrival g = some phase) (hp : phase < s.phase) :
    perform threads s (.wait g) = .done s := by
  simp [perform, hg, he, ha, hp]

end PTX.ClusterBarrier
end

section
namespace PTX.ClusterBarrier

variable {α : Type}

theorem run_append (block ctas : Nat) (s : State) (xs ys : List (Record α)) :
    run block ctas s (xs ++ ys) =
      match run block ctas s xs with
      | .done t => run block ctas t ys
      | other => other := by
  induction xs generalizing s with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.cons_append, run]
    cases h : r.perform block ctas s with
    | done t => exact ih t
    | blocked => rfl
    | fault e => rfl

theorem run_prefix {block ctas : Nat} {s t : State} {xs ys : List (Record α)}
    (h : run block ctas s (xs ++ ys) = .done t) :
    ∃ u, run block ctas s xs = .done u := by
  rw [run_append] at h
  cases hx : run block ctas s xs with
  | done u => exact ⟨u, rfl⟩
  | blocked => rw [hx] at h; cases h
  | fault e => rw [hx] at h; cases h

theorem ArrivalOf.append {block ctas phase : Nat} {xs ys : List (Record α)}
    {e : α} {release : Bool} (h : ArrivalOf block ctas xs e phase release) :
    ArrivalOf block ctas (xs ++ ys) e phase release := by
  obtain ⟨i, s, t, cta, warp, lanes, g, hi, hs, he, hp, hr⟩ := h
  have hlt : i < xs.length := (List.getElem?_eq_some_iff.mp hi).1
  refine ⟨i, s, t, cta, warp, lanes, g, ?_, ?_, he, hp, hr⟩
  · rwa [List.getElem?_append_left hlt]
  · unfold At at hs ⊢
    rwa [List.take_append_of_le_length hlt.le]

theorem WaitOf.append {block ctas phase : Nat} {xs ys : List (Record α)} {e : α}
    (h : WaitOf block ctas xs e phase) : WaitOf block ctas (xs ++ ys) e phase := by
  obtain ⟨i, s, t, cta, warp, lanes, g, hi, hs, he, hp, hr⟩ := h
  have hlt : i < xs.length := (List.getElem?_eq_some_iff.mp hi).1
  refine ⟨i, s, t, cta, warp, lanes, g, ?_, ?_, he, hp, hr⟩
  · rwa [List.getElem?_append_left hlt]
  · unfold At at hs ⊢
    rwa [List.take_append_of_le_length hlt.le]

theorem Synchronizes.append {block ctas : Nat} {xs ys : List (Record α)} {a w : α}
    (h : Synchronizes block ctas xs a w) : Synchronizes block ctas (xs ++ ys) a w := by
  obtain ⟨phase, ha, hw⟩ := h
  exact ⟨phase, ha.append, hw.append⟩

end PTX.ClusterBarrier
end

section
/-! Waiting dependencies after appending one record `r` to the history of cluster `c0`,
with the threads unchanged.

Only cluster dependencies can change in the cluster disjunct of `Waits`, and so can the
dependency layer's witness edges, whose needs are read from the cluster histories. An ordered pair
whose later record is `r`, or a pair inside `r`, enters a reference of `r`; an arrival/wait pair is
old as soon as the appended record contributes neither the arrival nor the wait. -/

namespace PTX
open AsyncCopy

section
variable {α : Type} {block ctas cta warp phase : Nat} {history : List (ClusterBarrier.Record α)}
  {lanes : List (Nat×α)} {e : α}

end

namespace ClusterRecordSnoc
noncomputable section
variable {L : Launch} {X : Execution} {c0 : Nat} {r : ClusterBarrier.Record EvId}

/-- The clusters of `X` with `r` appended to cluster `c0`. -/
def clusters (X : Execution) (c0 : Nat) (r : ClusterBarrier.Record EvId) :
    Nat → List (ClusterBarrier.Record EvId) :=
  fun c => if c=c0 then X.clusters c++[r] else X.clusters c

theorem old_history_get {c i : Nat} {q : ClusterBarrier.Record EvId}
    (hi : i<(X.clusters c).length) (hr : (clusters X c0 r c)[i]?=some q) :
    (X.clusters c)[i]?=some q := by
  by_cases hc : c=c0
  · simpa only [clusters,ite_eq_left hc,List.getElem?_append_left hi] using hr
  · simpa only [clusters,ite_eq_right hc] using hr

theorem history_get_cases {c i : Nat} {q : ClusterBarrier.Record EvId}
    (hr : (clusters X c0 r c)[i]?=some q) :
    (X.clusters c)[i]?=some q ∨ (c=c0 ∧ i=(X.clusters c).length ∧ q=r) := by
  by_cases hi : i<(X.clusters c).length
  · exact .inl (old_history_get hi hr)
  · by_cases hc : c=c0
    · simp only [clusters,ite_eq_left hc] at hr
      rw [List.getElem?_append_right (Nat.le_of_not_lt hi)] at hr
      have hd : i-(X.clusters c).length=0 := by
        have hb := (List.getElem?_eq_some_iff.mp hr).1
        simp only [List.length_singleton] at hb
        omega
      rw [hd,List.getElem?_cons_zero] at hr
      exact .inr ⟨hc,by omega,(Option.some.inj hr).symm⟩
    · have hold : (X.clusters c)[i]?=some q := by simpa only [clusters,ite_eq_right hc] using hr
      exact (hi (List.getElem?_eq_some_iff.mp hold).1).elim

/-- Only cluster dependencies and the dependency layer's witness edges change when only the
cluster histories do: every other `Waits` disjunct reads histories other than the clusters, or the
trace. -/
theorem waits_transport {cl : Nat → List (ClusterBarrier.Record EvId)} {u v : Ref×Bool}
    (hw : Waits L {X with clusters:=cl} u v) :
    (∃i j,u.1=.thread i ∧ v.1=.thread j ∧ ClusterWaits L {X with clusters:=cl} i j u.2 v.2) ∨
      (u.2=false ∧ v.2=true ∧ ∃ j, v.1=.thread j ∧ Witness L {X with clusters:=cl} u.1 j) ∨
      Waits L X u v := by
  rcases hw with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
  · exact .inr (.inr (.inl h0))
  · exact .inr (.inr (.inr (.inl h1)))
  · exact .inr (.inr (.inr (.inr (.inl h2))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl h3)))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl h4))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h5)))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl h6))))))))
  · exact .inl h7
  · exact .inr (.inl h8)
  · exact .inr (.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl h9)))))))))))
  · exact .inr (.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl h10))))))))))))
  · exact .inr (.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inl h11)))))))))))))
  · exact .inr (.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (
      Or.inr (Or.inr (Or.inr h12)))))))))))))

end
end ClusterRecordSnoc
end PTX
end
