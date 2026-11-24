-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.ReturningPrefix
import Lemmas.Flow.ContinuingEvent

@[expose] public section

namespace PTX.Flow
open PTX

variable {K : Kernel} {A : List Assumption} {l : Launch} {g : Nat}

/-- A path splits at the state returned by its last recorded event. -/
theorem TraceReach.returnedPrefix {s t : TState} {events : List Event}
    (h : TraceReach K A l g s events t) :
    ∃ before, Run K A l g s events (some before) ∧
      Relation.ReflTransGen (Tau K A l g) before t := by
  induction h with
  | refl => exact ⟨_,.nil _, .refl⟩
  | tau hs _ ih =>
    obtain ⟨u,hRun,hLocal⟩ := ih
    cases hRun with
    | nil => exact ⟨_,.nil _,.head hs hLocal⟩
    | step ht he hTail => exact ⟨_,.step (.head hs ht) he hTail,hLocal⟩
  | event he _ ih =>
    obtain ⟨u,hRun,hLocal⟩ := ih
    exact ⟨u,.step .refl he hRun,hLocal⟩

private theorem traceBetweenLaterIndex {events : List Event} {i j : Nat}
    {s₀ s t₀ t : TState} (hi : i < j) (hj : j ≤ events.length)
    (hS : Run K A l g {} (events.take i) (some s₀))
    (hPathS : Relation.ReflTransGen (Tau K A l g) s₀ s)
    (hT : Run K A l g {} (events.take j) (some t₀))
    (hPathT : Relation.ReflTransGen (Tau K A l g) t₀ t) :
    TraceReach K A l g s ((events.drop i).take (j-i)) t := by
  let prefixEvents := events.take j
  have hTake : prefixEvents.take i = events.take i := by
    rw [show prefixEvents = events.take j from rfl,List.take_take,Nat.min_eq_left hi.le]
  have hSplit : prefixEvents = events.take i ++ prefixEvents.drop i := by
    simpa only [hTake] using (List.take_append_drop i prefixEvents).symm
  have hPrefix : Run K A l g {} prefixEvents (some t₀) := hT
  have hMid := hS.after_returned_prefix (hSplit ▸ hPrefix)
  have hSome : prefixEvents.drop i ≠ [] := by
    intro h
    have hLen := congrArg List.length h
    simp [prefixEvents,List.length_take,Nat.min_eq_left hj] at hLen
    omega
  have hPath := (hMid.after_local_nonempty hPathS hSome).returning_reach.append
    (TraceReach.of_local hPathT)
  simpa only [List.append_nil,prefixEvents,List.drop_take] using hPath

/-- Two checkpoints in the same recorded trace are ordered when the latter cannot
reach the former, and the interval between them is an actual path. -/
theorem recordedCheckpointsPath {events : List Event} {i j : Nat}
    {s₀ s t₀ t : TState} (hi : i ≤ events.length) (hj : j ≤ events.length)
    (hS : Run K A l g {} (events.take i) (some s₀))
    (hPathS : Relation.ReflTransGen (Tau K A l g) s₀ s)
    (hT : Run K A l g {} (events.take j) (some t₀))
    (hPathT : Relation.ReflTransGen (Tau K A l g) t₀ t)
    (hForward : ∀ es, ¬ TraceReach K A l g t es s) :
    i ≤ j ∧ TraceReach K A l g s ((events.drop i).take (j-i)) t := by
  rcases lt_trichotomy i j with h | rfl | h
  · exact ⟨h.le,traceBetweenLaterIndex h hj hS hPathS hT hPathT⟩
  · obtain rfl := Option.some.inj (hS.det hT)
    rcases rtg_tau_total hPathS hPathT with hGo | hBack
    · exact ⟨le_rfl,by simpa only [Nat.sub_self,List.take_zero] using TraceReach.of_local hGo⟩
    · exact (hForward [] (TraceReach.of_local hBack)).elim
  · exact (hForward _ (traceBetweenLaterIndex h hi hT hPathT hS hPathS)).elim

/-- A local prefix can be dropped from the observed interval when the end cannot
precede that local checkpoint. -/
theorem TraceReach.afterLocalOfNoBack {s u t : TState} {events : List Event}
    (h : TraceReach K A l g s events t)
    (hLocal : Relation.ReflTransGen (Tau K A l g) s u)
    (hNoBack : ¬ Relation.ReflTransGen (Tau K A l g) t u) :
    TraceReach K A l g u events t := by
  obtain ⟨before,hRun,ht⟩ := h.returnedPrefix
  by_cases he : events = []
  · subst events
    cases hRun
    rcases rtg_tau_total hLocal ht with hGo | hBack
    · exact .of_local hGo
    · exact (hNoBack hBack).elim
  · have hGo := (hRun.after_local_nonempty hLocal he).returning_reach.append (.of_local ht)
    simpa only [List.append_nil] using hGo

end PTX.Flow
