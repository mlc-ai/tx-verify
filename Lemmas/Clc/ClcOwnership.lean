-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Clc.ClcOwnership
public import Mathlib.Logic.Relation

@[expose] public section

namespace PTX.Clc

/-- Launch/cancellation cannot steal a task from an earlier owner. -/
theorem Step.owner_stable {valid : Nat → Prop} {s t : State}
    (h : Step valid s t) {task : Nat} {o : Owner} (ho : s.owner task = some o) :
    t.owner task = some o := by
  cases h with
  | launch other hv hp =>
    have hn : task ≠ other := by intro he; subst other; simp_all
    simpa [Function.update, hn] using ho
  | success r other hv hf hp =>
    have hn : task ≠ other := by intro he; subst other; simp_all
    simpa [Function.update, hn] using ho
  | failure => exact ho

/-- A request cannot later acquire a different result. -/
theorem Step.response_stable {valid : Nat → Prop} {s t : State}
    (h : Step valid s t) {request : Nat} {answer : Option Nat}
    (hr : s.response request = some answer) : t.response request = some answer := by
  cases h with
  | launch => exact hr
  | success other task hv hf hp =>
    have hn : request ≠ other := by intro he; subst other; simp_all
    simpa [Function.update, hn] using hr
  | failure other hf =>
    have hn : request ≠ other := by intro he; subst other; simp_all
    simpa [Function.update, hn] using hr

theorem owner_stable {valid : Nat → Prop} {s t : State}
    (h : Relation.ReflTransGen (Step valid) s t) {task : Nat} {o : Owner}
    (ho : s.owner task = some o) : t.owner task = some o := by
  induction h with
  | refl => exact ho
  | tail _ h ih => exact h.owner_stable ih

/-- Distinct cancellations cannot claim a task already assigned by a prior success. -/
theorem canceled_unique {valid : Nat → Prop} {s t : State}
    (h : Relation.ReflTransGen (Step valid) s t) {task r q : Nat}
    (hs : s.owner task = some (.canceled r))
    (ht : t.owner task = some (.canceled q)) : r = q := by
  have he := owner_stable h hs
  simpa [ht] using he.symm

/-- Response payloads agree with the persistent ownership assignment. -/
def ResponsesOwnTasks (s : State) : Prop :=
  ∀ request task, s.response request = some (some task) →
    s.owner task = some (.canceled request)

theorem Step.responses_own_tasks {valid : Nat → Prop} {s t : State}
    (h : Step valid s t) (hi : ResponsesOwnTasks s) : ResponsesOwnTasks t := by
  intro request task hr
  cases h with
  | launch other hv hp =>
    have ho := hi request task hr
    have hn : task ≠ other := by intro he; subst other; simp_all
    simpa [Function.update, hn] using ho
  | success other newTask hv hf hp =>
    by_cases hn : request = other
    · subst request
      have ht : newTask = task := by simpa using hr
      subst task
      simp
    · have hold : _ := hi request task (by simpa [Function.update, hn] using hr)
      have ht : task ≠ newTask := by intro he; subst newTask; simp_all
      simpa [Function.update, ht] using hold
  | failure other hf =>
    by_cases hn : request = other
    · subst request
      simp at hr
    · exact hi request task (by simpa [Function.update, hn] using hr)

theorem responses_own_tasks {valid : Nat → Prop} {s : State}
    (h : Relation.ReflTransGen (Step valid) initial s) : ResponsesOwnTasks s := by
  induction h with
  | refl => intro request task hr; simp [initial] at hr
  | tail _ h ih => exact h.responses_own_tasks ih

/-- Every cancellation owner has the matching successful response. Ownership cannot
appear independently of the arbitration that assigned it. -/
theorem canceled_has_response {valid : Nat → Prop} {s : State}
    (h : Relation.ReflTransGen (Step valid) initial s) :
    ∀ task request, s.owner task = some (.canceled request) →
      s.response request = some (some task) := by
  induction h with
  | refl => intro task request ho; simp [initial] at ho
  | tail _ step ih =>
    intro task request ho
    cases step with
    | launch other hv hp =>
      by_cases ht : task = other
      · subst task; simp at ho
      · exact ih task request (by simpa [Function.update, ht] using ho)
    | success other newTask hv hf hp =>
      by_cases ht : task = newTask
      · subst task
        have hr : other = request := by simpa using ho
        subst request
        simp
      · have hold := ho
        simp only [Function.update_of_ne ht] at hold
        have hr := ih task request hold
        have hn : request ≠ other := by
          intro he
          subst request
          simp [hf] at hr
        simpa [Function.update, hn] using hr
    | failure other hf =>
      have hr := ih task request ho
      have hn : request ≠ other := by
        intro he
        subst request
        simp [hf] at hr
      simpa [Function.update, hn] using hr

end PTX.Clc
