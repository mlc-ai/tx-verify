-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness

@[expose] public section

/-! # Every cluster task has one owner

A proof tool. The arbitration state of cluster launch control pairs owners and responses
(`Owned`): a request's successful response names a valid task canceled by that request, and a
canceled task's request answered with it (`response_owner`, `owner_response`,
`response_valid`). So two successful responses name different tasks (`response_inj`), and a
launched task is named by no response (`response_not_launched`). In a complete execution, the
cluster of every launched thread is owned: it ran, or exactly one request canceled it
(`Complete.owner`). -/

namespace PTX.Clc

/-- Responses and owners agree, and responses name valid tasks. -/
structure Owned (v : Nat → Prop) (s : State) : Prop where
  response_owner : ∀ r t, s.response r = some (some t) → s.owner t = some (.canceled r)
  owner_response : ∀ r t, s.owner t = some (.canceled r) → s.response r = some (some t)
  response_valid : ∀ r t, s.response r = some (some t) → v t

theorem owned_initial (v : Nat → Prop) : Owned v initial :=
  ⟨fun _ _ h => by simp [initial] at h, fun _ _ h => by simp [initial] at h,
    fun _ _ h => by simp [initial] at h⟩

theorem Owned.step {v : Nat → Prop} {s t : State} (h : Owned v s) (hs : Step v s t) :
    Owned v t := by
  cases hs with
  | launch task _ hp =>
    refine ⟨fun r u hr => ?_, fun r u hu => ?_, fun r u hr => h.response_valid r u hr⟩
    · have ho := h.response_owner r u hr
      by_cases hu : u = task
      · subst hu; rw [hp] at ho; cases ho
      · simpa [Function.update_of_ne hu] using ho
    · by_cases he : u = task
      · subst he; simp at hu
      · exact h.owner_response r u (by simpa [Function.update_of_ne he] using hu)
  | success request task hv hf hp =>
    refine ⟨fun r u hr => ?_, fun r u hu => ?_, fun r u hr => ?_⟩
    · by_cases hre : r = request
      · subst hre
        simp only [Function.update_self, Option.some.injEq] at hr
        subst hr
        simp
      · have hr' : s.response r = some (some u) := by
          simpa [Function.update_of_ne hre] using hr
        have ho := h.response_owner r u hr'
        have hu : u ≠ task := by rintro rfl; rw [hp] at ho; cases ho
        simpa [Function.update_of_ne hu] using ho
    · by_cases he : u = task
      · subst he
        simp only [Function.update_self, Option.some.injEq, Owner.canceled.injEq] at hu
        subst hu
        simp
      · have hu' : s.owner u = some (.canceled r) := by
          simpa [Function.update_of_ne he] using hu
        have hr := h.owner_response r u hu'
        have hre : r ≠ request := by rintro rfl; rw [hf] at hr; cases hr
        simpa [Function.update_of_ne hre] using hr
    · by_cases hre : r = request
      · subst hre
        simp only [Function.update_self, Option.some.injEq] at hr
        subst hr
        exact hv
      · exact h.response_valid r u (by simpa [Function.update_of_ne hre] using hr)
  | failure request hf =>
    refine ⟨fun r u hr => ?_, fun r u hu => ?_, fun r u hr => ?_⟩
    · by_cases hre : r = request
      · subst hre; simp at hr
      · exact h.response_owner r u (by simpa [Function.update_of_ne hre] using hr)
    · have hr := h.owner_response r u hu
      have hre : r ≠ request := by rintro rfl; rw [hf] at hr; cases hr
      simpa [Function.update_of_ne hre] using hr
    · by_cases hre : r = request
      · subst hre; simp at hr
      · exact h.response_valid r u (by simpa [Function.update_of_ne hre] using hr)

theorem owned_of_reachable {v : Nat → Prop} {s : State}
    (h : Relation.ReflTransGen (Step v) initial s) : Owned v s := by
  induction h with
  | refl => exact owned_initial v
  | tail _ hs ih => exact ih.step hs

/-- **Two successful responses that name the same task are the same request.** -/
theorem Owned.response_inj {v : Nat → Prop} {s : State} (h : Owned v s) {r r' t : Nat}
    (hr : s.response r = some (some t)) (hr' : s.response r' = some (some t)) : r = r' := by
  have h1 := h.response_owner r t hr
  have h2 := h.response_owner r' t hr'
  rw [h1] at h2
  exact Owner.canceled.inj (Option.some.inj h2)

/-- A launched task is named by no successful response. -/
theorem Owned.response_not_launched {v : Nat → Prop} {s : State} (h : Owned v s) {r t : Nat}
    (hr : s.response r = some (some t)) (hl : s.owner t = some .launched) : False := by
  rw [h.response_owner r t hr] at hl
  cases hl

end PTX.Clc

namespace PTX

/-- In a complete execution that issues a cancellation request, the cluster of every launched
thread ran or was canceled by exactly one request. -/
theorem Complete.owner {L : Launch} {X : Execution} (hc : Complete L X) (hok : ClcOk L X)
    (hreq : ∃ i s targets, X.ClcIssue i s targets) {g : Nat} (hg : g < L.threads) :
    X.clcState.owner (L.clusterOfCta (g / L.block)) = some .launched ∨
      ∃ r, X.clcState.owner (L.clusterOfCta (g / L.block)) = some (.canceled r) ∧
        X.clcState.response r = some (some (L.clusterOfCta (g / L.block))) := by
  rcases hc.1 g hg with ⟨-, r, hr⟩ | ⟨pc, hl⟩
  · exact .inr ⟨r, hr, (Clc.owned_of_reachable hok.1).owner_response r _ hr⟩
  · refine .inl (hok.2.2.2.2 hreq g hg ?_)
    intro he
    rw [he] at hl
    cases hl

end PTX
