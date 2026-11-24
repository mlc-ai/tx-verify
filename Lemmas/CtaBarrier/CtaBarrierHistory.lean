-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Sync.CtaBarrierObject
public import Core.Sync.CtaBarrierHistory

@[expose] public section

section
namespace PTX.CtaBarrier

/-- Each resource completion advances exactly one generation and clears arrivals. -/
theorem settle_complete {block : Nat} {exited : Finset Nat} {s : Slot}
    (h : complete block exited s = true) :
    settle block exited s = { generation := s.generation + 1 } := by
  simp [settle, h]

theorem settle_pending {block : Nat} {exited : Finset Nat} {s : Slot}
    (h : complete block exited s = false) : settle block exited s = s := by
  simp [settle, h]

/-- There is no implicit phase-zero restriction or skipped generation. -/
theorem settle_generation (block : Nat) (exited : Finset Nat) (s : Slot) :
    (settle block exited s).generation = s.generation ∨
    (settle block exited s).generation = s.generation + 1 := by
  unfold settle
  split <;> simp

/-- A resource completed by its requested arrivals does not depend on other warps. -/
theorem complete_of_count {block n : Nat} {exited : Finset Nat} {s : Slot}
    (he : s.expected = some n) (hc : n ≤ s.arrived.card) :
    complete block exited s = true := by
  simp [complete, he, hc]

end PTX.CtaBarrier
end

section
namespace PTX.CtaBarrier

variable {α : Type}

theorem run_append (block : Nat) (s : State) (xs ys : List (Record α)) :
    run block s (xs ++ ys) = (run block s xs).bind (fun t => run block t ys) := by
  induction xs generalizing s with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.cons_append, run]
    cases h : r.perform block s with
    | error e => rfl
    | ok t => exact ih t

/-- Every prefix of a successful history is itself a successful object history. -/
theorem run_prefix {block : Nat} {s t : State} {xs ys : List (Record α)}
    (h : run block s (xs ++ ys) = .ok t) : ∃ u, run block s xs = .ok u := by
  cases hx : run block s xs with
  | error e =>
    have hb : run block s (xs ++ ys) = .error e := by
      rw [run_append, hx]
      rfl
    rw [hb] at h
    cases h
  | ok u => exact ⟨u, rfl⟩

/-- Appending records cannot change a source arrival's already assigned generation. -/
theorem GenerationOf.append {block id phase : Nat} {xs ys : List (Record α)} {e : α}
    (h : GenerationOf block xs e id phase) : GenerationOf block (xs ++ ys) e id phase := by
  obtain ⟨i, s, w, count, lanes, g, hi, hs, he, hg, hn⟩ := h
  have hlt : i < xs.length := (List.getElem?_eq_some_iff.mp hi).1
  refine ⟨i, s, w, count, lanes, g, ?_, ?_, he, hg, hn⟩
  · rwa [List.getElem?_append_left hlt]
  · unfold At at hs ⊢
    rwa [List.take_append_of_le_length hlt.le]

theorem CompletesAt.append {block i id phase : Nat} {xs ys : List (Record α)}
    (h : CompletesAt block xs i id phase) : CompletesAt block (xs ++ ys) i id phase := by
  obtain ⟨r, s, t, hi, hs, hr, hp, hq⟩ := h
  have hlt : i < xs.length := (List.getElem?_eq_some_iff.mp hi).1
  refine ⟨r, s, t, ?_, ?_, hr, hp, hq⟩
  · rwa [List.getElem?_append_left hlt]
  · unfold At at hs ⊢
    rwa [List.take_append_of_le_length hlt.le]

theorem Released.append {block id phase : Nat} {xs ys : List (Record α)}
    (h : Released block xs id phase) : Released block (xs ++ ys) id phase := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, hi.append⟩

end PTX.CtaBarrier
end
