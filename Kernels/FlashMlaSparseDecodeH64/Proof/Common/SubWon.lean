-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Common.RoleLane

@[expose] public section

/-! # A lane with an event of a sub-role's code after its election won it

The sub-role-independent part of "a lane of warpgroup 1's MMA or TMA warp with an event after the
election won it, and stays in the sub-role": the thread machine never leaves the idle code or a
stub (`IdleR`, `idle_next`) nor a region of a sub-role `j` kept by `j`'s steps without a hand-back
(`SubR`, `sub_next`), and a region it does not leave holds at every later state
(`region_stays`). So a lane whose election step at index `j` would enter the idle region, but that
is outside it at a later index, is the election's leader (`won_of`). A sub-role's instance
(`Common/MmaWon.lean`) supplies its election count, the shape of its election event, its losing
step and the step fact that keeps its post-election region (`Mma.succ_post`). -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof
open PTX PTX.Proof PTX.Flow MbarRow

noncomputable section

variable {P : Params} {L : Launch} {m : Mem0} {X : Execution} {g k : Nat} {e : Event}

/-- The idle region of the thread machine: warpgroup 1's idle code or a stub. -/
def IdleR : (thread P L g).D → Prop
  | (.inr ⟨.inl .wg1, .inr ⟨.inl .idle, _⟩⟩, _) => True
  | (.inr ⟨.inl .wg1, .inr ⟨.inr _, _⟩⟩, _) => True
  | (.inr ⟨.inr _, _⟩, _) => True
  | _ => False

/-- **The thread machine stays in the idle region.** -/
theorem idle_next {σ σ' : (thread P L g).D} (h : IdleR σ) {f : Event}
    (hn : (thread P L g).toMachine.next (some σ) f = some (some σ')) : IdleR σ' := by
  obtain ⟨s, n⟩ := σ
  rcases s with d | ⟨i | r, d'⟩
  · exact h.elim
  · cases i with
    | wg1 =>
      rcases d' with s | ⟨j | r, d⟩
      · exact h.elim
      · cases j with
        | idle =>
          simp only [Code.toMachine, Code.glue] at hn
          simp at hn
          obtain ⟨a, -, rfl⟩ := hn
          simp [Code.backEnter, subBack, IdleR]
        | _ => exact h.elim
      · simp [Code.toMachine] at hn
    | _ => exact h.elim
  · simp [Code.toMachine] at hn

/-- **A region the thread's steps keep**: from a state in it at index `j`, every later state of
the thread is in it, when each step of the thread from index `j` on (from a state in the region,
on the thread's event there) keeps it. -/
theorem region_stays_ev (R : (thread P L g).D → Prop) {j : Nat}
    (hc : ∀ {i : Nat} {σ σ' : (thread P L g).D} {f : Event}, j ≤ i →
      Frame.stateAt (thread P L) X g i = some (some σ) → R σ → (X.tr g)[i]? = some f →
      (thread P L g).toMachine.next (some σ) f = some (some σ') → R σ')
    {σ : (thread P L g).D}
    (hj : Frame.stateAt (thread P L) X g j = some (some σ)) (hI : R σ) :
    ∀ i, j ≤ i → ∀ σ', Frame.stateAt (thread P L) X g i = some (some σ') → R σ' := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base =>
    intro σ' h
    rw [hj] at h
    cases h
    exact hI
  | succ i hji ih =>
    intro σ' h
    cases hg : (X.tr g)[i]? with
    | none =>
      have hl : (X.tr g).length ≤ i := List.getElem?_eq_none_iff.mp hg
      rw [Frame.stateAt_of_le (by omega), ← Frame.stateAt_of_le hl] at h
      exact ih σ' h
    | some f =>
      rw [Frame.stateAt_succ hg] at h
      cases hi : Frame.stateAt (thread P L) X g i with
      | none => simp [hi] at h
      | some o =>
        rw [hi] at h
        cases o with
        | none => simp [Code.toMachine] at h
        | some σ0 => exact hc hji hi (ih σ0 hi) hg h

/-- **A region the thread machine does not leave**: from a state in it, every later state of
the thread is in it. -/
theorem region_stays (R : (thread P L g).D → Prop)
    (hc : ∀ {σ σ' : (thread P L g).D}, R σ → ∀ {f : Event},
      (thread P L g).toMachine.next (some σ) f = some (some σ') → R σ')
    {j : Nat} {σ : (thread P L g).D}
    (hj : Frame.stateAt (thread P L) X g j = some (some σ)) (hI : R σ) :
    ∀ i, j ≤ i → ∀ σ', Frame.stateAt (thread P L) X g i = some (some σ') → R σ' :=
  region_stays_ev R (fun _ _ hR _ hn => hc hR hn) hj hI

/-- An event of the lane's first `k` is an event of the lane before `k`. -/
theorem get_lt_of_mem_take {f : Event} (hf : f ∈ (X.tr g).take k) :
    ∃ j < k, X.get (g, j) = some f := by
  obtain ⟨j, hj, hfj⟩ := List.getElem_of_mem hf
  have hjk : j < k := by simp only [List.length_take] at hj; omega
  refine ⟨j, hjk, ?_⟩
  show (X.tr g)[j]? = some f
  rw [← List.getElem?_take_of_lt hjk, List.getElem?_eq_getElem hj, hfj]

/-- **A region of sub-role `j`**: its states with `Q`. -/
def SubR (j : SubEntry) (Q : (subFrag P L g j).D → Prop) (σ : (thread P L g).D) : Prop :=
  ∃ d n, σ = (.inr ⟨.inl .wg1, .inr ⟨.inl j, d⟩⟩, n) ∧ Q d

/-- **A step of sub-role `j`** that hands nothing back stays in `j`'s code. -/
theorem sub_step {j : SubEntry} {d : (subFrag P L g j).D} {n : Cls → Nat} {f : Event}
    {σ' : (thread P L g).D}
    (hn : (thread P L g).toMachine.next (some (.inr ⟨.inl .wg1, .inr ⟨.inl j, d⟩⟩, n)) f =
      some (some σ'))
    (hb : ∀ a, (Code.withStubsAt (subFrag P L g) (SubEntry.pc P L g) (Sum.inl j)).next d f =
      some (some a) → subBack P L g j a = none) :
    ∃ a, (Code.withStubsAt (subFrag P L g) (SubEntry.pc P L g) (Sum.inl j)).next d f =
      some (some a) ∧ σ' = (.inr ⟨.inl .wg1, .inr ⟨.inl j, a⟩⟩, Code.bump cls n f) := by
  simp only [Code.toMachine, Code.glue] at hn
  simp at hn
  obtain ⟨a, ha, rfl⟩ := hn
  exact ⟨a, ha, by simp [Code.backEnter, hb a ha]⟩

/-- **The thread machine stays in a region of sub-role `j`** whose steps keep `Q` and hand
nothing back. -/
theorem sub_next {j : SubEntry} {Q : (subFrag P L g j).D → Prop}
    (hQ : ∀ {d a : (subFrag P L g j).D} {f : Event}, Q d →
      (Code.withStubsAt (subFrag P L g) (SubEntry.pc P L g) (Sum.inl j)).next d f =
        some (some a) → Q a ∧ subBack P L g j a = none)
    {σ σ' : (thread P L g).D} (h : SubR j Q σ) {f : Event}
    (hn : (thread P L g).toMachine.next (some σ) f = some (some σ')) : SubR j Q σ' := by
  obtain ⟨d, n, rfl, hd⟩ := h
  obtain ⟨a, ha, rfl⟩ := sub_step hn fun a ha => (hQ hd ha).2
  exact ⟨a, _, rfl, (hQ hd ha).1⟩

/-- **A lane outside the idle region after its election step won the election**: if the step at
index `j` (an election with leader `ld`) enters the idle region unless the lane is the leader,
and the lane's state at a later index `k` is outside it, the lane is the leader. -/
theorem won_of {j : Nat} {pc mk inst ld : Nat} {σj σ : (thread P L g).D}
    (hj : X.get (g, j) = some ⟨pc, .elect mk inst ld⟩) (hjk : j < k)
    (hσj : Frame.stateAt (thread P L) X g j = some (some σj))
    (hσ : Frame.stateAt (thread P L) X g k = some (some σ)) (hout : ¬ IdleR σ)
    (hnone : (thread P L g).toMachine.next (some σj) ⟨pc, .elect mk inst ld⟩ ≠ some none)
    (hlose : PTX.laneOf L g ≠ ld → ∀ σ1,
      (thread P L g).toMachine.next (some σj) ⟨pc, .elect mk inst ld⟩ = some (some σ1) →
        IdleR σ1) :
    PTX.laneOf L g = ld := by
  by_contra hld
  have hn : Frame.stateAt (thread P L) X g (j + 1) =
      (thread P L g).toMachine.next (some σj) ⟨pc, .elect mk inst ld⟩ := by
    rw [Frame.stateAt_succ hj, hσj]
    rfl
  cases hn' : (thread P L g).toMachine.next (some σj) ⟨pc, .elect mk inst ld⟩ with
  | none =>
    rw [hn'] at hn
    have := Frame.stateAt_none_mono hn (show j + 1 ≤ k by omega)
    rw [hσ] at this
    cases this
  | some o =>
    cases o with
    | none => exact hnone hn'
    | some σ1 =>
      rw [hn'] at hn
      exact hout (region_stays IdleR idle_next hn (hlose hld σ1 hn') k (by omega) _ hσ)

end
end PTX.Kernels.FlashMlaSparseDecodeH64.Proof
