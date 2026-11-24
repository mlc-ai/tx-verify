-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.BlockSum.Proof.Interface

@[expose] public section

/-! # The events of the threads, by kind

From the thread facts: a read is a thread's input load (its first event) or, in thread 0 of a
CTA, the read of shared cell `i` (event `3 + i`); a write is a thread's store to its own shared
cell (its second event) or, in thread 0 of a CTA, the store of the sum of the cells it read to
`B[c]` (event 259); every barrier arrival is a thread's third event, on barrier `0` for the whole
CTA; an exit follows the barrier. -/

namespace PTX.Kernels.BlockSum.Proof

open PTX PTX.Proof PTX.Flow

noncomputable section

local notation "Prod" => [Assumptions.idealAdd]

variable {L : Launch} {A B : Nat} {x : Nat → ℝ} {mem0 : Mem0} {X : Execution}

/-- An event that is not undefined behaviour fires from a followed state. -/
theorem state_of_get (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩) : ∃ d, stateAt A B L X g k = some (some d) :=
  Frame.event_state (fun _ hg => sound hpre hg) hX ht.tracked he hub

/-- The state of an event, its site event, its position and invariant. -/
theorem event_facts (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩) :
    g < L.threads ∧ ∃ d, stateAt A B L X g k = some (some d) ∧ SiteEvent A B L g d e ∧
      k = d.idx g ∧ Inv d := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, hσ⟩ := state_of_get hpre hX ht he hub
  exact ⟨hg, d, hσ, ht.event hg he hσ, ht.index hg (len_of_get he).le hσ, ht.inv hg hσ⟩

/-- **A read** is a thread's input load, or a read of the reduction loop of thread 0 of a CTA. -/
theorem read_cases (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) {g k pc : Nat} {a : Acc} {bs : List (Option Byte)}
    (he : X.get (g, k) = some ⟨pc, .rd a bs⟩) :
    (k = 0 ∧ pc = Flow.load_0 ∧ a = { loc := gl (A + 4 * g), size := 4 }) ∨
    (g % 256 = 0 ∧ ∃ i < 256, k = 3 + i ∧ pc = Flow.load_1 ∧
      a = { loc := sh (g / 256) (L.sharedBase + 4 * i), size := 4 }) := by
  obtain ⟨hg, d, hσ, hev, hk, hi⟩ := event_facts hpre hX ht he (by intro _ _ h; cases h)
  obtain ⟨s, v, i, acc, sm⟩ := d
  cases s <;> simp only [SiteEvent] at hev
  · obtain ⟨bs', hev⟩ := hev
    simp only [Event.mk.injEq, Kind.rd.injEq] at hev
    exact .inl ⟨hk, hev.1, hev.2.1⟩
  · cases hev
  · cases hev
  · obtain ⟨bs', hev⟩ := hev
    simp only [Event.mk.injEq, Kind.rd.injEq] at hev
    exact .inr ⟨ht.reducer hg hσ (.inl rfl), i, (hi.sum rfl).1, hk, hev.1, hev.2.1⟩
  · cases hev
  · cases hev

/-- **A write** is a thread's store of its loaded input to its own shared cell, or the store of
the sum of the cells read to `B[c]` by thread 0 of a CTA. -/
theorem write_cases (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) {g k pc : Nat} {a : Acc} {bs : List Byte}
    (he : X.get (g, k) = some ⟨pc, .wr a bs⟩) :
    (k = 1 ∧ a = { loc := sh (g / 256) (L.sharedBase + 4 * (g % 256)), size := 4 } ∧
      ∃ v bs', X.get (g, 0) = some ⟨Flow.load_0, .rd { loc := gl (A + 4 * g), size := 4 } bs'⟩ ∧
        rebuild 3 bs' = .ok v ∧ bs = v.toBytes) ∨
    (g % 256 = 0 ∧ k = 259 ∧ a = { loc := gl (B + 4 * (g / 256)), size := 4 } ∧
      bs = (Assumption.erealValue .f32 (∑ j ∈ Finset.range 256,
        rdVal (X.get (g, 3 + j)))).toBytes) := by
  obtain ⟨hg, d, hσ, hev, hk, hi⟩ := event_facts hpre hX ht he (by intro _ _ h; cases h)
  obtain ⟨s, v, i, acc, sm⟩ := d
  cases s <;> simp only [SiteEvent] at hev
  · obtain ⟨bs', hev⟩ := hev
    cases hev
  · simp only [Event.mk.injEq, Kind.wr.injEq] at hev
    obtain ⟨bs', h0, hv⟩ := ht.input hg hσ (by simp)
    exact .inl ⟨hk, hev.2.1, v, bs', h0, hv, hev.2.2⟩
  · cases hev
  · obtain ⟨bs', hev⟩ := hev
    cases hev
  · simp only [Event.mk.injEq, Kind.wr.injEq] at hev
    have hs := ht.sum hg hσ (.inr rfl)
    have hi256 := (hi.out rfl).2
    simp only at hs hi256
    rw [hi256] at hs
    exact .inr ⟨ht.reducer hg hσ (.inr rfl), hk, hev.2.1, by rw [hev.2.2, hs]⟩
  · cases hev

/-- **A barrier arrival** is a thread's third event, on barrier `0` for the whole CTA. -/
theorem bar_cases (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) {g k id pc : Nat} {count : Option Nat}
    (he : X.IsBarrier (g, k) id count pc) :
    k = 2 ∧ id = 0 ∧ count = none ∧ pc = Flow.bar_0 := by
  obtain ⟨hg, d, hσ, hev, hk, hi⟩ := event_facts hpre hX ht he (by intro _ _ h; cases h)
  obtain ⟨s, v, i, acc, sm⟩ := d
  cases s <;> simp only [SiteEvent] at hev
  · obtain ⟨bs', hev⟩ := hev
    cases hev
  · cases hev
  · simp only [Event.mk.injEq, Kind.bar.injEq] at hev
    exact ⟨hk, hev.2.1, hev.2.2.1, hev.1⟩
  · obtain ⟨bs', hev⟩ := hev
    cases hev
  · cases hev
  · cases hev

/-- **An exit** follows the barrier. -/
theorem exit_index (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) {g k pc : Nat} (he : X.get (g, k) = some ⟨pc, .exit⟩) :
    3 ≤ k := by
  obtain ⟨hg, d, hσ, hev, hk, hi⟩ := event_facts hpre hX ht he (by intro _ _ h; cases h)
  obtain ⟨s, v, i, acc, sm⟩ := d
  cases s <;> simp only [SiteEvent] at hev
  · obtain ⟨bs', hev⟩ := hev
    cases hev
  · cases hev
  · cases hev
  · obtain ⟨bs', hev⟩ := hev
    cases hev
  · cases hev
  · simp only [D.idx] at hk
    split at hk <;> omega

/-- No thread performs a non-coherent read. -/
theorem no_nc (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) {e : EvId} {a : Acc} {bs : List (Option Byte)} :
    ¬ X.NcReads e a bs := by
  rintro ⟨pc, he⟩
  obtain ⟨hg, d, hσ, hev, hk, hi⟩ := event_facts hpre hX ht he (by intro _ _ h; cases h)
  obtain ⟨s, v, i, acc, sm⟩ := d
  cases s <;> simp only [SiteEvent] at hev
  · obtain ⟨bs', hev⟩ := hev
    cases hev
  · cases hev
  · cases hev
  · obtain ⟨bs', hev⟩ := hev
    cases hev
  · cases hev
  · cases hev

/-- A stopped machine stays stopped. -/
theorem stateAt_none_le {g j k : Nat} (hjk : j ≤ k) (h : stateAt A B L X g j = none) :
    stateAt A B L X g k = none := by
  induction k with
  | zero => obtain rfl : j = 0 := by omega
            exact h
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with hlt | hge
    · have hk := ih (by omega)
      show Frame.stateAt (codes A B L) X g (k + 1) = none
      cases he : (X.tr g)[k]? with
      | none =>
        have hl : (X.tr g).length ≤ k := by simpa using he
        rw [Frame.stateAt_of_le (by omega), ← Frame.stateAt_of_le hl]
        exact hk
      | some e =>
        rw [Frame.stateAt_succ he]
        change (stateAt A B L X g k).bind _ = none
        rw [hk]
        rfl
    · obtain rfl : j = k + 1 := by omega
      exact h

/-- **A thread with an event at `k`, not undefined behaviour, is followed up to `k`.** -/
theorem followed_before (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) {g j k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩) (hjk : j ≤ k) :
    ∃ d, stateAt A B L X g j = some (some d) := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, hσ⟩ := state_of_get hpre hX ht he hub
  cases hj : stateAt A B L X g j with
  | none => rw [stateAt_none_le hjk hj] at hσ; cases hσ
  | some σ =>
    cases σ with
    | none => exact absurd hj (ht.tracked g j hg)
    | some d' => exact ⟨d', rfl⟩

/-- **The event at a followed position is not undefined behaviour.** -/
theorem not_ub_of_followed (ht : ThreadFacts A B L X) {g k : Nat} (hg : g < L.threads)
    {d : D} (hσ : stateAt A B L X g k = some (some d)) {e : Event}
    (he : X.get (g, k) = some e) : ∀ pc f, e ≠ ⟨pc, .ub f⟩ := by
  rintro pc f rfl
  rw [ht.ub hg he] at hσ
  cases hσ

/-- **A thread with a later event than its barrier, not undefined behaviour, arrived at the
barrier** as its third event. -/
theorem bar_of_later (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) {g k : Nat} {e : Event} (he : X.get (g, k) = some e)
    (hub : ∀ pc f, e ≠ ⟨pc, .ub f⟩) (hk : 2 ≤ k) :
    X.IsBarrier (g, 2) 0 none Flow.bar_0 := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, hσ⟩ := followed_before hpre hX ht he hub hk
  obtain ⟨e2, he2⟩ : ∃ e, X.get (g, 2) = some e :=
    ⟨_, List.getElem?_eq_getElem (show 2 < (X.tr g).length by
      have := len_of_get he; simp only at this; omega)⟩
  obtain ⟨-, d', hσ', hev, hk', -⟩ :=
    event_facts hpre hX ht he2 (not_ub_of_followed ht hg hσ he2)
  obtain ⟨s, v, i, acc, sm⟩ := d'
  cases s with
  | bar =>
    simp only [SiteEvent] at hev
    rw [hev] at he2
    exact he2
  | exit => simp only [D.idx] at hk'; split at hk' <;> omega
  | input => simp only [D.idx] at hk'; omega
  | share => simp only [D.idx] at hk'; omega
  | sum => simp only [D.idx] at hk'; omega
  | out => simp only [D.idx] at hk'; omega

/-- **A thread that exits arrived at the barrier**, as its third event. -/
theorem bar_of_exit (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) {g k pc : Nat} (he : X.get (g, k) = some ⟨pc, .exit⟩) :
    X.IsBarrier (g, 2) 0 none Flow.bar_0 :=
  bar_of_later hpre hX ht he (by intro _ _ h; cases h)
    (by have := exit_index hpre hX ht he; omega)

/-- **A thread of an execution without undefined behaviour with three events arrived at the
barrier** as its third event. -/
theorem bar_at (hpre : Pre L A B x mem0) (hX : Consistent L kernel Prod mem0 X)
    (ht : ThreadFacts A B L X) (hub : ¬ HasUb X) {g : Nat} (hl : 3 ≤ (X.tr g).length) :
    X.IsBarrier (g, 2) 0 none Flow.bar_0 := by
  obtain ⟨e, he⟩ : ∃ e, X.get (g, 2) = some e :=
    ⟨_, List.getElem?_eq_getElem (show 2 < (X.tr g).length by omega)⟩
  exact bar_of_later hpre hX ht he (by rintro pc f rfl; exact hub ⟨_, pc, f, he⟩) le_rfl

end
end PTX.Kernels.BlockSum.Proof
