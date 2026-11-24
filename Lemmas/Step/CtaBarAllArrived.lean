-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.NamedBarLedger
public import Lemmas.Step.CtaBar

@[expose] public section

/-! # A generation in which every participant warp has arrived is released

A proof tool for named barriers whose participants may exit. Along a run of a CTA barrier
history, each record either keeps the generation of resource `id` and only adds to its arrived
set, or advances the generation by one (`perform_slot`, `run_slot`). So once a participant warp
has arrived in generation `G`, it stays in the arrived set until the generation advances. If
every participant warp of a group of `n` warps has a record in generation `G`, the arrived set
would hold all `n` of them, while a group's ledger keeps fewer than `n` arrived
(`Ledger.card_lt`): generation `G` is released (`released_of_all_arrived`). Exits of
participants do not matter, since an exit never removes a warp from the arrived set. -/

namespace PTX.CtaBarrier
open PTX NamedBar

variable {α : Type}

/-- **One record keeps the generation and adds arrivals, or advances the generation.** -/
theorem perform_slot {block id : Nat} {s t : State} {r : Record α}
    (h : r.perform block s = .ok t) :
    ((t.slots id).generation = (s.slots id).generation ∧
        (s.slots id).arrived ⊆ (t.slots id).arrived) ∨
      (t.slots id).generation = (s.slots id).generation + 1 := by
  cases r with
  | arrival id' w cnt lanes =>
    simp only [Record.perform] at h
    split_ifs at h
    obtain ⟨n, -, -, hslots⟩ := arrive_shape h
    rw [hslots id]
    split_ifs with hid
    · subst hid
      unfold settle
      split
      · exact .inr rfl
      · exact .inl ⟨rfl, Finset.subset_insert _ _⟩
    · exact .inl ⟨rfl, subset_refl _⟩
  | exit g e =>
    change exitThread block s g = .ok t at h
    unfold exitThread at h
    split_ifs at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      dsimp only
      unfold settle
      split
      · exact .inr rfl
      · exact .inl ⟨rfl, subset_refl _⟩
    · simp [bind, Except.bind, throw] at h

/-- **Along a run the generation grows, and the arrived set grows while it stays.** -/
theorem run_slot {block id : Nat} :
    ∀ {rs : List (Record α)} {s t : State}, run block s rs = .ok t →
      (s.slots id).generation ≤ (t.slots id).generation ∧
        ((t.slots id).generation = (s.slots id).generation →
          (s.slots id).arrived ⊆ (t.slots id).arrived)
  | [], s, t, h => by
    simp only [run, Except.ok.injEq] at h
    subst h
    exact ⟨le_refl _, fun _ => subset_refl _⟩
  | r :: rs, s, t, h => by
    cases hu : r.perform block s with
    | error err => simp [run, hu, Except.bind] at h
    | ok u =>
      have hr : run block u rs = .ok t := by simpa only [run, hu, Except.bind] using h
      obtain ⟨h1, h2⟩ := run_slot (id := id) hr
      rcases perform_slot (id := id) hu with ⟨hg, hs⟩ | hg
      · exact ⟨by omega, fun he => hs.trans (h2 (by omega))⟩
      · exact ⟨by omega, fun he => by omega⟩

/-- **A generation in which every participant warp has a record is released.** Let a checked
history follow the protocol of a group `p` of `n` warps on resource `id`, and let every warp of
`p` have an arrival record on `id` performed in generation `G`. Then generation `G` is
released. -/
theorem released_of_all_arrived {block n : Nat} {count : Option Nat} {p : Finset Nat}
    {id G : Nat} {h : List (Record α)} {u : State} (hp : Protocol count p id h) (hn : 0 < n)
    (hcount : target block count = .ok n) (hcard : p.card = n)
    (hbound : ∀ w ∈ p, w < block / 32) (hr : run block {} h = .ok u)
    (hall : ∀ w ∈ p, ∃ i lanes s, h[i]? = some (.arrival id w count lanes) ∧
      At block h i s ∧ (s.slots id).generation = G) :
    Released block h id G := by
  by_contra hrel
  have hle : (u.slots id).generation ≤ G := by
    by_contra hlt
    exact hrel (Step.CtaBar.released_of_generation_lt hr (by omega))
  have hsub : p ⊆ (u.slots id).arrived := by
    intro w hw
    obtain ⟨i, lanes, s, hi, hs, hgen⟩ := hall w hw
    have hlt := (List.getElem?_eq_some_iff.mp hi).1
    have hd : h = h.take i ++ (Record.arrival id w count lanes) :: h.drop (i + 1) := by
      rw [← (List.getElem?_eq_some_iff.mp hi).2, ← List.drop_eq_getElem_cons hlt]
      exact (List.take_append_drop i h).symm
    have hr' := hr
    rw [hd, run_append] at hr'
    unfold At at hs
    rw [hs] at hr'
    simp only [Except.bind] at hr'
    cases ht : (Record.arrival id w count lanes : Record α).perform block s with
    | error err => simp [run, ht, Except.bind] at hr'
    | ok t =>
      have hrest : run block t (h.drop (i + 1)) = .ok u := by
        simpa only [run, ht, Except.bind] using hr'
      obtain ⟨hmono, hkeep⟩ := run_slot (id := id) hrest
      have hperf : arrive block s id w count = .ok t := by
        have hh := ht
        simp only [Record.perform] at hh
        split_ifs at hh
        exact hh
      obtain ⟨m, -, -, hslots⟩ := arrive_shape hperf
      have hslot := hslots id
      simp only [↓reduceIte] at hslot
      unfold settle at hslot
      split at hslot
      · rw [hslot] at hmono
        simp only at hmono
        omega
      · have htg : (t.slots id).generation = G := by rw [hslot]; exact hgen
        have hwt : w ∈ (t.slots id).arrived := by rw [hslot]; exact Finset.mem_insert_self _ _
        exact hkeep (by omega) hwt
  have hl := hp.run_ledger hn hcount hcard hbound hr
  have := Finset.card_le_card hsub
  have := hl.card_lt
  omega

end PTX.CtaBarrier
