-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.NamedBarPhase
public import Lemmas.Step.CtaBarFinishExit

@[expose] public section

/-!
# Releasing a generation of a phased barrier from its arrivals (generic part)

The library version of Inkling's `Proof2/Lib/WfReleaseBase.lean`, in the namespace
`NamedBar.GenLedger`: `perform_expected`, `run_expected` (an open generation's `expected` count
stays while its generation is unchanged), `arrive_pending`, `released_of_group` (a generation in
which every warp of a group arrived with the count that targets the group is released, in a
history with the phased ledger of `Lemmas/Protocol/NamedBarPhase.lean`).
-/

namespace PTX.NamedBar.GenLedger
open PTX CtaBarrier

noncomputable section

variable {α : Type}

/-- **One update keeps an open generation's expected count while the generation is the
same.** -/
theorem perform_expected {block id : Nat} {r : Record α} {s t : State}
    (h : r.perform block s = .ok t) (hg : (t.slots id).generation = (s.slots id).generation)
    {k : Nat} (hk : (s.slots id).expected = some k) : (t.slots id).expected = some k := by
  cases r with
  | arrival id' w cnt lanes =>
    simp only [Record.perform] at h
    split_ifs at h
    obtain ⟨-, -, -, -, n, hn, hexp⟩ := arrive_ok_info h
    obtain ⟨n', hn', -, hslots⟩ := arrive_shape h
    have hnn : n' = n := Except.ok.inj (hn'.symm.trans hn)
    subst hnn
    have hs := hslots id
    by_cases hid : id = id'
    · subst hid
      simp only [↓reduceIte] at hs
      have hkn : k = n' := hexp k hk
      subst hkn
      by_cases hc : complete block s.exited
          {s.slots id with expected := some k, arrived := insert w (s.slots id).arrived} = true
      · rw [settle_complete hc] at hs
        rw [hs] at hg
        simp only at hg
        omega
      · have hc' : complete block s.exited
            {s.slots id with expected := some k, arrived := insert w (s.slots id).arrived} =
              false := by simpa using hc
        rw [settle_pending hc'] at hs
        rw [hs]
    · simp only [hid, ↓reduceIte] at hs
      rw [hs]
      exact hk
  | exit g e =>
    change exitThread block s g = .ok t at h
    unfold exitThread at h
    split_ifs at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      dsimp only at hg ⊢
      by_cases hc : complete block (insert g s.exited) (s.slots id) = true
      · rw [settle_complete hc] at hg
        simp only at hg
        omega
      · have hc' : complete block (insert g s.exited) (s.slots id) = false := by simpa using hc
        rw [settle_pending hc']
        exact hk
    · simp [bind, Except.bind, throw] at h

/-- **Along a run an open generation's expected count stays while the generation does.** -/
theorem run_expected {block id : Nat} :
    ∀ {rs : List (Record α)} {s t : State}, CtaBarrier.run block s rs = .ok t →
      (t.slots id).generation = (s.slots id).generation → ∀ {k : Nat},
        (s.slots id).expected = some k → (t.slots id).expected = some k
  | [], s, t, h, _, k, hk => by
    simp only [CtaBarrier.run, Except.ok.injEq] at h
    subst h
    exact hk
  | r :: rs, s, t, h, hg, k, hk => by
    cases hu : r.perform block s with
    | error err => simp [CtaBarrier.run, hu, Except.bind] at h
    | ok u =>
      have hr : CtaBarrier.run block u rs = .ok t := by
        simpa only [CtaBarrier.run, hu, Except.bind] using h
      obtain ⟨h1, -⟩ := CtaBarrier.run_slot (id := id) hr
      have hug : (u.slots id).generation = (s.slots id).generation := by
        rcases CtaBarrier.perform_slot (id := id) hu with ⟨hg', -⟩ | hg'
        · exact hg'
        · omega
      exact run_expected hr (by omega) (perform_expected hu hug hk)

/-- A pending arrival of warp `w` in an open generation: after it the slot has expected `n`
and `w` arrived, in the same generation. -/
theorem arrive_pending {block id w n : Nat} {cnt : Option Nat} {s t : State}
    (h : arrive block s id w cnt = .ok t) (hn : target block cnt = .ok n)
    (hg : (t.slots id).generation = (s.slots id).generation) :
    (t.slots id).expected = some n ∧ w ∈ (t.slots id).arrived := by
  obtain ⟨n', hn', -, hslots⟩ := arrive_shape h
  have hnn : n' = n := Except.ok.inj (hn'.symm.trans hn)
  subst hnn
  have hs := hslots id
  simp only [↓reduceIte] at hs
  by_cases hc : complete block s.exited
      {s.slots id with expected := some n', arrived := insert w (s.slots id).arrived} = true
  · rw [settle_complete hc] at hs
    rw [hs] at hg
    simp only at hg
    omega
  · have hc' : complete block s.exited
        {s.slots id with expected := some n', arrived := insert w (s.slots id).arrived} =
          false := by simpa using hc
    rw [settle_pending hc'] at hs
    rw [hs]
    exact ⟨rfl, Finset.mem_insert_self _ _⟩

/-- **A generation in which every warp of a group has arrived is released**, in a history whose
final state has the phased ledger. Let `P` be `n` warps, `cnt` an operand that targets `n`, and
let every warp of `P` have an arrival record with operand `cnt` performed in generation `G`.
Then `G` is released: otherwise the final open generation would have expected count `n` and every
warp of `P` arrived, while the ledger keeps fewer than `n` arrived. -/
theorem released_of_group {block nD start id n G : Nat} {D : Finset Nat} {cnt : Option Nat}
    {counts : Nat → Nat} {P : Finset Nat} {h : List (Record α)} {u : State}
    (hr : CtaBarrier.run block {} h = .ok u) (hl : Phased block D nD start id counts u)
    (hn : target block cnt = .ok n) (hcard : P.card = n) (hpos : 0 < n)
    (hall : ∀ w ∈ P, ∃ i lanes s, h[i]? = some (.arrival id w cnt lanes) ∧
      At block h i s ∧ (s.slots id).generation = G) : Released block h id G := by
  by_contra hrel
  have hle : (u.slots id).generation ≤ G := by
    by_contra hlt
    exact hrel (Step.CtaBar.released_of_generation_lt (phase := G) hr (by omega))
  -- every warp of `P` has arrived in the open generation, which expects `n`
  have key : ∀ w ∈ P, w ∈ (u.slots id).arrived ∧ (u.slots id).expected = some n := by
    intro w hw
    obtain ⟨i, lanes, s, hi, hs, hgen⟩ := hall w hw
    have hlt := (List.getElem?_eq_some_iff.mp hi).1
    have hd : h = h.take i ++ (Record.arrival id w cnt lanes) :: h.drop (i + 1) := by
      rw [← (List.getElem?_eq_some_iff.mp hi).2, ← List.drop_eq_getElem_cons hlt]
      exact (List.take_append_drop i h).symm
    have hr' := hr
    rw [hd, CtaBarrier.run_append] at hr'
    unfold At at hs
    rw [hs] at hr'
    simp only [Except.bind] at hr'
    cases ht : (Record.arrival id w cnt lanes : Record α).perform block s with
    | error err => simp [CtaBarrier.run, ht, Except.bind] at hr'
    | ok t =>
      have hrest : CtaBarrier.run block t (h.drop (i + 1)) = .ok u := by
        simpa only [CtaBarrier.run, ht, Except.bind] using hr'
      obtain ⟨hmono, hkeep⟩ := CtaBarrier.run_slot (id := id) hrest
      have hperf : arrive block s id w cnt = .ok t := by
        have hh := ht
        simp only [Record.perform] at hh
        split_ifs at hh
        exact hh
      have htg : (t.slots id).generation = G := by
        rcases CtaBarrier.perform_slot (id := id) ht with ⟨hg', -⟩ | hg'
        · rw [hg', hgen]
        · exfalso
          have := hg'
          omega
      have hug : (u.slots id).generation = (t.slots id).generation := by omega
      obtain ⟨hex, hwt⟩ := arrive_pending hperf hn (by rw [htg, hgen])
      exact ⟨hkeep hug hwt, run_expected hrest hug hex⟩
  obtain ⟨w0, hw0⟩ : P.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨-, hexp⟩ := key w0 hw0
  have hcl := (hl.some_info n hexp).2.1
  have hsub : P ⊆ (u.slots id).arrived := fun w hw => (key w hw).1
  have := Finset.card_le_card hsub
  omega


end
end PTX.NamedBar.GenLedger
