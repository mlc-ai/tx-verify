-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof2.Lib.WfReleaseBase
public import Lemmas.Protocol.NamedBarSources

@[expose] public section

/-!
# What a completed generation of a barrier has recorded (promotion candidate)

Two facts about a history of a CTA's barrier resource that the library does not state:

* `arrived_owned`: every warp in the `arrived` set of a slot has an arrival record on the barrier
  in the slot's current generation;
* `completion_arrivals`: if a generation `φ` of a barrier whose arrivals all request the whole
  CTA (`n = warps block`) is released, and a warp's record is performed in it, then every warp that
  is live at the completion has a record in `φ`.
-/

namespace PTX.NamedBar
open PTX CtaBarrier

noncomputable section

variable {α : Type}

/-- **Every warp in a slot's arrived set has a record in the slot's current generation.** -/
theorem arrived_owned {block id : Nat} :
    ∀ {h : List (Record α)} {s : State}, CtaBarrier.run block {} h = .ok s →
      ∀ w ∈ (s.slots id).arrived, ∃ i cnt lanes s', h[i]? = some (.arrival id w cnt lanes) ∧
        At block h i s' ∧ (s'.slots id).generation = (s.slots id).generation := by
  intro h
  induction h using List.reverseRecOn with
  | nil =>
    intro s hr w hw
    simp only [CtaBarrier.run, Except.ok.injEq] at hr
    subst hr
    simp at hw
  | @append_singleton xs r ih =>
    intro s hr w hw
    rw [CtaBarrier.run_append] at hr
    cases hx : CtaBarrier.run block {} xs with
    | error err => simp [hx, Except.bind] at hr
    | ok u =>
      have hp : r.perform block u = .ok s := by
        have h1 : CtaBarrier.run block u [r] = .ok s := by simpa [hx, Except.bind] using hr
        cases hq : r.perform block u with
        | error err => simp [CtaBarrier.run, hq, Except.bind] at h1
        | ok v => simpa [CtaBarrier.run, hq, Except.bind] using h1
      -- carry a witness of the old history to the longer one
      have carry : ∀ {i cnt lanes s'}, xs[i]? = some (.arrival id w cnt lanes) →
          At block xs i s' → (xs ++ [r])[i]? = some (.arrival id w cnt lanes) ∧
            At block (xs ++ [r]) i s' := by
        intro i cnt lanes s' hi hs
        have hlt := (List.getElem?_eq_some_iff.mp hi).1
        refine ⟨by rw [List.getElem?_append_left hlt]; exact hi, ?_⟩
        unfold At at hs ⊢
        rw [List.take_append_of_le_length hlt.le]
        exact hs
      have hAtEnd : At block (xs ++ [r]) xs.length u := by
        unfold At
        rw [List.take_left]
        exact hx
      cases r with
      | arrival id' w' cnt lanes =>
        simp only [Record.perform] at hp
        split_ifs at hp with hl
        obtain ⟨n, hn, -, hslots⟩ := arrive_shape hp
        by_cases hid : id = id'
        · subst hid
          have hs1 : s.slots id = settle block u.exited
              {u.slots id with expected := some n, arrived := insert w' (u.slots id).arrived} := by
            simpa only [↓reduceIte] using hslots id
          by_cases hc :
              complete block u.exited
                {u.slots id with expected := some n, arrived := insert w' (u.slots id).arrived} =
                  true
          · rw [settle_complete hc] at hs1
            rw [hs1] at hw
            simp at hw
          · have hc' : complete block u.exited
                {u.slots id with expected := some n, arrived := insert w' (u.slots id).arrived} =
                  false := by simpa using hc
            rw [settle_pending hc'] at hs1
            rw [hs1] at hw ⊢
            simp only [Finset.mem_insert] at hw
            rcases hw with rfl | hw
            · exact ⟨xs.length, cnt, lanes, u, by simp, hAtEnd, rfl⟩
            · obtain ⟨i, cnt', lanes', s', hi, hs', hgen⟩ := ih hx w hw
              obtain ⟨h1, h2⟩ := carry hi hs'
              exact ⟨i, cnt', lanes', s', h1, h2, hgen⟩
        · have hs1 : s.slots id = u.slots id := by simpa only [hid, ↓reduceIte] using hslots id
          rw [hs1] at hw ⊢
          obtain ⟨i, cnt', lanes', s', hi, hs', hgen⟩ := ih hx w hw
          obtain ⟨h1, h2⟩ := carry hi hs'
          exact ⟨i, cnt', lanes', s', h1, h2, hgen⟩
      | exit g e =>
        change exitThread block u g = .ok s at hp
        unfold exitThread at hp
        split_ifs at hp
        · simp only [pure, Except.pure, Except.ok.injEq] at hp
          subst hp
          dsimp only at hw ⊢
          by_cases hc : complete block (insert g u.exited) (u.slots id) = true
          · rw [settle_complete hc] at hw
            simp at hw
          · have hc' : complete block (insert g u.exited) (u.slots id) = false := by
              simpa using hc
            rw [settle_pending hc'] at hw ⊢
            obtain ⟨i, cnt', lanes', s', hi, hs', hgen⟩ := ih hx w hw
            obtain ⟨h1, h2⟩ := carry hi hs'
            exact ⟨i, cnt', lanes', s', h1, h2, hgen⟩
        · simp [bind, Except.bind, throw] at hp

/-- The records between two prefixes of a history run from the first state to the second. -/
theorem run_between {block i j : Nat} {h : List (Record α)} {s t : State} (hij : i ≤ j)
    (hi : At block h i s) (hj : At block h j t) :
    CtaBarrier.run block s ((h.take j).drop i) = .ok t := by
  have hd : h.take j = h.take i ++ (h.take j).drop i := by
    calc
      h.take j = (h.take j).take i ++ (h.take j).drop i := (List.take_append_drop i _).symm
      _ = h.take i ++ (h.take j).drop i := by rw [List.take_take, Nat.min_eq_left hij]
  unfold At at hi hj
  rw [hd, CtaBarrier.run_append, hi] at hj
  simpa [Except.bind] using hj

/-- The generation of a slot does not decrease from one prefix to a later one. -/
theorem at_gen_mono {block i j id : Nat} {h : List (Record α)} {s t : State} (hij : i ≤ j)
    (hi : At block h i s) (hj : At block h j t) :
    (s.slots id).generation ≤ (t.slots id).generation := by
  have h1 := run_between hij hi hj
  exact (CtaBarrier.run_slot (id := id) h1).1

/-- The state after record `i` of a history. -/
theorem at_succ {block i : Nat} {h : List (Record α)} {r : Record α} {s t : State}
    (hi : h[i]? = some r) (hs : At block h i s) (ht : r.perform block s = .ok t) :
    At block h (i + 1) t := by
  unfold At at hs ⊢
  rw [List.take_add_one, hi, CtaBarrier.run_append, hs]
  simp [CtaBarrier.run, ht, Except.bind]

/-- **A released generation of a barrier that requests the whole CTA has a record of every live
warp.** Let a record of some warp be performed in generation `φ` with an operand that targets
all warps, and let `φ` be released. Then every warp that is live after the completing record has
an arrival record performed in `φ`. `howners`: arrived warps of every state are warps of the
CTA (the phased ledger's `owners`). -/
theorem completion_arrivals {block id φ : Nat} {h : List (Record α)} {u : State}
    (hr : CtaBarrier.run block {} h = .ok u)
    (howners : ∀ i s, At block h i s → (s.slots id).arrived ⊆ Finset.range (warps block))
    {i' w' : Nat} {cnt : Option Nat} {lanes' : List (Nat × α)} {s' : State}
    (hi' : h[i']? = some (.arrival id w' cnt lanes')) (hs' : At block h i' s')
    (hg' : (s'.slots id).generation = φ) (hn : target block cnt = .ok (warps block))
    (hrel : Released block h id φ) :
    ∃ ic t, At block h (ic + 1) t ∧
      ∀ w ∈ Finset.range (warps block), warpLive block t.exited w →
      ∃ i cnt lanes s, h[i]? = some (.arrival id w cnt lanes) ∧ At block h i s ∧
        (s.slots id).generation = φ := by
  obtain ⟨ic, r, s, t, hric, hAtic, hperf, hgs, hgt⟩ := hrel
  have hAtt : At block h (ic + 1) t := at_succ hric hAtic hperf
  have hle : i' ≤ ic := by
    by_contra hlt
    have := at_gen_mono (id := id) (by omega : ic + 1 ≤ i') hAtt hs'
    omega
  -- a warp in the arrived set of the completing slot has a record in `φ`
  have own : ∀ w ∈ (s.slots id).arrived, ∃ i cnt lanes s₁,
      h[i]? = some (.arrival id w cnt lanes) ∧
      At block h i s₁ ∧ (s₁.slots id).generation = φ := by
    intro w hw
    obtain ⟨i, cnt₁, lanes₁, s₁, hi₁, hs₁, hgen⟩ :=
      arrived_owned (id := id) hAtic w hw
    have hlt := (List.getElem?_eq_some_iff.mp hi₁).1
    simp only [List.length_take] at hlt
    refine ⟨i, cnt₁, lanes₁, s₁, ?_, ?_, by rw [hgen, hgs]⟩
    · rw [List.getElem?_take_of_lt (by omega)] at hi₁
      exact hi₁
    · unfold At at hs₁ ⊢
      rw [List.take_take, Nat.min_eq_left (by omega)] at hs₁
      exact hs₁
  -- the expected count of the completing slot
  have hexp : i' < ic → (s.slots id).expected = some (warps block) := by
    intro hlt
    obtain ⟨s₂, t₂, hat₂, hp₂⟩ := run_at_record hr hi'
    have hss : s₂ = s' := Except.ok.inj ((show CtaBarrier.run block {} (h.take i') = .ok s₂
      from hat₂).symm.trans hs')
    subst hss
    have hAt₂ := at_succ hi' hs' hp₂
    have hg₂ : (t₂.slots id).generation = φ := by
      have h1 := at_gen_mono (id := id) (by omega : i' + 1 ≤ ic) hAt₂ hAtic
      rcases CtaBarrier.perform_slot (id := id) hp₂ with ⟨h2, -⟩ | h2 <;> omega
    have hperf₂ : arrive block s₂ id w' cnt = .ok t₂ := by
      simp only [Record.perform] at hp₂
      split_ifs at hp₂
      exact hp₂
    obtain ⟨hex, -⟩ := arrive_pending hperf₂ hn (by omega)
    exact run_expected (run_between (by omega : i' + 1 ≤ ic) hAt₂ hAtic) (by omega) hex
  cases r with
  | arrival b v cntc lanesc =>
    simp only [Record.perform] at hperf
    split_ifs at hperf with hl
    obtain ⟨-, hwb, -, -, nc, hnc, hexpc⟩ := arrive_ok_info hperf
    obtain ⟨nc', hnc', hexit, hslots⟩ := arrive_shape hperf
    have hnn : nc' = nc := Except.ok.inj (hnc'.symm.trans hnc)
    subst hnn
    by_cases hid : b = id
    · subst hid
      have hs1 : t.slots b = settle block s.exited
          {s.slots b with expected := some nc', arrived := insert v (s.slots b).arrived} := by
        simpa only [↓reduceIte] using hslots b
      by_cases hc : complete block s.exited
          {s.slots b with expected := some nc', arrived := insert v (s.slots b).arrived} =
            true
      · have hnw : nc' = warps block := by
          rcases Nat.eq_or_lt_of_le hle with heq | hlt
          · subst heq
            have := hric.symm.trans hi'
            simp only [Option.some.injEq, Record.arrival.injEq] at this
            obtain ⟨-, -, rfl, -⟩ := this
            exact Except.ok.inj (hnc.symm.trans hn)
          · exact (hexpc _ (hexp hlt)).symm
        subst hnw
        refine ⟨ic, t, hAtt, fun w hw hlive => ?_⟩
        rw [hexit] at hlive
        simp only [complete, decide_eq_true_eq] at hc
        have hmem : w ∈ insert v (s.slots b).arrived := by
          rcases hc with hcard | ⟨-, hall⟩
          · have hsub : insert v (s.slots b).arrived ⊆ Finset.range (warps block) :=
              Finset.insert_subset (Finset.mem_range.mpr hwb) (howners ic s hAtic)
            have := Finset.eq_of_subset_of_card_le hsub (by simpa using hcard)
            rw [this]
            exact hw
          · exact hall w hw hlive
        rcases Finset.mem_insert.mp hmem with rfl | hwa
        · exact ⟨ic, cntc, lanesc, s, hric, hAtic, hgs⟩
        · exact own w hwa
      · have hc' : complete block s.exited
            {s.slots b with expected := some nc', arrived := insert v (s.slots b).arrived} =
              false := by simpa using hc
        rw [settle_pending hc'] at hs1
        rw [hs1] at hgt
        simp only at hgt
        omega
    · have hs1 : t.slots id = s.slots id := by
        simpa only [Ne.symm hid, ↓reduceIte] using hslots id
      rw [hs1] at hgt
      omega
  | exit g e =>
    change exitThread block s g = .ok t at hperf
    unfold exitThread at hperf
    split_ifs at hperf
    · simp only [pure, Except.pure, Except.ok.injEq] at hperf
      have hlt : i' < ic := by
        rcases Nat.eq_or_lt_of_le hle with heq | hlt
        · subst heq
          have := hric.symm.trans hi'
          cases this
        · exact hlt
      have hex := hexp hlt
      subst hperf
      dsimp only at hgt ⊢
      by_cases hc : complete block (insert g s.exited) (s.slots id) = true
      · refine ⟨ic, _, hAtt, fun w hw hlive => ?_⟩
        simp only [complete, hex, decide_eq_true_eq] at hc
        have hmem : w ∈ (s.slots id).arrived := by
          rcases hc with hcard | ⟨-, hall⟩
          · have := Finset.eq_of_subset_of_card_le (howners ic s hAtic) (by simpa using hcard)
            rw [this]
            exact hw
          · exact hall w hw hlive
        exact own w hmem
      · have hc' : complete block (insert g s.exited) (s.slots id) = false := by simpa using hc
        rw [settle_pending hc'] at hgt
        omega
    · simp [bind, Except.bind, throw] at hperf

/-- **Two arrival records performed in one generation have the same target.** -/
theorem same_gen_target_le {block id φ : Nat} {h : List (Record α)} {u : State}
    (hr : CtaBarrier.run block {} h = .ok u) {i₁ i₂ w₁ w₂ n₁ n₂ : Nat} {c₁ c₂ : Option Nat}
    {l₁ l₂ : List (Nat × α)} {s₁ s₂ : State} (hle : i₁ ≤ i₂)
    (hi₁ : h[i₁]? = some (.arrival id w₁ c₁ l₁)) (hs₁ : At block h i₁ s₁)
    (hg₁ : (s₁.slots id).generation = φ) (hi₂ : h[i₂]? = some (.arrival id w₂ c₂ l₂))
    (hs₂ : At block h i₂ s₂) (hg₂ : (s₂.slots id).generation = φ)
    (hn₁ : target block c₁ = .ok n₁) (hn₂ : target block c₂ = .ok n₂) : n₁ = n₂ := by
  rcases Nat.eq_or_lt_of_le hle with heq | hlt
  · subst heq
    have := hi₁.symm.trans hi₂
    simp only [Option.some.injEq, Record.arrival.injEq] at this
    obtain ⟨-, -, rfl, -⟩ := this
    exact Except.ok.inj (hn₁.symm.trans hn₂)
  · obtain ⟨s₃, t₃, hat₃, hp₃⟩ := run_at_record hr hi₁
    have hss : s₃ = s₁ := Except.ok.inj ((show CtaBarrier.run block {} (h.take i₁) = .ok s₃
      from hat₃).symm.trans hs₁)
    subst hss
    have hAt₃ := at_succ hi₁ hs₁ hp₃
    have hg₃ : (t₃.slots id).generation = φ := by
      have h1 := at_gen_mono (id := id) (by omega : i₁ + 1 ≤ i₂) hAt₃ hs₂
      rcases CtaBarrier.perform_slot (id := id) hp₃ with ⟨h2, -⟩ | h2 <;> omega
    have hperf₃ : arrive block s₃ id w₁ c₁ = .ok t₃ := by
      simp only [Record.perform] at hp₃
      split_ifs at hp₃
      exact hp₃
    obtain ⟨hex, -⟩ := arrive_pending hperf₃ hn₁ (by omega)
    have hex₂ := run_expected (run_between (by omega : i₁ + 1 ≤ i₂) hAt₃ hs₂) (by omega) hex
    obtain ⟨s₄, t₄, hat₄, hp₄⟩ := run_at_record hr hi₂
    have hss' : s₄ = s₂ := Except.ok.inj ((show CtaBarrier.run block {} (h.take i₂) = .ok s₄
      from hat₄).symm.trans hs₂)
    subst hss'
    have hperf₄ : arrive block s₄ id w₂ c₂ = .ok t₄ := by
      simp only [Record.perform] at hp₄
      split_ifs at hp₄
      exact hp₄
    obtain ⟨-, -, -, -, n, hn, hexp⟩ := arrive_ok_info hperf₄
    have := hexp _ hex₂
    have hnn : n = n₂ := Except.ok.inj (hn.symm.trans hn₂)
    omega

theorem same_gen_target {block id φ : Nat} {h : List (Record α)} {u : State}
    (hr : CtaBarrier.run block {} h = .ok u) {i₁ i₂ w₁ w₂ n₁ n₂ : Nat} {c₁ c₂ : Option Nat}
    {l₁ l₂ : List (Nat × α)} {s₁ s₂ : State}
    (hi₁ : h[i₁]? = some (.arrival id w₁ c₁ l₁)) (hs₁ : At block h i₁ s₁)
    (hg₁ : (s₁.slots id).generation = φ) (hi₂ : h[i₂]? = some (.arrival id w₂ c₂ l₂))
    (hs₂ : At block h i₂ s₂) (hg₂ : (s₂.slots id).generation = φ)
    (hn₁ : target block c₁ = .ok n₁) (hn₂ : target block c₂ = .ok n₂) : n₁ = n₂ := by
  rcases le_total i₁ i₂ with hle | hle
  · exact same_gen_target_le hr hle hi₁ hs₁ hg₁ hi₂ hs₂ hg₂ hn₁ hn₂
  · exact (same_gen_target_le hr hle hi₂ hs₂ hg₂ hi₁ hs₁ hg₁ hn₂ hn₁).symm

/-- A warp's arrival count on a barrier before a prefix is at most its count before a longer
prefix. -/
theorem idArrivals_take_mono {id w i j : Nat} {h : List (Record α)} (hij : i ≤ j) :
    idArrivals (h.take i) id w ≤ idArrivals (h.take j) id w := by
  unfold idArrivals
  have h1 : (h.take i) = (h.take j).take i := by
    rw [List.take_take, Nat.min_eq_left hij]
  rw [h1]
  exact (List.take_sublist i (h.take j)).countP_le

/-- A warp's arrival record on a barrier raises its arrival count by one. -/
theorem idArrivals_take_succ {id w i : Nat} {h : List (Record α)} {c : Option Nat}
    {l : List (Nat × α)} (hi : h[i]? = some (.arrival id w c l)) :
    idArrivals (h.take (i + 1)) id w = idArrivals (h.take i) id w + 1 := by
  unfold idArrivals
  rw [List.take_add_one, hi, List.countP_append]
  simp [isWarpIdArrival]

end

end PTX.NamedBar
