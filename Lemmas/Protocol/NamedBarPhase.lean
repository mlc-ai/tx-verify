-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.NamedBarEarly

@[expose] public section

/-!
# A named barrier with a loop group: the generation ledger of the resource

A proof tool, generic over the kernel (promoted from Inkling's `Proof2/Lib/BarLanePhase.lean`).
A named barrier may serve three groups in turn (Inkling's barrier 0): all warps without a count
(the first `start` generations), the warps `D` of the default partition with the count of `D` (the
loop's generations), and all warps without a count again (the last generation, which the default
partition and the workers share). The library's ledger (`NamedBar.Ledger`) asks one group for the
whole history. This file proves what holds of the resource for all three at once, from the sources
of the records alone (`SrcOk`: a record without a count is any warp's; a record with the loop
group's count is a loop warp's whose number of earlier records on the barrier is at least
`start`):

* `Phased`: the state of the slot, relative to `D` (`phased_run`, replay of a history whose records
  follow `SrcOk`): the arrivals in a generation of the loop group are loop warps; every live loop
  warp has arrived exactly once in each generation below the current one (`balD`); every live warp
  has arrived exactly once in each generation below `start` (`early`);
* `gen_of_record_D`: a loop warp's record is in the generation equal to its number of earlier
  records on the barrier, whatever the other warps do;
* `completed_D_record`: a loop warp's lane that never exits has a record in every released
  generation.

No claim is made about the workers' arrival in the last generation: its generation is a
consequence of the ordering, which `NamedBarPhaseKeys.lean` does with the thread facts.
-/

namespace PTX.NamedBar
open PTX CtaBarrier
noncomputable section

variable {α : Type}

/-- The source classification of the records on the barrier: a record has no count, or the loop
group's count and is a loop warp's record of ordinal at least `start`. -/
def SrcOk (D : Finset Nat) (cD : Option Nat) (start w N : Nat) (cnt : Option Nat) : Prop :=
  cnt = none ∨ (cnt = cD ∧ w ∈ D ∧ start ≤ N)

/-- A successful arrival: the facts the resource checked. -/
theorem arrive_ok_info {block id w : Nat} {cnt : Option Nat} {s t : State}
    (h : arrive block s id w cnt = .ok t) :
    id < 16 ∧ w < warps block ∧ warpLive block s.exited w ∧ w ∉ (s.slots id).arrived ∧
      ∃ n, target block cnt = .ok n ∧ ∀ k, (s.slots id).expected = some k → k = n := by
  have hl := arrive_live h
  have hna := arrive_not_arrived h
  by_cases hid : id < 16
  · refine ⟨hid, hl.1, hl.2, hna, ?_⟩
    cases hn : target block cnt with
    | error err => simp [arrive, hid, hl, hn, bind, Except.bind] at h
    | ok n =>
      refine ⟨n, rfl, fun k hk => ?_⟩
      by_contra hkn
      simp [arrive, hid, hl, hn, hna, hk, hkn, bind, Except.bind, pure, Except.pure,
        throw] at h
  · simp [arrive, hid, bind, Except.bind, pure, Except.pure, throw] at h

/-- The ledger of one slot for the loop group `D` (`nD` warps, `start` generations before it). -/
structure Phased (block : Nat) (D : Finset Nat) (nD start id : Nat) (counts : Nat → Nat)
    (s : State) : Prop where
  owners : (s.slots id).arrived ⊆ Finset.range (warps block)
  none_empty : (s.slots id).expected = none → (s.slots id).arrived = ∅
  some_info : ∀ k, (s.slots id).expected = some k →
    (k = warps block ∨ k = nD) ∧ (s.slots id).arrived.card < k ∧
      (k = nD → (s.slots id).arrived ⊆ D ∧ start ≤ (s.slots id).generation)
  balD : ∀ w ∈ D, warpLive block s.exited w →
    counts w = (s.slots id).generation + if w ∈ (s.slots id).arrived then 1 else 0
  early : ∀ w ∈ Finset.range (warps block), warpLive block s.exited w →
    ((s.slots id).generation < start →
      counts w = (s.slots id).generation + if w ∈ (s.slots id).arrived then 1 else 0) ∧
    (start ≤ (s.slots id).generation → start ≤ counts w)

theorem Phased.initial (block nD start id : Nat) (D : Finset Nat) :
    Phased block D nD start id (fun _ => 0) {} := by
  refine ⟨by simp, fun _ => by simp, fun k hk => by simp at hk, fun w _ _ => by simp,
    fun w _ _ => ⟨fun _ => by simp, fun h => by simpa using h⟩⟩

/-- A completion by the requested count of a slot all of whose arrivals are in `P`, whose number
is the size of `P`, has every warp of `P` arrived. -/
theorem complete_all {block n : Nat} {P : Finset Nat} {exited : Finset Nat} {sl : Slot}
    (hP : P ⊆ Finset.range (warps block)) (hcard : P.card = n)
    (hsub : sl.arrived ⊆ P) (hexp : sl.expected = some n)
    (hd : complete block exited sl = true) :
    ∀ w ∈ P, warpLive block exited w → w ∈ sl.arrived := by
  intro w hw hl
  simp only [complete, hexp, decide_eq_true_eq] at hd
  rcases hd with hc | ⟨-, hall⟩
  · have heq : sl.arrived = P := Finset.eq_of_subset_of_card_le hsub (by omega)
    exact heq ▸ hw
  · exact hall w (hP hw) hl

/-- One arrival of a warp with a `SrcOk` record preserves the ledger. -/
theorem Phased.arrival {block nD start id warp : Nat} {D : Finset Nat} {cD cnt : Option Nat}
    {counts : Nat → Nat} {s t : State} (h : Phased block D nD start id counts s)
    (hD : D ⊆ Finset.range (warps block)) (hcard : D.card = nD) (hnD : nD ≠ warps block)
    (hcD : target block cD = .ok nD) (hsrc : SrcOk D cD start warp (counts warp) cnt)
    (ha : arrive block s id warp cnt = .ok t) :
    Phased block D nD start id (increment counts warp) t := by
  obtain ⟨hid, hwb, hwl, hmiss, n, hn, hexp⟩ := arrive_ok_info ha
  obtain ⟨n', hn', hexit, hslots⟩ := arrive_shape ha
  have hnn' : n' = n := Except.ok.inj (hn'.symm.trans hn)
  rw [hnn'] at hslots
  have hslot : t.slots id = settle block s.exited
      {s.slots id with expected := some n, arrived := insert warp (s.slots id).arrived} := by
    simpa only [↓reduceIte] using hslots id
  have hrange : target block none = .ok (warps block) := by
    simp [target]
  -- the group of the arrival
  have hgrp : (n = warps block) ∨ (n = nD ∧ warp ∈ D ∧ start ≤ counts warp) := by
    rcases hsrc with hc | ⟨hc, hw, hN⟩
    · left
      subst hc
      exact (Except.ok.inj (hn.symm.trans hrange))
    · right
      subst hc
      exact ⟨(Except.ok.inj (hn.symm.trans hcD)), hw, hN⟩
  have hsubA : insert warp (s.slots id).arrived ⊆ Finset.range (warps block) :=
    Finset.insert_subset (Finset.mem_range.mpr hwb) h.owners
  have hcardA : (insert warp (s.slots id).arrived).card = (s.slots id).arrived.card + 1 :=
    Finset.card_insert_of_notMem hmiss
  have hbw : warp ∈ D → counts warp = (s.slots id).generation := by
    intro hw
    have hb := h.balD warp hw hwl
    simpa only [hmiss, ↓reduceIte, Nat.add_zero] using hb
  -- the arrived set of a loop generation is within `D`
  have hAD : n = nD →
      insert warp (s.slots id).arrived ⊆ D ∧ start ≤ (s.slots id).generation := by
    intro hnD'
    have hw : warp ∈ D ∧ start ≤ counts warp := by
      rcases hgrp with h1 | ⟨-, hw, hN⟩
      · exact absurd (h1.symm.trans hnD') (Ne.symm hnD)
      · exact ⟨hw, hN⟩
    have hb := hbw hw.1
    refine ⟨?_, by omega⟩
    refine Finset.insert_subset hw.1 ?_
    by_cases he : (s.slots id).expected = none
    · rw [h.none_empty he]; exact Finset.empty_subset _
    · obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp he
      have hkn := hexp k hk
      exact ((h.some_info k hk).2.2 (by omega)).1
  have hnn : n = warps block ∨ n = nD := by
    rcases hgrp with h1 | ⟨h1, -⟩
    · exact .inl h1
    · exact .inr h1
  by_cases hd : complete block s.exited
      {s.slots id with expected := some n, arrived := insert warp (s.slots id).arrived} = true
  · rw [settle_complete hd] at hslot
    -- every live warp of the group has arrived
    have hall : ∀ w ∈ Finset.range (warps block), n = warps block →
        warpLive block s.exited w → w ∈ insert warp (s.slots id).arrived := by
      intro w hw hnw hl
      exact complete_all (n := warps block) (P := Finset.range (warps block))
        (Finset.Subset.refl _) (by simp) hsubA (by simp [hnw]) hd w hw hl
    have hallD : ∀ w ∈ D, n = nD → warpLive block s.exited w →
        w ∈ insert warp (s.slots id).arrived := by
      intro w hw hnw hl
      exact complete_all (n := nD) hD hcard (hAD hnw).1 (by simp [hnw]) hd w hw hl
    have hmemD : ∀ w ∈ D, warpLive block s.exited w →
        w ∈ insert warp (s.slots id).arrived := by
      intro w hw hl
      rcases hnn with h1 | h1
      · exact hall w (hD hw) h1 hl
      · exact hallD w hw h1 hl
    refine ⟨by rw [hslot]; simp, fun _ => by rw [hslot],
      fun k hk => by rw [hslot] at hk; simp at hk, ?_, ?_⟩
    · intro w hw hl
      rw [hexit] at hl
      have hm := hmemD w hw hl
      have hb := h.balD w hw hl
      rw [hslot]
      by_cases hww : w = warp
      · subst hww
        simp only [increment, ↓reduceIte, hmiss, Nat.add_zero, Finset.notMem_empty] at hb ⊢
        omega
      · have hmA : w ∈ (s.slots id).arrived := (Finset.mem_insert.mp hm).resolve_left hww
        simp only [increment, hww, ↓reduceIte, hmA] at hb ⊢
        simp
        omega
    · intro w hw hl
      rw [hexit] at hl
      have hb := h.early w hw hl
      rw [hslot]
      simp only [increment]
      constructor
      · intro hlt
        have hlt' : (s.slots id).generation < start := by omega
        have hb1 := hb.1 hlt'
        have hm := hall w hw (by
          rcases hnn with h1 | h1
          · exact h1
          · have := (hAD h1).2; omega) hl
        by_cases hww : w = warp
        · subst hww
          simp only [↓reduceIte, Finset.notMem_empty]
          simp [hmiss] at hb1
          omega
        · have hmA : w ∈ (s.slots id).arrived := (Finset.mem_insert.mp hm).resolve_left hww
          simp only [hww, ↓reduceIte, hmA] at hb1 ⊢
          simp
          omega
      · intro hst
        have hb2 : start ≤ counts w ∨ (s.slots id).generation < start := by
          by_cases hh : start ≤ (s.slots id).generation
          · exact .inl (hb.2 hh)
          · exact .inr (by omega)
        by_cases hww : w = warp
        · subst hww
          simp only [↓reduceIte]
          rcases hb2 with hb2 | hb2
          · omega
          · have hb1 := hb.1 hb2
            simp [hmiss] at hb1
            omega
        · simp only [hww, ↓reduceIte]
          rcases hb2 with hb2 | hb2
          · exact hb2
          · have hb1 := hb.1 hb2
            have hm := hall w hw (by
              rcases hnn with h1 | h1
              · exact h1
              · have := (hAD h1).2; omega) hl
            have hmA : w ∈ (s.slots id).arrived := (Finset.mem_insert.mp hm).resolve_left hww
            simp only [hmA, ↓reduceIte] at hb1
            omega
  · have hd' : complete block s.exited
        {s.slots id with expected := some n, arrived := insert warp (s.slots id).arrived} =
          false := by simpa using hd
    rw [settle_pending hd'] at hslot
    have hlt : (insert warp (s.slots id).arrived).card < n := by
      by_contra hge
      exact hd (complete_of_count rfl (show n ≤ (insert warp (s.slots id).arrived).card by omega))
    refine ⟨by rw [hslot]; exact hsubA, fun h' => by rw [hslot] at h'; simp at h',
      fun k hk => ?_, ?_, ?_⟩
    · rw [hslot] at hk
      have hkn : k = n := (Option.some.inj hk).symm
      subst hkn
      rw [hslot]
      exact ⟨hnn, hlt, hAD⟩
    · intro w hw hl
      rw [hexit] at hl
      have hb := h.balD w hw hl
      rw [hslot]
      by_cases hww : w = warp
      · subst hww
        simp only [increment, ↓reduceIte, hmiss, Nat.add_zero, Finset.mem_insert,
          true_or] at hb ⊢
        omega
      · simp only [increment, hww, ↓reduceIte, Finset.mem_insert, false_or] at hb ⊢
        exact hb
    · intro w hw hl
      rw [hexit] at hl
      have hb := h.early w hw hl
      rw [hslot]
      simp only [increment]
      by_cases hww : w = warp
      · subst hww
        simp only [↓reduceIte, Finset.mem_insert, true_or]
        constructor
        · intro hlt'
          have := hb.1 hlt'
          simp [hmiss] at this
          omega
        · intro hst
          by_cases hh : start ≤ (s.slots id).generation
          · have := hb.2 hh; omega
          · have := hb.1 (by omega)
            simp [hmiss] at this
            omega
      · simp only [hww, ↓reduceIte, Finset.mem_insert, false_or]
        exact hb

/-- An arrival on another barrier leaves the ledger of `id` alone. -/
theorem Phased.other_arrival {block nD start id other warp : Nat} {D : Finset Nat}
    {cnt : Option Nat} {counts : Nat → Nat} {s t : State}
    (h : Phased block D nD start id counts s) (hne : id ≠ other)
    (ha : arrive block s other warp cnt = .ok t) : Phased block D nD start id counts t := by
  obtain ⟨_, -, hexit, hslots⟩ := arrive_shape ha
  have hs : t.slots id = s.slots id := by simpa only [ite_eq_right hne] using hslots id
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hs] using h.owners
  · simpa only [hs] using h.none_empty
  · simpa only [hs] using h.some_info
  · intro w hw hl
    rw [hexit] at hl
    simpa only [hs] using h.balD w hw hl
  · intro w hw hl
    rw [hexit] at hl
    simpa only [hs] using h.early w hw hl

/-- An exit leaves the counts alone; it may complete a generation, but only when every live warp
of the group has arrived. -/
theorem Phased.exit {block nD start id g : Nat} {D : Finset Nat} {counts : Nat → Nat}
    {s t : State} (h : Phased block D nD start id counts s)
    (hD : D ⊆ Finset.range (warps block)) (he : exitThread block s g = .ok t) :
    Phased block D nD start id counts t := by
  unfold exitThread at he
  split_ifs at he with hg
  · simp only [pure, Except.pure, Except.ok.injEq] at he
    subst he
    have hmono : s.exited ⊆ insert g s.exited := Finset.subset_insert _ _
    by_cases hd : complete block (insert g s.exited) (s.slots id) = true
    · -- a completion by exit is by every live warp having arrived
      obtain ⟨k, hk⟩ : ∃ k, (s.slots id).expected = some k := by
        cases hx : (s.slots id).expected with
        | none => simp [complete, hx] at hd
        | some k => exact ⟨k, rfl⟩
      obtain ⟨hkk, hlt, hkD⟩ := h.some_info k hk
      have hall : ∀ w ∈ Finset.range (warps block), warpLive block (insert g s.exited) w →
          w ∈ (s.slots id).arrived := by
        intro w hw hl
        simp only [complete, hk, decide_eq_true_eq] at hd
        rcases hd with hc | ⟨-, hall⟩
        · omega
        · exact hall w hw hl
      refine ⟨by simp [settle_complete hd], fun _ => by simp [settle_complete hd],
        fun k' hk' => by simp [settle_complete hd] at hk', ?_, ?_⟩
      · intro w hw hl
        have hb := h.balD w hw (warpLive_mono hmono hl)
        have hm := hall w (hD hw) hl
        simp [settle_complete hd, hm] at hb ⊢
        omega
      · intro w hw hl
        have hb := h.early w hw (warpLive_mono hmono hl)
        have hm := hall w hw hl
        simp only [settle_complete hd]
        simp only [hm, ↓reduceIte] at hb
        simp only [Finset.notMem_empty, ↓reduceIte, Nat.add_zero]
        constructor
        · intro hlt'
          omega
        · intro hst
          by_cases hh : start ≤ (s.slots id).generation
          · have := hb.2 hh; omega
          · have := hb.1 (by omega); omega
    · have hd' : complete block (insert g s.exited) (s.slots id) = false := by simpa using hd
      have hs : settle block (insert g s.exited) (s.slots id) = s.slots id := settle_pending hd'
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simpa only [hs] using h.owners
      · simpa only [hs] using h.none_empty
      · simpa only [hs] using h.some_info
      · intro w hw hl
        simpa only [hs] using h.balD w hw (warpLive_mono hmono hl)
      · intro w hw hl
        simpa only [hs] using h.early w hw (warpLive_mono hmono hl)
  · simp [bind, Except.bind, throw] at he

/-- **The records of a history follow `SrcOk`.** Every arrival record on `id` has no count, or the
loop group's count and a loop warp whose number of earlier records on `id` is at least `start`. -/
def PhProtocol (D : Finset Nat) (cD : Option Nat) (start id : Nat) (h : List (Record α)) :
    Prop :=
  ∀ k warp cnt lanes, h[k]? = some (.arrival id warp cnt lanes) →
    SrcOk D cD start warp (idArrivals (h.take k) id warp) cnt

/-- **Replaying a history whose records follow `SrcOk` gives the ledger** of its final state. -/
theorem phased_run {block nD start id : Nat} {D : Finset Nat} {cD : Option Nat}
    (hD : D ⊆ Finset.range (warps block)) (hcard : D.card = nD) (hnD : nD ≠ warps block)
    (hcD : target block cD = .ok nD) :
    ∀ {h : List (Record α)} {s : State}, PhProtocol D cD start id h →
      run block {} h = .ok s → Phased block D nD start id (idArrivals h id) s := by
  intro h
  induction h using List.reverseRecOn with
  | nil =>
    intro s _ hr
    cases hr
    exact Phased.initial block nD start id D
  | @append_singleton xs r ih =>
    intro s hp hr
    obtain ⟨u, hu⟩ := run_prefix hr
    have hpx : PhProtocol D cD start id xs := by
      intro k warp cnt lanes hk
      have hk' : (xs ++ [r])[k]? = some (.arrival id warp cnt lanes) := by
        rw [List.getElem?_append_left (by exact (List.getElem?_eq_some_iff.mp hk).1)]
        exact hk
      have := hp k warp cnt lanes hk'
      rwa [List.take_append_of_le_length (by
        exact (List.getElem?_eq_some_iff.mp hk).1.le)] at this
    have hs := ih hpx hu
    have hf : r.perform block u = .ok s := by
      rw [run_append, hu] at hr
      cases hf : r.perform block u with
      | error err => simp [run, hf, Except.bind] at hr
      | ok v => simpa only [run, hf, Except.bind, Except.ok.injEq, throw, throwThe,
          MonadExceptOf.throw] using hr
    cases r with
    | arrival other warp cnt lanes =>
      simp only [Record.perform] at hf
      split_ifs at hf with hlanes
      by_cases hother : other = id
      · subst other
        have hsrc := hp xs.length warp cnt lanes (by simp)
        rw [List.take_left] at hsrc
        have heq : idArrivals (xs ++ [Record.arrival id warp cnt lanes]) id =
            increment (idArrivals xs id) warp := by
          funext w
          by_cases hw' : w = warp
          · subst w
            simp [idArrivals, isWarpIdArrival, increment]
          · simp [idArrivals, isWarpIdArrival, increment, hw', Ne.symm hw']
        rw [heq]
        exact hs.arrival hD hcard hnD hcD hsrc hf
      · have heq : idArrivals (xs ++ [Record.arrival other warp cnt lanes]) id =
            idArrivals xs id := by
          funext w
          simp [idArrivals, isWarpIdArrival, hother]
        rw [heq]
        exact hs.other_arrival (Ne.symm hother) hf
    | exit g e =>
      have heq : idArrivals (xs ++ [Record.exit g e]) id = idArrivals xs id := by
        funext w
        simp [idArrivals, isWarpIdArrival]
      rw [heq]
      exact hs.exit hD hf

theorem PhProtocol.take {D : Finset Nat} {cD : Option Nat} {start id : Nat} {h : List (Record α)}
    (hp : PhProtocol D cD start id h) (k : Nat) : PhProtocol D cD start id (h.take k) := by
  intro j warp cnt lanes hj
  have hjk : j < k := by
    have := (List.getElem?_eq_some_iff.mp hj).1
    simp only [List.length_take] at this
    omega
  rw [List.getElem?_take_of_lt hjk] at hj
  have := hp j warp cnt lanes hj
  rwa [List.take_take, Nat.min_eq_left hjk.le]

variable {block nD start id : Nat} {D : Finset Nat} {cD : Option Nat}

/-- **The generation of a record** is the number of earlier records of its warp on the barrier,
for a loop warp, and for any warp that has fewer than `start` earlier records. -/
theorem gen_of_record (hD : D ⊆ Finset.range (warps block)) (hcard : D.card = nD)
    (hnD : nD ≠ warps block) (hcD : target block cD = .ok nD) {h : List (Record α)}
    (hp : PhProtocol D cD start id h) {k warp : Nat} {cnt : Option Nat}
    {lanes : List (Nat × α)} {s t : State} (hs : At block h k s)
    (ht : Record.perform block s (.arrival id warp cnt lanes) = .ok t) :
    (warp ∈ D ∨ idArrivals (h.take k) id warp < start) →
      idArrivals (h.take k) id warp = (s.slots id).generation := by
  have hl := phased_run hD hcard hnD hcD (hp.take k) hs
  simp only [Record.perform] at ht
  split_ifs at ht
  obtain ⟨-, hwb, hwl, hmiss, -⟩ := arrive_ok_info ht
  rintro (hw | hlt)
  · have := hl.balD warp hw hwl
    simpa only [hmiss, ↓reduceIte, Nat.add_zero] using this
  · have := (hl.early warp (Finset.mem_range.mpr hwb) hwl).1 (by
      by_contra hge
      have := (hl.early warp (Finset.mem_range.mpr hwb) hwl).2 (by omega)
      omega)
    simpa only [hmiss, ↓reduceIte, Nat.add_zero] using this

/-- **A loop warp's lane that never exits has a record in every released generation**: the
lane's record in generation `phase`, with the count the record has. -/
theorem completed_D_record (hD : D ⊆ Finset.range (warps block)) (hcard : D.card = nD)
    (hnD : nD ≠ warps block) (hcD : target block cD = .ok nD) {h : List (Record α)}
    (hp : PhProtocol D cD start id h) {phase : Nat} {last : State}
    (hr : run block {} h = .ok last) (hphase : phase < (last.slots id).generation)
    {g : Nat} (hg : g < block) (hw : g / 32 ∈ D) (hlive : g ∉ last.exited) :
    ∃ (index : Nat) (cnt : Option Nat) (lanes : List (Nat × α)) (e : α),
      h[index]? = some (.arrival id (g / 32) cnt lanes) ∧ (g, e) ∈ lanes ∧
        idArrivals (h.take index) id (g / 32) = phase ∧ GenerationOf block h e id phase := by
  have hl := phased_run hD hcard hnD hcD hp hr
  have hb := hl.balD (g / 32) hw (warpLive_of_lane hg hlive)
  have hocc : phase < h.countP (isWarpIdArrival id (g / 32)) := by
    change phase < idArrivals h id (g / 32)
    omega
  obtain ⟨index, r, hi, hsel, hprior⟩ := countP_index hocc
  cases r with
  | exit _ _ => simp [isWarpIdArrival] at hsel
  | arrival other warp cnt lanes =>
    have hfields : other = id ∧ warp = g / 32 := by
      simpa only [isWarpIdArrival, Bool.and_eq_true, beq_iff_eq] using hsel
    obtain ⟨hid, hwarp⟩ := hfields
    subst other
    subst warp
    obtain ⟨before, after, hbefore, hafter⟩ := run_at_record hr hi
    have hil := (List.getElem?_eq_some_iff.mp hi).1
    have hnot : g ∉ before.exited := fun hm => hlive (exited_prefix (j := h.length) hil.le hbefore
      (by unfold At; rw [List.take_length]; exact hr) hm)
    have hmembers := perform_arrival_lanes hafter
    obtain ⟨pair, hpair, hpairg⟩ := List.mem_map.mp (hmembers.2.2 g hg rfl hnot)
    have hpge : (g, pair.2) = pair := by rw [← hpairg]
    have hgmember : (g, pair.2) ∈ lanes := hpge.symm ▸ hpair
    have hgeneration := gen_of_record hD hcard hnD hcD hp hbefore hafter (.inl hw)
    have hprior' : idArrivals (h.take index) id (g / 32) = phase := hprior
    refine ⟨index, cnt, lanes, pair.2, hi, hgmember, hprior', index, before, g / 32,
      cnt, lanes, g, hi, hbefore, hgmember, ?_, after, hafter⟩
    omega

end
end PTX.NamedBar
