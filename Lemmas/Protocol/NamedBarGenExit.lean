-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.NamedBarGenLedger

@[expose] public section

/-!
# A released generation of all warps counts every lane: arrival or exit

Generic facts about one named resource along a checked history (`CtaBarrier.run`), without any
protocol on the history. They are what Inkling's exit argument (`BarExit.lean`) needs about the
last generation of named barrier 0, whose arrivals the library's single-group ledgers do not
cover.

* `arrival_kept`: within one generation, a warp that arrived stays arrived and the requested count
  stays the count its arrival asked for;
* `arrived_record`: a warp that has arrived in the open generation has an arrival record in that
  generation;
* `completes_counts`: when a generation is completed and one of its arrivals asked for all the
  warps of the CTA, every lane of the CTA has, at or before the completing record, an exit record
  or a lane in an arrival record of that generation which asked for all the warps;
* `start_le_ordinal`: for a barrier whose records follow `PhProtocol`, an arrival record in a
  generation at least `start` is preceded by at least `start` records of its warp.

The library version of Inkling's `Proof2/Lib/BarExitRes.lean`, in the namespace
`NamedBar.GenLedger`; it uses `at_succ`, `run_between` and `at_gen_mono` of
`Lemmas/Protocol/NamedBarGenLedger.lean`.
-/

namespace PTX.NamedBar.GenLedger
open PTX CtaBarrier
noncomputable section

variable {α : Type} {block : Nat}

/-- **An update that keeps the generation of a resource keeps its arrived warps and its requested
count.** -/
theorem perform_keep {id : Nat} {r : Record α} {s t : State} (h : r.perform block s = .ok t)
    (hg : (t.slots id).generation = (s.slots id).generation) :
    (s.slots id).arrived ⊆ (t.slots id).arrived ∧
      ∀ n, (s.slots id).expected = some n → (t.slots id).expected = some n := by
  cases r with
  | exit g e =>
    simp only [Record.perform, exitThread] at h
    by_cases hg' : g < block ∧ g ∉ s.exited
    · simp only [hg', not_false_eq_true, and_self, bind, Except.bind, pure,
        Except.pure] at h
      cases h
      change (settle block (insert g s.exited) (s.slots id)).generation = _ at hg
      change (s.slots id).arrived ⊆ (settle block (insert g s.exited) (s.slots id)).arrived ∧
        ∀ n, (s.slots id).expected = some n →
          (settle block (insert g s.exited) (s.slots id)).expected = some n
      by_cases hc : complete block (insert g s.exited) (s.slots id) = true
      · rw [settle_complete hc] at hg
        simp at hg
      · rw [settle_pending (by simpa using hc)]
        exact ⟨Finset.Subset.refl _, fun n h => h⟩
    · simp [hg', bind, Except.bind, throw] at h
  | arrival id' w cnt lanes =>
    simp only [Record.perform] at h
    split_ifs at h with hl
    obtain ⟨-, -, -, -, n', hn', hk⟩ := arrive_ok_info h
    obtain ⟨n, hn, -, hslots⟩ := arrive_shape h
    have hnn : n = n' := Except.ok.inj (hn.symm.trans hn')
    rw [hslots] at hg ⊢
    by_cases hi : id = id'
    · subst hi
      simp only [↓reduceIte] at hg ⊢
      by_cases hc : complete block s.exited
          {s.slots id with expected := some n, arrived := insert w (s.slots id).arrived} = true
      · rw [settle_complete hc] at hg
        simp at hg
      · rw [settle_pending (by simpa using hc)]
        refine ⟨Finset.subset_insert _ _, fun m hm => ?_⟩
        have := hk m hm
        simp only [Option.some.injEq]
        omega
    · simp only [hi, ↓reduceIte]
      exact ⟨Finset.Subset.refl _, fun n h => h⟩

/-- **A run that keeps the generation keeps the arrived warps and the requested count.** -/
theorem run_keep {id : Nat} :
    ∀ {xs : List (Record α)} {u v : State}, CtaBarrier.run block u xs = .ok v →
      (v.slots id).generation = (u.slots id).generation →
      (u.slots id).arrived ⊆ (v.slots id).arrived ∧
        ∀ n, (u.slots id).expected = some n → (v.slots id).expected = some n
  | [], u, v, hr, _ => by
    simp only [CtaBarrier.run, Except.ok.injEq] at hr
    subst hr
    exact ⟨Finset.Subset.refl _, fun n h => h⟩
  | r :: rs, u, v, hr, hg => by
    cases hp : r.perform block u with
    | error err => simp only [CtaBarrier.run, hp, Except.bind] at hr; cases hr
    | ok w =>
      have ht : CtaBarrier.run block w rs = .ok v := by
        simpa only [CtaBarrier.run, hp, Except.bind] using hr
      have h1 := perform_generation_mono hp id
      have h2 := run_generation_mono ht id
      obtain ⟨a1, e1⟩ := perform_keep (id := id) hp (by omega)
      obtain ⟨a2, e2⟩ := run_keep (id := id) ht (by omega)
      exact ⟨a1.trans a2, fun n h => e2 n (e1 n h)⟩

/-- **Within one generation an arrival stays**: the warp of an arrival record stays arrived, and
the requested count stays the one the arrival asked for, at every later state of the same
generation. -/
theorem arrival_kept {h : List (Record α)} {i k id w : Nat} {cnt : Option Nat}
    {lanes : List (Nat × α)} {si ti sk : State} (hi : h[i]? = some (.arrival id w cnt lanes))
    (hsi : At block h i si) (hti : Record.perform block si (.arrival id w cnt lanes) = .ok ti)
    (hik : i < k) (hsk : At block h k sk)
    (hgen : (sk.slots id).generation = (si.slots id).generation) :
    w ∈ (sk.slots id).arrived ∧
      ∃ n, target block cnt = .ok n ∧ (sk.slots id).expected = some n := by
  have hti' := at_succ hi hsi hti
  have h1 := at_gen_mono (id := id) (Nat.le_succ i) hsi hti'
  have h2 := at_gen_mono (id := id) (show i + 1 ≤ k by omega) hti' hsk
  have hrun := run_between (show i + 1 ≤ k by omega) hti' hsk
  obtain ⟨a, e⟩ := run_keep (id := id) hrun (by omega)
  simp only [Record.perform] at hti
  split_ifs at hti with hl
  obtain ⟨n, hn, -, hslots⟩ := arrive_shape hti
  have hslot : ti.slots id = settle block si.exited
      {si.slots id with expected := some n, arrived := insert w (si.slots id).arrived} := by
    simpa only [↓reduceIte] using hslots id
  have hc : ¬ complete block si.exited
      {si.slots id with expected := some n, arrived := insert w (si.slots id).arrived} = true := by
    intro hc
    rw [hslot, settle_complete hc] at h1 h2
    simp only at h1 h2
    omega
  rw [settle_pending (by simpa using hc)] at hslot
  refine ⟨a (by rw [hslot]; exact Finset.mem_insert_self _ _), n, hn, e n (by rw [hslot])⟩

/-- One update: a warp arrived after it was arrived before in the same generation, or the update
is its arrival and keeps the generation. -/
theorem perform_arrived {id w : Nat} {r : Record α} {s t : State} (h : r.perform block s = .ok t)
    (hw : w ∈ (t.slots id).arrived) :
    ((t.slots id).generation = (s.slots id).generation ∧ w ∈ (s.slots id).arrived) ∨
      ((t.slots id).generation = (s.slots id).generation ∧
        ∃ cnt lanes, r = .arrival id w cnt lanes) := by
  cases r with
  | exit g e =>
    simp only [Record.perform, exitThread] at h
    by_cases hg' : g < block ∧ g ∉ s.exited
    · simp only [hg', not_false_eq_true, and_self, bind, Except.bind, pure,
        Except.pure] at h
      cases h
      change w ∈ (settle block (insert g s.exited) (s.slots id)).arrived at hw
      change ((settle block (insert g s.exited) (s.slots id)).generation = _ ∧ _) ∨
        ((settle block (insert g s.exited) (s.slots id)).generation = _ ∧ _)
      by_cases hc : complete block (insert g s.exited) (s.slots id) = true
      · rw [settle_complete hc] at hw
        simp at hw
      · rw [settle_pending (by simpa using hc)] at hw ⊢
        exact .inl ⟨rfl, hw⟩
    · simp [hg', bind, Except.bind, throw] at h
  | arrival id' w' cnt lanes =>
    simp only [Record.perform] at h
    split_ifs at h with hl
    obtain ⟨n, hn, -, hslots⟩ := arrive_shape h
    rw [hslots] at hw ⊢
    by_cases hi : id = id'
    · subst hi
      simp only [↓reduceIte] at hw ⊢
      by_cases hc : complete block s.exited
          {s.slots id with expected := some n, arrived := insert w' (s.slots id).arrived} = true
      · rw [settle_complete hc] at hw
        simp at hw
      · rw [settle_pending (by simpa using hc)] at hw ⊢
        rcases Finset.mem_insert.mp hw with rfl | hw'
        · exact .inr ⟨rfl, cnt, lanes, rfl⟩
        · exact .inl ⟨rfl, hw'⟩
    · simp only [hi, ↓reduceIte] at hw ⊢
      exact .inl ⟨by simp, hw⟩

/-- **A warp arrived in the open generation has an arrival record in it.** -/
theorem arrived_record {h : List (Record α)} {id : Nat} :
    ∀ k {s : State}, At block h k s → ∀ w ∈ (s.slots id).arrived,
      ∃ i cnt lanes si ti, i < k ∧ h[i]? = some (.arrival id w cnt lanes) ∧ At block h i si ∧
        Record.perform block si (.arrival id w cnt lanes) = .ok ti ∧
        (si.slots id).generation = (s.slots id).generation := by
  intro k
  induction k with
  | zero =>
    intro s hs w hw
    unfold At at hs
    simp only [List.take_zero, CtaBarrier.run, Except.ok.injEq] at hs
    subst hs
    simp at hw
  | succ k ih =>
    intro s hs w hw
    by_cases hlt : k < h.length
    · obtain ⟨r, hr⟩ : ∃ r, h[k]? = some r := ⟨h[k], List.getElem?_eq_getElem hlt⟩
      obtain ⟨s0, hs0⟩ : ∃ s0, At block h k s0 := by
        have hs' := hs
        unfold At at hs'
        rw [List.take_add_one, hr] at hs'
        obtain ⟨u, hu⟩ := run_prefix hs'
        exact ⟨u, hu⟩
      obtain ⟨t, ht⟩ : ∃ t, r.perform block s0 = .ok t := by
        have hs' := hs
        unfold At at hs' hs0
        rw [List.take_add_one, hr, run_append, hs0] at hs'
        cases hp : r.perform block s0 with
        | error err => simp [CtaBarrier.run, hp, Except.bind] at hs'
        | ok t => exact ⟨t, rfl⟩
      have hts : t = s := by
        have h1 := at_succ hr hs0 ht
        unfold At at h1 hs
        exact Except.ok.inj (h1.symm.trans hs)
      subst hts
      rcases perform_arrived ht hw with ⟨hg, hw0⟩ | ⟨hg, cnt, lanes, rfl⟩
      · obtain ⟨i, cnt, lanes, si, ti, hi, hri, hsi, hti, hgi⟩ := ih hs0 w hw0
        exact ⟨i, cnt, lanes, si, ti, by omega, hri, hsi, hti, hgi.trans hg.symm⟩
      · exact ⟨k, cnt, lanes, s0, t, by omega, hr, hs0, ht, hg.symm⟩
    · have hk : h.take (k + 1) = h.take k := by
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      have hs' : At block h k s := by
        unfold At at hs ⊢
        rwa [hk] at hs
      obtain ⟨i, cnt, lanes, si, ti, hi, hri, hsi, hti, hgi⟩ := ih hs' w hw
      exact ⟨i, cnt, lanes, si, ti, by omega, hri, hsi, hti, hgi⟩

/-- The arrived warps of a slot are warps of the CTA. -/
theorem arrived_lt {h : List (Record α)} {id k : Nat} {s : State} (hs : At block h k s)
    {w : Nat} (hw : w ∈ (s.slots id).arrived) : w < warps block := by
  obtain ⟨i, cnt, lanes, si, ti, -, -, -, hti, -⟩ := arrived_record k hs w hw
  simp only [Record.perform] at hti
  split_ifs at hti
  exact (arrive_live hti).1

/-- A completion with the count of all warps has every live warp of the CTA arrived. -/
theorem complete_all_warps {exited : Finset Nat} {sl : Slot}
    (hsub : sl.arrived ⊆ Finset.range (warps block)) (he : sl.expected = some (warps block))
    (hc : complete block exited sl = true) {w : Nat} (hw : w < warps block)
    (hl : warpLive block exited w) : w ∈ sl.arrived := by
  simp only [complete, he, decide_eq_true_eq] at hc
  rcases hc with hc | ⟨-, hall⟩
  · have heq : sl.arrived = Finset.range (warps block) :=
      Finset.eq_of_subset_of_card_le hsub (by simpa using hc)
    rw [heq]
    exact Finset.mem_range.mpr hw
  · exact hall w (Finset.mem_range.mpr hw) hl

/-- **A released generation of all warps counts every lane of the CTA.** The generation `G` of
resource `id` is completed by the record at `ic`, and one of its arrival records (at `j ≤ ic`)
asked for all the warps of the CTA. Every lane `l` of the CTA then has, at or before `ic`, an
exit record, or a lane in an arrival record of generation `G` that asked for all the warps. -/
theorem completes_counts {h : List (Record α)} {ic id G : Nat}
    (hc : CompletesAt block h ic id G) {j w : Nat} {cnt : Option Nat} {lanes : List (Nat × α)}
    {sj tj : State} (hj : h[j]? = some (.arrival id w cnt lanes)) (hsj : At block h j sj)
    (htj : Record.perform block sj (.arrival id w cnt lanes) = .ok tj)
    (hjg : (sj.slots id).generation = G) (hjn : target block cnt = .ok (warps block))
    (hji : j ≤ ic) {l : Nat} (hl : l < block) :
    (∃ i y, i ≤ ic ∧ h[i]? = some (.exit l y)) ∨
    ∃ i cnt' lanes' y si ti, i ≤ ic ∧ h[i]? = some (.arrival id (l / 32) cnt' lanes') ∧
      (l, y) ∈ lanes' ∧ At block h i si ∧
      Record.perform block si (.arrival id (l / 32) cnt' lanes') = .ok ti ∧
      (si.slots id).generation = G ∧ target block cnt' = .ok (warps block) := by
  obtain ⟨r, s, t, hr, hs, ht, hg0, hg1⟩ := hc
  have hat := at_succ hr hs ht
  by_cases hx : l ∈ t.exited
  · left
    have hrun : CtaBarrier.run block {} (h.take (ic + 1)) = .ok t := hat
    obtain ⟨a, ha⟩ := run_exited_mem hrun hx
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp ha
    have hil : i < ic + 1 := by
      have := (List.getElem?_eq_some_iff.mp hi).1
      simp only [List.length_take] at this
      omega
    rw [List.getElem?_take_of_lt hil] at hi
    exact ⟨i, a, by omega, hi⟩
  right
  have hlw : l / 32 < warps block := by unfold warps; omega
  have hsub : (s.slots id).arrived ⊆ Finset.range (warps block) :=
    fun w hw => Finset.mem_range.mpr (arrived_lt hs hw)
  -- the warp of `l` in the open generation: the record found, with the count of all warps
  have hfound : ∀ {sl : Slot}, sl.arrived ⊆ Finset.range (warps block) →
      sl.expected = some (warps block) → complete block t.exited sl = true →
      l / 32 ∈ sl.arrived := fun hsl he hcomp =>
    complete_all_warps hsl he hcomp hlw (warpLive_of_lane hl hx)
  have hfrom : l / 32 ∈ (s.slots id).arrived →
      (∀ i cnt' lanes' si ti, i < ic → h[i]? = some (.arrival id (l / 32) cnt' lanes') →
        At block h i si → Record.perform block si (.arrival id (l / 32) cnt' lanes') = .ok ti →
        (si.slots id).generation = G → target block cnt' = .ok (warps block)) →
      ∃ i cnt' lanes' y si ti, i ≤ ic ∧ h[i]? = some (.arrival id (l / 32) cnt' lanes') ∧
        (l, y) ∈ lanes' ∧ At block h i si ∧
        Record.perform block si (.arrival id (l / 32) cnt' lanes') = .ok ti ∧
        (si.slots id).generation = G ∧ target block cnt' = .ok (warps block) := by
    intro hw htg
    obtain ⟨i, cnt', lanes', si, ti, hi, hri, hsi, hti, hgi⟩ := arrived_record ic hs (l / 32) hw
    have hnot : l ∉ si.exited := fun hm => hx (exited_prefix (by omega) hsi hat hm)
    obtain ⟨q, hq, hql⟩ := List.mem_map.mp ((perform_arrival_lanes hti).2.2 l hl rfl hnot)
    refine ⟨i, cnt', lanes', q.2, si, ti, by omega, hri, ?_, hsi, hti, by omega,
      htg i cnt' lanes' si ti hi hri hsi hti (by omega)⟩
    have : (l, q.2) = q := by rw [← hql]
    rw [this]
    exact hq
  -- a record of the generation before `ic` gives the requested count at `ic`
  have hkept : ∀ i w' cnt' lanes' si ti, i < ic → h[i]? = some (.arrival id w' cnt' lanes') →
      At block h i si → Record.perform block si (.arrival id w' cnt' lanes') = .ok ti →
      (si.slots id).generation = G →
      ∃ n, target block cnt' = .ok n ∧ (s.slots id).expected = some n :=
    fun i w' cnt' lanes' si ti hi hri hsi hti hgi =>
      (arrival_kept hri hsi hti hi hs (by omega)).2
  cases r with
  | exit g y =>
    have hjic : j < ic := by
      rcases Nat.lt_or_eq_of_le hji with h1 | h1
      · exact h1
      · subst h1; rw [hj] at hr; cases hr
    obtain ⟨n, hn, hexp⟩ := hkept j w cnt lanes sj tj hjic hj hsj htj hjg
    have hnw : n = warps block := Except.ok.inj (hn.symm.trans hjn)
    subst hnw
    simp only [Record.perform, exitThread] at ht
    by_cases hg' : g < block ∧ g ∉ s.exited
    · simp only [hg', not_false_eq_true, and_self, bind, Except.bind, pure,
        Except.pure] at ht
      cases ht
      change (settle block (insert g s.exited) (s.slots id)).generation = G + 1 at hg1
      have hcomp : complete block (insert g s.exited) (s.slots id) = true := by
        by_contra hc
        rw [settle_pending (by simpa using hc)] at hg1
        omega
      refine hfrom (hfound hsub hexp hcomp) fun i cnt' lanes' si ti hi hri hsi hti hgi => ?_
      obtain ⟨n', hn', he'⟩ := hkept i _ cnt' lanes' si ti hi hri hsi hti hgi
      rw [hexp] at he'
      rw [hn', Option.some.inj he']
    · simp [hg', bind, Except.bind, throw] at ht
  | arrival id' w' c' lanes' =>
    have ht0 := ht
    simp only [Record.perform] at ht
    split_ifs at ht with hl'
    obtain ⟨n', hn', hex, hslots⟩ := arrive_shape ht
    obtain ⟨-, hw'b, -, -, n'', hn'', hk⟩ := arrive_ok_info ht
    have hnn : n' = n'' := Except.ok.inj (hn'.symm.trans hn'')
    subst hnn
    by_cases hi : id = id'
    · subst hi
      have hslot : t.slots id = settle block s.exited
          {s.slots id with expected := some n', arrived := insert w' (s.slots id).arrived} := by
        simpa only [↓reduceIte] using hslots id
      rw [hslot] at hg1
      have hcomp : complete block s.exited
          {s.slots id with expected := some n', arrived := insert w' (s.slots id).arrived} =
            true := by
        by_contra hc
        rw [settle_pending (by simpa using hc)] at hg1
        simp only at hg1
        omega
      -- the requested count is that of all warps
      have hnw : n' = warps block := by
        rcases Nat.lt_or_eq_of_le hji with hjic | hjic
        · obtain ⟨n, hn, hexp⟩ := hkept j w cnt lanes sj tj hjic hj hsj htj hjg
          rw [← hk n hexp]
          exact Except.ok.inj (hn.symm.trans hjn)
        · subst hjic
          rw [hj] at hr
          simp only [Option.some.injEq, Record.arrival.injEq] at hr
          obtain ⟨-, -, rfl, -⟩ := hr
          exact Except.ok.inj (hn'.symm.trans hjn)
      subst hnw
      have hsub' : insert w' (s.slots id).arrived ⊆ Finset.range (warps block) :=
        Finset.insert_subset (Finset.mem_range.mpr hw'b) hsub
      have hx' : l ∉ s.exited := by rw [← hex]; exact hx
      have hmem := complete_all_warps (exited := s.exited) hsub' rfl hcomp hlw
        (warpLive_of_lane hl hx')
      rcases Finset.mem_insert.mp hmem with hww | hmem
      · -- the completing record is the arrival of the warp of `l`
        obtain ⟨q, hq, hql⟩ := List.mem_map.mp ((perform_arrival_lanes ht0).2.2 l hl
          hww hx')
        subst hww
        refine ⟨ic, c', lanes', q.2, s, t, le_refl _, hr, ?_, hs, ht0, hg0, hn'⟩
        have : (l, q.2) = q := by rw [← hql]
        rw [this]
        exact hq
      · refine hfrom hmem fun i cnt' lanes' si ti hi hri hsi hti hgi => ?_
        obtain ⟨n, hn, he⟩ := hkept i _ cnt' lanes' si ti hi hri hsi hti hgi
        rw [hn, hk n he]
    · have hslot : t.slots id = s.slots id := by simpa only [hi, ↓reduceIte] using hslots id
      rw [hslot] at hg1
      omega

/-- **An arrival record in a generation at least `start` follows `start` records of its warp**, on
a barrier whose records follow `PhProtocol`. -/
theorem start_le_ordinal {D : Finset Nat} {cD : Option Nat} {nD start id : Nat}
    (hD : D ⊆ Finset.range (warps block)) (hcard : D.card = nD) (hnD : nD ≠ warps block)
    (hcD : target block cD = .ok nD) {h : List (Record α)} (hp : PhProtocol D cD start id h)
    {i w : Nat} {cnt : Option Nat} {lanes : List (Nat × α)} {s t : State}
    (hs : At block h i s) (ht : Record.perform block s (.arrival id w cnt lanes) = .ok t)
    (hge : start ≤ (s.slots id).generation) : start ≤ idArrivals (h.take i) id w := by
  have hl := phased_run hD hcard hnD hcD (hp.take i) hs
  simp only [Record.perform] at ht
  split_ifs at ht
  obtain ⟨-, hwb, hwl, -, -⟩ := arrive_ok_info ht
  exact (hl.early w (Finset.mem_range.mpr hwb) hwl).2 hge

end
end PTX.NamedBar.GenLedger
