-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Protocol.NamedBarPhaseKeys

@[expose] public section

/-!
# Pending arrivals of a named barrier that serves several thread counts

`NamedBar.no_duplicate_arrival` asks one thread count for every arrival on a barrier id. A barrier
that serves a loop group with a count and the whole CTA without one (Inkling's barrier 0) does not
have it, so its two halves are separated here:

* `Multi.no_dup_pending`: a pending (unrecorded) `bar.sync` lane whose warp has already arrived in
  the open generation is impossible, whatever the counts are: the warp's arrival in that
  generation is an earlier event of the same lane, which was passed, so its generation is
  released;
* `Multi.pending_ordinal`: the source ordinal of a pending `bar.sync` equals the number of arrival
  records of its warp on the barrier;
* `Multi.NoMismatch`, `Multi.no_fault_of_mismatch`: a CTA barrier fault is a count mismatch with an
  arrival of the open generation, which a kernel excludes from its own facts.
-/

namespace PTX.NamedBar.Multi
open PTX CtaBarrier
noncomputable section

variable {L : Launch} {X : Execution} {K : Kernel} {A : List Assumption} {mem0 : Mem0}
  [hK : Fact K.NoBarArrive]

/-- **A pending `bar.sync` of a warp that has arrived in the open generation is impossible.** The
lane `g` of CTA `c` has the unrecorded `bar.sync` event `e`; the warp of `g` is in the arrived set
of the final state `s` of the CTA's history; the lane is not exited. -/
theorem no_dup_pending (hX : Consistent L K A mem0 X) {c : Nat} (hc : c < L.grid) {s : State}
    (hrun : run L.block {} (X.barriers c) = .ok s) {id g pc : Nat} {cnt : Option Nat}
    {e : EvId} (hgb : g < L.block) (he1 : e.1 = c * L.block + g)
    (hb : X.IsBarrier e id cnt pc) (hfree : e ∉ (X.barriers c).flatMap Record.refs)
    (hgx : g ∉ s.exited) (hdup : g / 32 ∈ (s.slots id).arrived) : False := by
  obtain ⟨hnd, hsrcs, -⟩ := hX.ctaBar.2 c hc
  have hslot := (slotFrom_run hrun) id
  have hdiv : e.1 / L.block = c := by rw [he1]; exact lane_div hgb
  obtain ⟨i, u, cnt', lanes', t, hi, ha, hgen, hp'⟩ := hslot.1 (g / 32) hdup
  have hxu : g ∉ u.exited := fun hx => hgx (at_exited_mono ha hrun hx)
  obtain ⟨⟨_, e'⟩, hm', hge'⟩ := List.mem_map.mp (perform_arrival_lane hp' hgb rfl hxu)
  simp only at hge'
  subst hge'
  obtain ⟨-, he1', pc', mode', hb'⟩ := hsrcs _ (List.mem_of_getElem? hi) (_, e') hm'
  simp only at he1' hb'
  have hrec' : e' ∈ (X.barriers c).flatMap Record.refs :=
    List.mem_flatMap.mpr ⟨_, List.mem_of_getElem? hi, List.mem_map.mpr ⟨(_, e'), hm', rfl⟩⟩
  have hne : e ≠ e' := fun h => hfree (h ▸ hrec')
  have hsame : e.1 = e'.1 := he1.trans he1'.symm
  have hel := len_of_get hb
  have hel' := len_of_get hb'
  have hlt' : e'.2 < e.2 := by
    by_contra hge
    have hne2 : e.2 ≠ e'.2 := fun h2 => hne (Prod.ext hsame h2)
    rw [← hsame] at hel'
    exact barrier_unrecorded_last hX hb (by rw [hdiv]; exact hfree) (by omega)
  have hge' : e'.1 < L.threads := by rw [he1']; exact cta_thread_lt hc hgb
  have hdiv' : e'.1 / L.block = c := by rw [← hsame]; exact hdiv
  have hgo := generationOf_of_record (L := L) hi ha hp' hm'
  have hid : id < 16 := hX.ctaBar.arrival_id_lt hi
  have hrel : Released L.block (X.barriers c) id (u.slots id).generation := by
    have hpass : e'.2 + 1 < (X.tr e'.1).length := by rw [← hsame]; omega
    have hb'' : X.IsBarrier e' id cnt' pc' := hX.isBarrier_of_arrival hK.out ⟨mode', hb'⟩
    obtain ⟨key, hk, hdone'⟩ := ctaBarDone_of_returned hX hb'' hpass
    have hgk := hk.2.2
    rw [hdiv'] at hgk
    obtain ⟨hid', hph⟩ := GenerationOf.unique hnd hgk hgo
    unfold CtaBarDone at hdone'
    rwa [hdiv', hid', hph] at hdone'
  have := released_generation_lt hrun hrel
  omega

/-- **A pending `bar.sync` is the next event of its lane**: the source ordinal of an unrecorded
`bar.sync` of a lane that never exits is the number of arrival records of the lane's warp on the
barrier. -/
theorem pending_ordinal (hX : Consistent L K A mem0 X) {c : Nat} (hc : c < L.grid) {s : State}
    (hrun : run L.block {} (X.barriers c) = .ok s) {id g pc : Nat} {cnt : Option Nat}
    {e : EvId} (hgb : g < L.block) (he1 : e.1 = c * L.block + g)
    (hb : X.IsBarrier e id cnt pc) (hfree : e ∉ (X.barriers c).flatMap Record.refs)
    (hgx : g ∉ s.exited) :
    ((X.tr e.1).take e.2).countP (Execution.isBarId id) =
      idArrivals (X.barriers c) id (g / 32) := by
  obtain ⟨-, hsrcs, -⟩ := hX.ctaBar.2 c hc
  have hdiv : e.1 / L.block = c := by rw [he1]; exact lane_div hgb
  have hge : e.1 < L.threads := by rw [he1]; exact cta_thread_lt hc hgb
  have hlastev : ¬ e.2 + 1 < (X.tr e.1).length :=
    barrier_unrecorded_last hX hb (by rw [hdiv]; exact hfree)
  have hel := len_of_get hb
  have hbid : Execution.isBarId id ⟨pc, .bar id cnt .sync⟩ = true := by simp [Execution.isBarId]
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · -- fewer events than records: the record of the lane's warp with the ordinal of `e` has `e`
    have hocc : ((X.tr e.1).take e.2).countP (Execution.isBarId id) <
        (X.barriers c).countP (isWarpIdArrival id (g / 32)) := hlt
    obtain ⟨index, r, hi, hsel, hprior⟩ := countP_index hocc
    cases r with
    | exit _ _ => simp [isWarpIdArrival] at hsel
    | arrival other warp cnt' lanes =>
      have hfields : other = id ∧ warp = g / 32 := by
        simpa only [isWarpIdArrival, Bool.and_eq_true, beq_iff_eq] using hsel
      obtain ⟨rfl, rfl⟩ := hfields
      obtain ⟨before, after, hbefore, hafter⟩ := run_at_record hrun hi
      have hil := (List.getElem?_eq_some_iff.mp hi).1
      have hnot : g ∉ before.exited := fun hm => hgx (exited_prefix (j := (X.barriers c).length)
        hil.le hbefore (by unfold At; rw [List.take_length]; exact hrun) hm)
      obtain ⟨pair, hpair, hpairg⟩ := List.mem_map.mp
        ((perform_arrival_lanes hafter).2.2 g hgb rfl hnot)
      have hpge : (g, pair.2) = pair := by rw [← hpairg]
      have hmem : (g, pair.2) ∈ lanes := hpge.symm ▸ hpair
      obtain ⟨hql, hq2, hqw, ⟨pce, hbar⟩, hord, -⟩ := record_ordinal hX hc hrun hi hbefore hmem
      obtain ⟨mode, hget⟩ := hbar
      have hbar' : X.IsBarrier pair.2 other cnt' pce := hX.isBarrier_of_arrival hK.out ⟨mode, hget⟩
      have hee : pair.2.1 = e.1 := by rw [hq2, he1]
      have hee' : pair.2 = (e.1, pair.2.2) := Prod.ext hee rfl
      have he'' : X.IsBarrier (e.1, pair.2.2) other cnt' pce := hee' ▸ hbar'
      rw [hee] at hord
      have h2 : e.2 = pair.2.2 :=
        source_ordinal_unique (X := X) hb he'' (by rw [← hord]; exact hprior.symm)
      have hef : pair.2 = e := Prod.ext hee h2.symm
      exact hfree (List.mem_flatMap.mpr ⟨_, List.mem_of_getElem? hi,
        List.mem_map.mpr ⟨(g, pair.2), hmem, hef⟩⟩)
  · -- more events than records: an earlier event has the ordinal of the missing record
    have hocc : idArrivals (X.barriers c) id (g / 32) <
        ((X.tr e.1).take e.2).countP (Execution.isBarId id) := hgt
    obtain ⟨j, x, hj, hx, hxord⟩ := countP_index
      (xs := (X.tr e.1).take e.2) (p := Execution.isBarId id) hocc
    have hjl : j < e.2 := by
      have := (List.getElem?_eq_some_iff.mp hj).1
      simp only [List.length_take] at this
      omega
    rw [List.getElem?_take_of_lt hjl] at hj
    obtain ⟨pcx, cx, mx, rfl⟩ := isBarId_form hx
    have hxf : X.IsBarArrival (e.1, j) id cx pcx := ⟨mx, hj⟩
    have hxb : X.IsBarrier (e.1, j) id cx pcx := hX.isBarrier_of_arrival hK.out hxf
    obtain ⟨key, hk, -⟩ := ctaBarDone_of_returned hX hxb (by simp only; omega)
    have hkid : key % 16 = id := by
      obtain ⟨count', pc'', he'⟩ := hk.2.1
      exact (Kind.bar.inj (Event.mk.inj (Option.some.inj (he'.symm.trans hxb))).2).1
    have hgen := hk.2.2
    rw [hkid] at hgen
    simp only at hgen
    rw [hdiv] at hgen
    obtain ⟨i, s1, warp, cnt', lanes, g', hi, hs1, hm, hphase, t1, ht1⟩ := hgen
    obtain ⟨hql, hq2, hqw, -, hord, -⟩ := record_ordinal hX hc hrun hi hs1 hm
    have hq1 : g' = g := by
      have h1 : e.1 = c * L.block + g' := by simpa using hq2
      omega
    subst hq1
    have hrec : idArrivals ((X.barriers c).take (i + 1)) id (g' / 32) =
        idArrivals ((X.barriers c).take i) id (g' / 32) + 1 := by
      unfold idArrivals
      rw [List.take_add_one, hi]
      simp [List.countP_append, isWarpIdArrival, hqw]
    have hmono : idArrivals ((X.barriers c).take (i + 1)) id (g' / 32) ≤
        idArrivals (X.barriers c) id (g' / 32) :=
      (List.take_sublist _ _).countP_le
    have hordj : idArrivals ((X.barriers c).take i) id (g' / 32) =
        ((X.tr e.1).take j).countP (Execution.isBarId id) := by rw [hqw]; simpa using hord
    rw [List.take_take, Nat.min_eq_left hjl.le] at hxord
    omega

/-- **No count mismatch**: the pending `bar.sync` lane `e` of a lane `g` of CTA `c` whose warp has
not arrived in the open generation of barrier `id` (expected count `k`) has the open generation's
count: no record `i` of the open generation, with a lane `(g2, e2)`, has a count that decodes to
`k` while the pending lane's decodes to `n ≠ k`. -/
def NoMismatch (L : Launch) (X : Execution) : Prop :=
  ∀ {c : Nat}, c < L.grid → ∀ {s : State}, run L.block {} (X.barriers c) = .ok s →
    ∀ {id g pc k n : Nat} {cnt : Option Nat} {e : EvId}, g < L.block →
      e.1 = c * L.block + g → X.IsBarrier e id cnt pc →
      e ∉ (X.barriers c).flatMap Record.refs → g ∉ s.exited →
      g / 32 ∉ (s.slots id).arrived → (s.slots id).expected = some k →
      target L.block cnt = .ok n → k ≠ n →
      ∀ {i : Nat} {u t : State} {w2 : Nat} {cnt2 : Option Nat} {lanes2 : List (Nat × EvId)}
        {g2 : Nat} {e2 : EvId}, (X.barriers c)[i]? = some (.arrival id w2 cnt2 lanes2) →
        At L.block (X.barriers c) i u → (u.slots id).generation = (s.slots id).generation →
        target L.block cnt2 = .ok k →
        Record.perform L.block u (.arrival id w2 cnt2 lanes2) = .ok t →
        (g2, e2) ∈ lanes2 → False

/-- **No CTA barrier arrival faults, given that no arrival is a count mismatch.** The second
premise of `no_duplicate_arrival` (one count per barrier) is replaced by `hmis`. A second arrival
in a generation is `no_dup_pending`. -/
theorem no_fault_of_mismatch (hX : Consistent L K A mem0 X) (hmis : NoMismatch L X) :
    ¬ CtaBarFault L X := by
  rintro ⟨c, hc, s, hrun, id, warp, count, lanes, err, hsrc, hfree, hp, hfault⟩
  have hslot := (slotFrom_run hrun) id
  simp only [Record.perform] at hp
  split_ifs at hp with hl
  · obtain ⟨hlive, n, hn, hcase⟩ := arrive_error_cases hp hfault
    obtain ⟨lane, hlr, hgb, hgx⟩ := hlive
    have hlt := Finset.mem_range.mp hlr
    obtain ⟨⟨g, e⟩, hm, hge⟩ := List.mem_map.mp (hl.2.2 lane hlr hgb hgx)
    simp only at hge
    subst hge
    obtain ⟨-, he1, pc, mode, hb⟩ := hsrc _ hm
    simp only at he1 hb
    have hbar : X.IsBarrier e id count pc := hX.isBarrier_of_arrival hK.out ⟨mode, hb⟩
    have hwarp : (warp * 32 + lane) / 32 = warp := by omega
    have hdupcase : warp ∈ (s.slots id).arrived → False := fun hdup =>
      no_dup_pending hX hc hrun hgb he1 hbar (hfree _ hm) hgx (by rw [hwarp]; exact hdup)
    rcases hcase with hdup | ⟨k, hk, hkn⟩
    · exact hdupcase hdup
    · by_cases hdup : warp ∈ (s.slots id).arrived
      · exact hdupcase hdup
      · obtain ⟨i, u, w2, cnt2, lanes2, t, hi, ha, hgen, htg, hp2⟩ := hslot.2 k hk
        obtain ⟨g2, e2, hm2⟩ := record_live_lane (L := L) hp2
        exact hmis hc hrun hgb he1 hbar (hfree _ hm) hgx (by rw [hwarp]; exact hdup) hk hn hkn
          hi ha hgen htg hp2 hm2
  · cases hp
    simp [Error.isFault] at hfault


end
end PTX.NamedBar.Multi
