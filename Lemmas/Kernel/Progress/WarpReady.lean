-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Kernel.Progress.Blocked
public import Lemmas.Step.CtaBarNamed
import Lemmas.CtaBarrier.CtaBarrierIdSourceCount
import Lemmas.Protocol.NamedBarArrive
import Lemmas.CtaBarrier.CtaBarrierIdentity
import Lemmas.Step.WarpLanes
import Lemmas.Tcgen05.TcCollectiveOrdinaryWaiting

@[expose] public section

/-! # A blocking event of a warp that is ready for one lane is ready for the other

A `bar.sync` is recorded by its warp's arrival, which holds every live lane of the warp; a
warp-collective `tcgen05` event waits for every lane of the warp. So of two lanes of a warp at the
same barrier event, or with no more such `tcgen05` events, the readiness of one lane's event is the
other's. -/

namespace PTX.Sched
open PTX

variable {K : Kernel} {A : List Assumption} {mem0 : Mem0} {L : Launch} {X : Execution}

/-- **The barrier event of a lane of the warp in the record of a ready one**: of the same ordinal
and generation. -/
theorem record_lane (hX : Consistent L K A mem0 X) {g h j pc id : Nat}
    {cnt : Option Nat} {md : BarMode} (hg : g < L.threads) (hsw : SameWarp L g h)
    (he : X.get (g, j) = some ⟨pc, .bar id cnt md⟩) (hr : Ready L X (g, j))
    (hnx : ∀ k pc, X.get (h, k) ≠ some ⟨pc, .exit⟩) :
    ∃ j' key, CtaBarArrivalK L X (g, j) key ∧ CtaBarArrivalK L X (h, j') key ∧ key % 16 = id ∧
      (∃ pc' cnt' md', X.get (h, j') = some ⟨pc', .bar id cnt' md'⟩) ∧
      ((X.tr h).take j').countP (Execution.isBarId id) =
        ((X.tr g).take j).countP (Execution.isBarId id) := by
  have hh := hsw.1.2.1
  have hcta : h / L.block = g / L.block := hsw.1.2.2.symm
  have hb : 0 < L.block := NamedBar.block_pos_of_thread_lt hg
  have hc : g / L.block < L.grid := (Nat.div_lt_iff_lt_mul hb).mpr hg
  obtain ⟨hnd, hsrcs, last, hlast⟩ := hX.ctaBar.2 _ hc
  have hneeds : Needs L X (g, j) = ctaBarNeeds L X (g, j) md := by
    simp only [Needs, he, KindNeeds]
  obtain ⟨x, -, i, r, y, hi, hmem, rfl, hy1, hy⟩ := hr (.node _) (by
    rw [hneeds]
    unfold ctaBarNeeds
    exact List.mem_append_left _ (List.mem_map.mpr
      ⟨h, mem_warpLanes_of_sameWarp (sameWarp_symm hsw), rfl⟩))
  obtain ⟨yh, yj⟩ := y
  simp only at hy1
  subst hy1
  simp only at hi hmem
  have hsrc := hsrcs r (List.mem_of_getElem? hi)
  have hyr : (yh, yj) ∈ r.refs := by
    rcases hy with hy | ⟨j0, g0, -, hex⟩
    · exact hy
    · obtain ⟨-, -, pc0, h0⟩ := hsrcs _ (List.mem_of_getElem? hex)
      exact absurd h0 (hnx _ _)
  obtain ⟨s, t, hat, hperf⟩ := CtaBarrier.run_at_record hlast hi
  cases r with
  | exit x0 y0 =>
    exfalso
    obtain ⟨-, -, pc0, h0⟩ := hsrc
    simp only [CtaBarrier.Record.refs, List.mem_singleton] at hmem
    rw [← hmem, he] at h0
    cases h0
  | arrival id' w count lanes =>
    obtain ⟨⟨g0, y0⟩, hm0, hy0⟩ := List.mem_map.mp hmem
    obtain ⟨⟨g1, y1⟩, hm1, hy1⟩ := List.mem_map.mp hyr
    simp only at hy0 hy1
    subst hy0 hy1
    obtain ⟨hg0, ht0, pc0, md0, h0⟩ := hsrc _ hm0
    obtain ⟨hg1, ht1, pc1, md1, h1⟩ := hsrc _ hm1
    simp only at h0 h1 ht0 ht1 hg0 hg1
    have hid : id' = id := by
      rw [he] at h0
      simp only [Option.some.injEq, Event.mk.injEq, Kind.bar.injEq] at h0
      exact h0.2.1.symm
    subst hid
    have hl0 := (CtaBarrier.perform_arrival_lanes hperf).2.1 _ hm0
    have hl1 := (CtaBarrier.perform_arrival_lanes hperf).2.1 _ hm1
    simp only at hl0 hl1
    have o0 := cta_prefix_id_arrival_count (id := id') hX hc hi hmem hat hg0 ht0 hl0.2.2 rfl
    have o1 := cta_prefix_id_arrival_count (id := id') hX hc hi hyr hat hg1 ht1 hl1.2.2 rfl
    rw [hl0.2.1] at o0
    rw [hl1.2.1] at o1
    have hlt : id' < 16 := hX.ctaBar.arrival_id_lt hi
    refine ⟨yj, id' + 16 * (s.slots id').generation,
      CtaBarArrivalK.of_generation hX.ctaBar hg hlt
        ⟨i, s, w, count, lanes, g0, hi, hat, hm0, rfl, t, hperf⟩,
      CtaBarArrivalK.of_generation hX.ctaBar hh hlt (by
        simp only [hcta]; exact ⟨i, s, w, count, lanes, g1, hi, hat, hm1, rfl, t, hperf⟩),
      by omega, ⟨pc1, count, md1, h1⟩, ?_⟩
    rw [← o0, ← o1]

/-- **A barrier event ready for a lane is ready for a lane of its warp** that has not exited, at its
event of the same form and ordinal. -/
theorem bar_ready_lane (hX : Consistent L K A mem0 X) {g h j j' pc pc' id : Nat}
    {cnt cnt' : Option Nat} {md : BarMode} (hg : g < L.threads) (hsw : SameWarp L g h)
    (he : X.get (g, j) = some ⟨pc, .bar id cnt md⟩) (hr : Ready L X (g, j))
    (he' : X.get (h, j') = some ⟨pc', .bar id cnt' md⟩)
    (hord : ((X.tr h).take j').countP (Execution.isBarId id) =
      ((X.tr g).take j).countP (Execution.isBarId id))
    (hnx : ∀ k pc, X.get (h, k) ≠ some ⟨pc, .exit⟩) : Ready L X (h, j') := by
  have hcta : h / L.block = g / L.block := hsw.1.2.2.symm
  obtain ⟨y, key, hk, hk', hid, ⟨pc1, cnt1, md1, h1⟩, ho⟩ := record_lane hX hg hsw he hr hnx
  obtain rfl : y = j' := NamedBar.ordinal_unique (X := X) (g := h) h1 he'
    (by simp [Execution.isBarId]) (by simp [Execution.isBarId]) (ho.trans hord.symm)
  cases md with
  | arrive => exact NamedBar.ready_of_arrivalK hX.ctaBar he' hk'
  | sync =>
    have hneeds : Needs L X (g, j) = ctaBarNeeds L X (g, j) .sync := by
      simp only [Needs, he, KindNeeds]
    obtain ⟨key2, hk2, hd⟩ := hr (.cond _) (by
      rw [hneeds]
      unfold ctaBarNeeds
      exact List.mem_append_right _ (List.mem_cons_self ..))
    have hkK : CtaBarK L X (g, j) key := ⟨hk.1, ⟨cnt, pc, by rw [hid]; exact he⟩, hk.2.2⟩
    obtain rfl : key2 = key := CtaBarK.key_unique hX.ctaBar hk2 hkK
    refine NamedBar.ready_of_released hX.ctaBar he' (key := key2)
      ⟨hk'.1, ⟨cnt', pc', ?_⟩, hk'.2.2⟩ (by simpa only [hcta] using hd)
    rw [hid]; exact he'

/-- **A warp-collective `tcgen05` event is ready** when a lane of its warp has a ready one of at
least its ordinal. -/
theorem tc_ready_lane {g h j j' pc pc' k : Nat} {t t' : TcKind}
    (hsw : SameWarp L g h) (he : X.get (g, j) = some ⟨pc, .tc t⟩)
    (ht : ∀ grp dst act, t ≠ .resource grp dst act) (hk : X.TcK (g, j) k) (hr : Ready L X (g, j))
    (he' : X.get (h, j') = some ⟨pc', .tc t'⟩) (ht' : ∀ grp dst act, t' ≠ .resource grp dst act)
    {k' : Nat} (hk' : X.TcK (h, j') k') (hle : k' ≤ k) : Ready L X (h, j') := by
  have hn : Needs L X (g, j) = tcNeeds L X (g, j) := by
    obtain ⟨ev, hev, hc⟩ := hk.1
    rw [he] at hev
    cases hev
    unfold Needs
    rw [he]
    cases t <;> first | exact (ht _ _ _ rfl).elim | rfl | simp [isTcColl] at hc
  refine tc_ready_of_done hsw.1.2.1 he' ht' hk' fun y hy hhy => ?_
  have hgy : SameWarp L g y := Step.sameWarp_trans hsw hhy
  obtain ⟨x, -, i, -, hi⟩ := hr (.node _) (by
    rw [hn]
    exact List.mem_map.mpr ⟨y, mem_warpLanes_of_sameWarp (sameWarp_symm hgy), rfl⟩)
  obtain ⟨⟨ev, hev, hc⟩, hcnt⟩ := hi
  simp only at hcnt
  rw [hk.2] at hcnt
  -- the lane's event of the earlier ordinal
  rcases Nat.lt_or_eq_of_le hle with hlt | rfl
  · obtain ⟨i', ev', hi', hc', hcnt'⟩ := NamedBar.exists_ordinal isTcColl (X.tr y)
      (r := k') (Nat.lt_of_lt_of_le (by rw [← hcnt] at hlt; exact hlt)
        (List.take_sublist i (X.tr y)).countP_le)
    exact ⟨i', ⟨ev', hi', hc'⟩, hcnt'⟩
  · exact ⟨i, ⟨ev, hev, hc⟩, hcnt⟩

end PTX.Sched
