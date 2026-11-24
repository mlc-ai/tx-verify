-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Step.ClusterProgress

@[expose] public section

/-! # A recorded cluster barrier operation is ready

A proof tool for the progress step at a cluster barrier operation. A record of a valid cluster
history that holds an operation is the record of a live warp (`recorded_warp`): the barrier accepts
it only when it holds every lane of the warp that has not exited (`ClusterBarrier.liveWarp`). So the
operation's warp needs are filled, by the lane's event in the record or by its exit recorded before
it, and the references a wait counts are present events of records (`ready_of_recorded`,
DEP-ORDER). The operation of a thread's last event is then ready exactly when it is recorded. -/

namespace PTX.Step

open PTX

noncomputable section

variable {L : Launch} {X : Execution}

/-- A record of a valid cluster history that holds a cluster barrier operation is an arrival or
wait record of a live warp: its lanes are cluster-local threads backed by their events, and every
lane of the warp that has not exited before the record is among them. -/
theorem recorded_warp (hc : ClusterHistoryOk L X) {c i : Nat} {r : ClusterBarrier.Record EvId}
    {e : EvId} {pc : Nat} {op : ClusterOp} (he : X.get e = some ⟨pc, .cluster op⟩)
    (hi : (X.clusters c)[i]? = some r) (her : e ∈ r.refs) :
    ∃ u cta warp, ∃ lanes : List (Nat × EvId), r.refs = lanes.map Prod.snd ∧
      ClusterBarrier.run L.block (L.clusterSizeAt c) {} ((X.clusters c).take i) = .done u ∧
      ClusterBarrier.liveWarp L.block (L.clusterSizeAt c) u cta warp (lanes.map Prod.fst) = true ∧
      ∀ p ∈ lanes, p.1 < L.block * L.clusterSizeAt c ∧
        p.2.1 = L.clusterStart c * L.block + p.1 := by
  have hmem := List.mem_of_getElem? hi
  have hcn : c < L.nclusters := by
    by_contra hn
    rw [hc.2.1 c (by omega)] at hmem
    cases hmem
  obtain ⟨-, hsrc, s, hs⟩ := hc.2.2 c hcn
  have hsplit : X.clusters c = (X.clusters c).take i ++ r :: (X.clusters c).drop (i + 1) := by
    have hlt := (List.getElem?_eq_some_iff.mp hi).1
    conv_lhs => rw [← List.take_append_drop i (X.clusters c)]
    rw [List.drop_eq_getElem_cons hlt, (List.getElem?_eq_some_iff.mp hi).2]
  rw [hsplit, ClusterBarrier.run_append] at hs
  cases hu : ClusterBarrier.run L.block (L.clusterSizeAt c) {} ((X.clusters c).take i) with
  | blocked => rw [hu] at hs; cases hs
  | fault f => rw [hu] at hs; cases hs
  | done u =>
    rw [hu] at hs
    simp only [ClusterBarrier.run] at hs
    have hsr := hsrc r hmem
    cases r with
    | exit g y =>
      simp only [ClusterBarrier.Record.refs, List.mem_singleton] at her
      subst her
      obtain ⟨-, -, pc', hget⟩ := hsr
      rw [hget] at he
      cases he
    | arrival cta warp release lanes =>
      refine ⟨u, cta, warp, lanes, rfl, rfl, ?_, fun p hp => ⟨(hsr p hp).1, (hsr p hp).2.1⟩⟩
      by_contra hn
      simp only [Bool.not_eq_true] at hn
      simp [ClusterBarrier.Record.perform, hn] at hs
    | wait cta warp lanes =>
      refine ⟨u, cta, warp, lanes, rfl, rfl, ?_, fun p hp => ⟨(hsr p hp).1, (hsr p hp).2.1⟩⟩
      by_contra hn
      simp only [Bool.not_eq_true] at hn
      simp [ClusterBarrier.Record.perform, hn] at hs

/-- **A recorded cluster barrier operation is ready.** A record of a valid history that holds the
operation holds an event of every lane of its warp that had not exited before the record, and the
exit of every other lane is recorded before it (`liveWarp`); every reference that a wait counts is a
present event of a record. -/
theorem ready_of_recorded (hc : ClusterHistoryOk L X) {e : EvId} {pc : Nat} {op : ClusterOp}
    (he : X.get e = some ⟨pc, .cluster op⟩) (hrec : ClusterRecorded L X e) : Ready L X e := by
  obtain ⟨r, hr, her⟩ := hrec
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
  obtain ⟨u, cta, warp, lanes, hrefs, hu, hlive, hsrc⟩ := recorded_warp hc he hi her
  have hcn : L.clusterOfCta (e.1 / L.block) < L.nclusters := by
    by_contra hn
    rw [hc.2.1 _ (by omega)] at hr
    cases hr
  have her' := her
  rw [hrefs] at her'
  obtain ⟨p, hp, hpe⟩ := List.mem_map.mp her'
  obtain ⟨hb, -, -, -, -, hall, hcover⟩ := of_decide_eq_true hlive
  obtain ⟨-, hpc, hpw, -⟩ := hall p.1 (List.mem_map_of_mem hp)
  have hpe1 := (hsrc p hp).2
  rw [hpe] at hpe1
  intro n hn
  simp only [Needs, he, KindNeeds, clusterNeeds, List.mem_append] at hn
  rcases hn with hwn | hcount
  · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hwn
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hh
    rw [List.mem_range] at hl
    unfold warpSize at hl
    rw [lt_min_iff] at hl
    generalize hS : L.clusterStart (L.clusterOfCta (e.1 / L.block)) * L.block = S at hpe1
    have hmod : e.1 % L.block = p.1 % L.block := by
      rw [hpe1, ← hS, Nat.add_comm, Nat.add_mul_mod_self_right]
    have hd := Nat.div_add_mod p.1 L.block
    rw [hpc] at hd
    have hd2 := Nat.div_add_mod (p.1 % L.block) 32
    rw [hpw] at hd2
    rw [hmod] at hl
    have hlt : warp * 32 + l < L.block := by omega
    have hh : warpLane L e.1 l = S + (cta * L.block + (warp * 32 + l)) := by
      unfold warpLane laneOf
      rw [hmod, hpe1]
      rw [Nat.mul_comm] at hd
      omega
    by_cases hx : cta * L.block + (warp * 32 + l) ∈ u.exited
    · rcases ClusterPhase.run_exited_source hu hx with h0 | ⟨y, hy⟩
      · simp at h0
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hy
      have hji : j < i := by
        have := (List.getElem?_eq_some_iff.mp hj).1
        simp only [List.length_take] at this
        omega
      simp only [List.getElem?_take, hji, ↓reduceIte] at hj
      have hcn' := hcn
      obtain ⟨-, hsrcs, -⟩ := hc.2.2 _ hcn'
      obtain ⟨-, hy1, pcy, hgy⟩ := hsrcs _ (List.mem_of_getElem? hj)
      rw [hS] at hy1
      exact ⟨.thread y, ⟨_, hgy⟩, i, r, y, hi, her, rfl, by rw [hh, hy1],
        .inr ⟨j, _, hji, hj⟩⟩
    · obtain ⟨q, hq, hq1⟩ := List.mem_map.mp (hcover l (Finset.mem_range.mpr hl.1) hlt hx)
      have hq2 := (hsrc q hq).2
      rw [hS, hq1] at hq2
      refine ⟨.thread q.2, hc.ref_present hr (by rw [hrefs]; exact List.mem_map_of_mem hq), i, r,
        q.2, hi, her, rfl, by rw [hh, hq2], .inl ?_⟩
      rw [hrefs]
      exact List.mem_map_of_mem hq
  · cases op with
    | arrive release aligned => simp at hcount
    | wait aligned =>
      obtain ⟨y, hy, hcc⟩ := List.mem_flatMap.mp hcount
      unfold needsIf at hcc
      split at hcc
      · rw [List.mem_singleton] at hcc
        subst hcc
        obtain ⟨r', hr', hyr⟩ := List.mem_flatMap.mp hy
        exact ⟨.thread y, hc.ref_present hr' hyr, rfl⟩
      · simp at hcc

end

end PTX.Step
