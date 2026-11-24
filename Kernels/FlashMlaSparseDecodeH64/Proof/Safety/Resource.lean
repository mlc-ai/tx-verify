-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.FlashMlaSparseDecodeH64.Proof.Thread.ResourceTrace

public section

/-! # Each CTA's single-warp allocator history replays without a fault -/

namespace PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety

open PTX PTX.Flow PTX.Proof Tmem.Pair

variable {P : Params} {L : Launch} {mem0 : Mem0} {X : Execution}

private def ordinal (L : Launch) (X : Execution) (cta : Nat) (r : Requests) : Nat :=
  opsAt X (cta * L.block) (r.own.indices 0)

private structure RecordData (L : Launch) (X : Execution) (cta : Nat) (r : Requests) : Prop where
  home : r.own.cta = cta
  warp : r.own.warp = 0
  group : r.group = .one
  count : ordinal L X cta r < 3
  request : r.action.request = (opAct 0 (ordinal L X cta r)).request
  lane : ∃ tag dst req, X.get (cta * L.block, r.own.indices 0) =
    some ⟨tag, .tc (.resource .one dst req)⟩

private theorem record_data (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
    {cta : Nat} {r : Requests} (hr : r ∈ X.tmemHistory cta) : RecordData L X cta r := by
  obtain ⟨valid, home, _⟩ := hX.tmemPair.1 cta
  obtain ⟨_, hRequest, hWarp⟩ := valid r hr
  have he := hWarp.2.2.1 0
  have hGeo := (WarpRequest.event_props hWarp 0).2.1
  have hThread : (r.own.event L 0).1 < L.threads := Frame.lt_of_get hX he
  obtain ⟨d, hd⟩ := Frame.event_state hs hX ht he (by simp)
  obtain ⟨hw, hgrp, hn, hShape⟩ := ResourceEvents.ordinal hpre hX (hs _ hThread).machine he hd
  have hw' : r.own.warp = 0 := by
    have h : (r.own.event L 0).1 % L.block / 32 = 0 := by
      rw [hpre.block]
      simpa only [warpOf, tidOf_eq hpre] using hw
    exact hGeo.symm.trans h
  have hHome := home r hr
  refine ⟨hHome, hw', hgrp, ?_, ?_, ?_⟩
  · simpa [ordinal, WarpRequest.event, hw', hHome] using hn
  · rw [hRequest]
    simpa [ordinal, WarpRequest.event, hw', hHome] using hShape
  · exact ⟨_, r.own.dst, r.own.request, by
      simpa [WarpRequest.event, hw', hHome, hgrp] using he⟩

private theorem indices_ordered
    (hX : Consistent L kernel Assumptions.all mem0 X) {cta : Nat}
    (hData : ∀ r ∈ X.tmemHistory cta, RecordData L X cta r) :
    ((X.tmemHistory cta).map (ordinal L X cta)).Pairwise (· < ·) := by
  rw [List.pairwise_map]
  refine (hX.object.tmemOrdered hX.tmemPair cta).imp_of_mem fun {a b} ha hb hab => ?_
  have haData := hData a ha
  have hbData := hData b hb
  have hBefore := hab (haData.home.trans hbData.home.symm) (haData.warp.trans hbData.warp.symm)
  obtain ⟨_, _, _, hget⟩ := haData.lane
  exact tmemOps_lt hget rfl (hBefore.2.2 0)

private theorem first_index_zero {cta : Nat} {r : Requests} (hr : r ∈ X.tmemHistory cta)
    (hOrdinal : ordinal L X cta r = 0)
    (hOrder : ((X.tmemHistory cta).map (ordinal L X cta)).Pairwise (· < ·)) :
    ∃ tail, X.tmemHistory cta = r :: tail := by
  obtain ⟨before, tail, hList⟩ := List.append_of_mem hr
  cases before with
  | nil => exact ⟨tail, hList⟩
  | cons first pre =>
    simp only [hList, List.cons_append, List.map_cons] at hOrder
    have h := (List.pairwise_cons.mp hOrder).1 (ordinal L X cta r) (by simp)
    omega

variable (hpre : Pre P L mem0) (hX : Consistent L kernel Assumptions.all mem0 X)
    (hs : GlobalWrites.SoundThreads P L) (ht : Frame.Tracked (Machine.code P L) X)
include hpre hX hs ht

private theorem performed_record {cta i : Nat} (hp : Performed L X (cta * L.block, i)) :
    ∃ a ∈ X.tmemHistory cta, a.own.indices 0 = i := by
  obtain ⟨key, a, ha, lane, hEvent⟩ := hp
  have hv := record_data hpre hX hs ht ha
  have hThread := congrArg Prod.fst hEvent
  change a.own.cta * L.block + a.own.warp * 32 + lane.val = cta * L.block at hThread
  rw [hv.home, hv.warp] at hThread
  have hRange : lane.val < L.block := by rw [hpre.block]; have := lane.isLt; omega
  have ⟨hKey, hLane⟩ := block_pos_inj (B := L.block) (c := key) (c' := cta)
    (l := lane.val) (l' := 0) hRange (by rw [hpre.block]; decide)
    (by simpa using hThread)
  subst hKey
  have hl : lane = 0 := Fin.ext hLane
  subst lane
  exact ⟨a, ha, congrArg Prod.snd hEvent⟩

private theorem history_has_before {cta i tag : Nat} {kind : Kind}
    (he : X.get (cta * L.block, i) = some ⟨tag, kind⟩) {n : Nat}
    (hn : n < opsAt X (cta * L.block) i) :
    ∃ a ∈ X.tmemHistory cta, ordinal L X cta a = n := by
  let g := cta * L.block
  obtain ⟨j, hj, hjLt, hOp, hCount⟩ :=
    countP_take_occ isTmemOp (X.tr g) i n hn
  have hGet : X.get (g, j) = some (X.tr g)[j] := List.getElem?_eq_getElem hjLt
  obtain ⟨tag, grp, dst, req, hKind⟩ := tmemOp_resource hOp
  rw [hKind] at hGet
  have hLater : (g, j).2 + 1 < (X.tr (g, j).1).length := by
    change j + 1 < (X.tr g).length
    exact Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hj) (PTX.len_of_get he)
  obtain ⟨a, ha, hIdx⟩ :=
    performed_record hpre hX hs ht (hX.tmemPairBlocking.performed hGet hLater)
  exact ⟨a, ha, by simpa [ordinal, hIdx, g, tmemOps] using hCount⟩

private theorem history_has_earlier {cta : Nat} {r : Requests} (hData : RecordData L X cta r)
    {n : Nat} (hn : n < ordinal L X cta r) :
    ∃ a ∈ X.tmemHistory cta, ordinal L X cta a = n := by
  obtain ⟨_, _, _, hGet⟩ := hData.lane
  exact history_has_before hpre hX hs ht hGet hn

omit hpre hX hs ht in
private theorem record_action
    (hX : Consistent L kernel Assumptions.all mem0 X) {cta : Nat} {r : Requests}
    (hr : r ∈ X.tmemHistory cta) (hData : RecordData L X cta r)
    (hOrder : ((X.tmemHistory cta).map (ordinal L X cta)).Pairwise (· < ·)) :
    r.action = opAct 0 (ordinal L X cta r) := by
  have hn := hData.count
  have hReq := hData.request
  generalize hN : ordinal L X cta r = n at hn hReq ⊢
  interval_cases n
  · change r.action.request = .alloc 512 at hReq
    obtain ⟨col, hAction⟩ := Tmem.Action.request_eq_alloc hReq
    obtain ⟨tail, hList⟩ := first_index_zero hr hN hOrder
    have hCol : col = 0 := by
      by_contra hNe
      apply (hX.tmemPair.1 cta).2.2
      rw [hList]
      simp [runRequests, hAction, perform_alloc, hNe]
    subst col
    exact hAction
  · exact Tmem.Action.request_eq_relinquish hReq
  · exact Tmem.Action.request_eq_dealloc hReq

/-- The first allocator record is the full allocation and precedes any gate state. -/
theorem alloc_record_at_gate {cta gate tag : Nat}
    (he : X.get (cta * L.block, gate) = some ⟨tag, .bar 0 none .sync⟩)
    (hGate : Frame.stateAt (Machine.code P L) X (cta * L.block) gate =
      some (some (.prologue .barrier))) :
    ∃ (r : Requests) (ev : Event), r ∈ X.tmemHistory cta ∧ r.own.cta = cta ∧
      r.action = .alloc 512 0 ∧ (r.own.event L 0).1 = cta * L.block ∧
      X.get (r.own.event L 0) = some ev ∧
      ∀ j, Frame.stateAt (Machine.code P L) X (cta * L.block) j =
        some (some (.prologue .barrier)) → (r.own.event L 0).2 < j := by
  let g := cta * L.block
  have hg : g < L.threads := Frame.lt_of_get hX he
  have hw : warpOf L g = 0 := by simp [g, warpOf, tidOf_eq hpre, hpre.block]
  have hCount := ResourceEvents.ops_at_gate hpre hX (hs g hg).machine hg hw hGate
  have hZero : 0 < opsAt X (cta * L.block) gate := hCount.symm ▸ (by decide : 0 < 2)
  obtain ⟨r, hr, hOrd⟩ := history_has_before hpre hX hs ht he hZero
  have hData := fun a ha => record_data hpre hX hs ht (cta := cta) (r := a) ha
  have hv := hData r hr
  have hAct := record_action hX hr hv (indices_ordered hX hData)
  rw [hOrd] at hAct
  have hThread : (r.own.event L 0).1 = g := by simp [WarpRequest.event, hv.home, hv.warp, g]
  have hIdx : (r.own.event L 0).2 = r.own.indices 0 := rfl
  obtain ⟨tag', dst, req, hget⟩ := hv.lane
  refine ⟨r, ⟨tag', .tc (.resource .one dst req)⟩, hr, hv.home, hAct, hThread, ?_, ?_⟩
  · rwa [show r.own.event L 0 = (g, r.own.indices 0) from Prod.ext hThread hIdx]
  · intro j hj
    have hTwo := ResourceEvents.ops_at_gate hpre hX (hs g hg).machine hg hw hj
    by_contra hn
    have hle : j ≤ r.own.indices 0 := by omega
    have hm : opsAt X g j ≤ opsAt X g (r.own.indices 0) :=
      (List.take_sublist_take_left hle).countP_le
    change opsAt X g (r.own.indices 0) = 0 at hOrd
    omega

private theorem history_pattern {cta : Nat} :
    let ns := (X.tmemHistory cta).map (ordinal L X cta)
    ns = [] ∨ ns = [0] ∨ ns = [1] ∨ ns = [0, 1] ∨ ns = [0, 2] ∨ ns = [0, 1, 2] := by
  have hData := fun r hr => record_data hpre hX hs ht (cta := cta) (r := r) hr
  refine ops_pattern (indices_ordered hX hData) ?_ ?_
  · rintro n hn
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hn
    exact Nat.le_of_lt_succ (hData r hr).count
  · intro hTwo
    obtain ⟨r, hr, hOrdinal⟩ := List.mem_map.mp hTwo
    obtain ⟨a, ha, hZero⟩ := history_has_earlier hpre hX hs ht (hData r hr)
      (n := 0) (by omega)
    exact List.mem_map.mpr ⟨a, ha, hZero⟩

/-- The next unrecorded request can be replayed after the actual earlier allocator history. -/
theorem run_before_resource {cta i tag n : Nat} {dst : Option Loc} {r : Requests} (hN : n < 3)
    (hOrd : opsAt X (cta * L.block) i = n)
    (he : X.get (cta * L.block, i) = some ⟨tag, .tc (.resource .one dst (opAct 0 n).request)⟩)
    (hp : ¬ Covered L X (cta * L.block, i)) (hr : r.action = opAct 0 n) :
    runRequests {} (X.tmemHistory cta ++ [r]) ≠ .blocked := by
  have hData := fun a ha => record_data hpre hX hs ht (cta := cta) (r := a) ha
  have hHas (j : Nat) (hj : j < n) :
      j ∈ (X.tmemHistory cta).map (ordinal L X cta) := by
    obtain ⟨a, ha, hOrdA⟩ := history_has_before hpre hX hs ht he (hOrd ▸ hj)
    exact List.mem_map.mpr ⟨a, ha, hOrdA⟩
  have hNo : n ∉ (X.tmemHistory cta).map (ordinal L X cta) := by
    intro hMem
    obtain ⟨a, ha, hOrdA⟩ := List.mem_map.mp hMem
    have hrec := hData a ha
    obtain ⟨atag, addr, req, hGet⟩ := hrec.lane
    have hIdx := tmemOp_unique
      (show TmemOp X (cta * L.block) n (a.own.indices 0) from
        ⟨⟨atag, .one, addr, req, hGet⟩, hOrdA⟩)
      (show TmemOp X (cta * L.block) n i from ⟨⟨tag, .one, dst, _, he⟩, hOrd⟩)
    apply hp
    exact ⟨[a.own], .inl ⟨cta, a, ha, hrec.group, rfl⟩, a.own, by simp, 0, by
      simp [WarpRequest.event, hrec.home, hrec.warp, hIdx]⟩
  have hEarlier {j : Nat} (hj : j ∈ (X.tmemHistory cta).map (ordinal L X cta)) :
      j < n := by
    by_contra! hn
    have hLt : n < j := lt_of_le_of_ne hn (fun h => hNo (h.symm ▸ hj))
    obtain ⟨a, ha, hA⟩ := List.mem_map.mp hj
    obtain ⟨b, hb, hB⟩ := history_has_earlier hpre hX hs ht (hData a ha)
      (n := n) (hA ▸ hLt)
    exact hNo (List.mem_map.mpr ⟨b, hb, hB⟩)
  have hHistory : (X.tmemHistory cta).map (ordinal L X cta) = List.range n := by
    have hZero : 0 ∈ (X.tmemHistory cta).map (ordinal L X cta) ↔ 0 < n :=
      ⟨hEarlier, hHas 0⟩
    have hOne : 1 ∈ (X.tmemHistory cta).map (ordinal L X cta) ↔ 1 < n :=
      ⟨hEarlier, hHas 1⟩
    have hTwo : 2 ∈ (X.tmemHistory cta).map (ordinal L X cta) ↔ 2 < n :=
      ⟨hEarlier, hHas 2⟩
    rcases history_pattern hpre hX hs ht (cta := cta) with h | h | h | h | h | h
    all_goals interval_cases n
    all_goals first | exact h | simp [h] at hZero hOne hTwo
  have hActs : (X.tmemHistory cta).map (·.action) = (List.range n).map (opAct 0) := by
    rw [← hHistory, List.map_map]
    exact List.map_congr_left fun a ha => record_action hX ha (hData a ha)
      (indices_ordered hX hData)
  rw [run_acts, List.map_append, hActs, List.map_singleton, hr]
  interval_cases n <;> decide +kernel

/-- An actual deallocation awaiting its record can follow the allocation and relinquishment. -/
theorem run_before_dealloc {cta i tag : Nat} {r : Requests}
    (he : X.get (cta * L.block, i) = some ⟨tag, .tc (.resource .one none (.dealloc 0 512))⟩)
    (hp : ¬ Covered L X (cta * L.block, i)) (hr : r.action = .dealloc 0 512) :
    runRequests {} (X.tmemHistory cta ++ [r]) ≠ .blocked := by
  have hg := Frame.lt_of_get hX he
  obtain ⟨d, hd⟩ := Frame.event_state hs hX ht he (by simp)
  obtain ⟨_, _, hlt, hreq⟩ := ResourceEvents.ordinal hpre hX (hs _ hg).machine he hd
  have hTwo : opsAt X (cta * L.block) i = 2 := by
    generalize opsAt X (cta * L.block) i = n at hlt hreq ⊢
    interval_cases n <;> first | rfl | contradiction
  exact run_before_resource hpre hX hs ht (by decide) hTwo he hp hr

/-- The allocator history has a successful replay. No record is a paired deallocation. -/
theorem no_resourceUnsafe :
    ¬ Tmem.Pair.ResourceUnsafe L X := by
  rintro ⟨cta, ⟨reason, hFault⟩ | hPending⟩
  · have hData := fun r hr => record_data hpre hX hs ht (cta := cta) (r := r) hr
    have hOrder := indices_ordered hX hData
    refine run_alloc_ok (c := 0) ?_ (history_pattern hpre hX hs ht (cta := cta)) reason hFault
    rw [List.map_map]
    exact List.map_congr_left fun r hr => record_action hX hr (hData r hr) hOrder
  · obtain ⟨_, _, d, _, hd, _, _, hgrp, _⟩ := hPending
    have hData := record_data hpre hX hs ht (List.mem_of_getElem? hd)
    cases hData.group.symm.trans hgrp

/-- A deallocation performed before the lane returns leaves the CTA's allocator empty. -/
theorem released_of_dealloc
    (hDealloc : ∀ cta, cta * L.block < L.threads → ∃ i tag,
      X.get (cta * L.block, i) = some ⟨tag, .tc (.resource .one none (.dealloc 0 512))⟩ ∧
      i + 1 < (X.tr (cta * L.block)).length) : Released X := by
  intro cta s hRun
  cases hh : X.tmemHistory cta with
  | nil =>
    rw [hh] at hRun
    change Tmem.Outcome.done {} = .done s at hRun
    obtain rfl := Tmem.Outcome.done.inj hRun
    rfl
  | cons a rest =>
    have hData := fun r hr => record_data hpre hX hs ht (cta := cta) (r := r) hr
    obtain ⟨_, _, _, hFirst⟩ := (hData a (by simp [hh])).lane
    obtain ⟨i, tag, he, hnext⟩ := hDealloc cta (Frame.lt_of_get hX hFirst)
    obtain ⟨r, hr, hIndex⟩ := performed_record hpre hX hs ht
      (hX.tmemPairBlocking.performed he hnext)
    obtain ⟨d, hd⟩ := Frame.event_state hs hX ht he (by simp)
    obtain ⟨_, _, hn, hReq⟩ :=
      ResourceEvents.ordinal hpre hX (hs _ (Frame.lt_of_get hX he)).machine he hd
    have hTwo : ordinal L X cta r = 2 := by
      rw [ordinal, hIndex]
      generalize opsAt X (cta * L.block) i = n at hn hReq ⊢
      interval_cases n <;> first | rfl | contradiction
    obtain ⟨r', hr', hOne⟩ := history_has_earlier hpre hX hs ht (hData r hr)
      (n := 1) (by omega)
    have hTwoMem : 2 ∈ (X.tmemHistory cta).map (ordinal L X cta) :=
      List.mem_map.mpr ⟨r, hr, hTwo⟩
    have hOneMem : 1 ∈ (X.tmemHistory cta).map (ordinal L X cta) :=
      List.mem_map.mpr ⟨r', hr', hOne⟩
    have hIndices : (X.tmemHistory cta).map (ordinal L X cta) = [0, 1, 2] := by
      rcases history_pattern hpre hX hs ht (cta := cta) with h | h | h | h | h | h
      all_goals first | exact h | simp [h] at hTwoMem hOneMem
    apply run_alloc_released (c := 0) ?_ hRun
    rw [← hIndices, List.map_map]
    exact List.map_congr_left fun r hr => record_action hX hr (hData r hr)
      (indices_ordered hX hData)

end PTX.Kernels.FlashMlaSparseDecodeH64.Proof.Safety
