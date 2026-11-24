-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tmem.TmemPairHistory
public import Lemmas.Tmem.TmemPairOrder
public import Lemmas.Kernel.Correct
public import Lemmas.Tmem.TmemPairSize
public import Lemmas.Execution.ExecutionGrowth
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases

namespace PTX.Tests.TmemPairHistory
open Tmem.Pair
noncomputable section

private def L : Launch := { grid := 2, block := 64, params := fun _ => none, clusterSize := 2 }
private def request (cta warp index : Nat) (a : Tmem.Action) : WarpRequest :=
  ⟨cta, warp, fun _ => index, 10 + index,
    match a with | .alloc .. => some ⟨.shared, cta, 0⟩ | _ => none, a.request⟩
private def ent (cta warp index : Nat) (a : Tmem.Action) : Requests :=
  ⟨request cta warp index a, .two, a⟩
private def act0 : Nat → Tmem.Action
  | 0 => .alloc 64 0 | 1 => .dealloc 0 64 | 2 => .alloc 32 0 | _ => .dealloc 0 32
private def act1 : Nat → Tmem.Action
  | 0 => .alloc 64 128 | 1 => .dealloc 128 64 | 2 => .alloc 32 128 | _ => .dealloc 128 32
/-- CTA 0's warp 0 and CTA 1's warp 1 each perform two lifetimes, reusing their addresses. -/
private def h0 : List Requests := [ent 0 0 0 (.alloc 64 0), ent 0 0 1 (.dealloc 0 64),
  ent 0 0 2 (.alloc 32 0), ent 0 0 3 (.dealloc 0 32)]
private def h1 : List Requests := [ent 1 1 0 (.alloc 64 128), ent 1 1 1 (.dealloc 128 64),
  ent 1 1 2 (.alloc 32 128), ent 1 1 3 (.dealloc 128 32)]
private def pairs : List (WarpRequest × WarpRequest) :=
  [0, 1, 2, 3].map fun i => (request 0 0 i (act0 i), request 1 1 i (act1 i))
private def event (w : WarpRequest) : Event := ⟨w.pc, .tc (.resource .two w.dst w.request)⟩
private def X : Execution := {
  tr := fun g => if g < 32 then h0.map (event ·.own)
    else if 96 ≤ g ∧ g < 128 then h1.map (event ·.own) else [],
  rf := fun _ _ => none }

private theorem valid0 (i : Nat) (hi : i < 4) : (request 0 0 i (act0 i)).Valid L X .two := by
  interval_cases i
  all_goals refine ⟨by decide, by decide, fun lane => by fin_cases lane <;> rfl, ?_⟩
  · exact ⟨0, fun lane => by fin_cases lane <;> exact ⟨⟨_, rfl, rfl⟩, rfl⟩⟩
  · exact ⟨1, fun lane => by fin_cases lane <;> exact ⟨⟨_, rfl, rfl⟩, rfl⟩⟩
  · exact ⟨2, fun lane => by fin_cases lane <;> exact ⟨⟨_, rfl, rfl⟩, rfl⟩⟩
  · exact ⟨3, fun lane => by fin_cases lane <;> exact ⟨⟨_, rfl, rfl⟩, rfl⟩⟩

private theorem valid1 (i : Nat) (hi : i < 4) : (request 1 1 i (act1 i)).Valid L X .two := by
  interval_cases i
  all_goals refine ⟨by decide, by decide, fun lane => by fin_cases lane <;> rfl, ?_⟩
  · exact ⟨0, fun lane => by fin_cases lane <;> exact ⟨⟨_, rfl, rfl⟩, rfl⟩⟩
  · exact ⟨1, fun lane => by fin_cases lane <;> exact ⟨⟨_, rfl, rfl⟩, rfl⟩⟩
  · exact ⟨2, fun lane => by fin_cases lane <;> exact ⟨⟨_, rfl, rfl⟩, rfl⟩⟩
  · exact ⟨3, fun lane => by fin_cases lane <;> exact ⟨⟨_, rfl, rfl⟩, rfl⟩⟩

private theorem mem0 {r : Requests} (hr : r ∈ h0) : ∃ i < 4, r = ent 0 0 i (act0 i) := by
  simp only [h0, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [⟨0, by decide, rfl⟩, ⟨1, by decide, rfl⟩, ⟨2, by decide, rfl⟩, ⟨3, by decide, rfl⟩]

private theorem mem1 {r : Requests} (hr : r ∈ h1) : ∃ i < 4, r = ent 1 1 i (act1 i) := by
  simp only [h1, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  exacts [⟨0, by decide, rfl⟩, ⟨1, by decide, rfl⟩, ⟨2, by decide, rfl⟩, ⟨3, by decide, rfl⟩]

private theorem history0 : RequestHistory L X h0 := by
  intro r hr
  obtain ⟨i, hi, rfl⟩ := mem0 hr
  exact ⟨by decide, by interval_cases i <;> rfl, valid0 i hi⟩

private theorem history1 : RequestHistory L X h1 := by
  intro r hr
  obtain ⟨i, hi, rfl⟩ := mem1 hr
  exact ⟨by decide, by interval_cases i <;> rfl, valid1 i hi⟩

private theorem history_ordered : h0.Pairwise fun a b => a.own.Ordered b.own := by
  simp [h0, ent, WarpRequest.Ordered, WarpRequest.Before, request]

private theorem run0 : runRequests {} h0 = .done { previousColumns := some 32, nextLifetime :=
                                                   2 } :=
  by decide
private theorem run1 : runRequests {} h1 = .done { previousColumns := some 32, nextLifetime :=
                                                   2 } :=
  by decide

-- Reusing a request and reversing one warp's program order are excluded by the order of the
-- history (OBJ-TMEM-ORDER); see Tests/Tmem/TmemPairOrder.lean.

-- Duplicating deallocation remains a resource fault, not an impossible trace.
example : runRequests {} [h0[0], h0[1], h0[1]] = .fault .unmatchedRelease := by decide

-- Inventing an empty source trace cannot supply the required requests.
example : ¬ RequestHistory L { X with tr := fun _ => [] } h0 := by
  intro h
  obtain ⟨ev, he⟩ := no_ghost_history L _ h0[0] h0.tail h
  cases he

private def recorded : Execution := { X with
  tmemHistory := fun cta => if cta = 0 then h0 else if cta = 1 then h1 else []
  tmemPairing := pairs }

private theorem pairs_valid {q : WarpRequest × WarpRequest} (hq : q ∈ pairs) :
    ∃ i < 4, q = (request 0 0 i (act0 i), request 1 1 i (act1 i)) := by
  simp only [pairs, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  exacts [⟨0, by decide, rfl⟩, ⟨1, by decide, rfl⟩, ⟨2, by decide, rfl⟩, ⟨3, by decide, rfl⟩]

private theorem pair_ok (i : Nat) (hi : i < 4) :
    PairValid L recorded (request 0 0 i (act0 i), request 1 1 i (act1 i)) := by
  refine ⟨by decide, valid0 i hi, valid1 i hi, ?_, ?_, ?_, ?_⟩ <;> interval_cases i
  all_goals first | decide |
    (unfold SameCtaGroup CtaInCluster Launch.ctaGroupRanks CtaGroup.size; decide)

private theorem mem_left (i : Nat) (hi : i < 4) :
    ent 0 0 i (act0 i) ∈ recorded.tmemHistory (request 0 0 i (act0 i)).cta := by
  interval_cases i <;> simp [recorded, h0, act0, request]

private theorem mem_right (i : Nat) (hi : i < 4) :
    ent 1 1 i (act1 i) ∈ recorded.tmemHistory (request 1 1 i (act1 i)).cta := by
  interval_cases i <;> simp [recorded, h1, act1, request]

/-- Each CTA's history is performed by its own allocator, and each pairing pairs the matching
requests of the two CTAs. -/
theorem recorded_ok : HistoriesOk L recorded := by
  refine ⟨fun cta => ?_, fun q hq => ?_, ?_⟩
  · by_cases h0c : cta = 0
    · subst h0c
      refine ⟨history0, fun r hr => ?_, by change runRequests {} h0 ≠ _; rw [run0]; simp⟩
      obtain ⟨i, -, rfl⟩ := mem0 hr
      rfl
    by_cases h1c : cta = 1
    · subst h1c
      refine ⟨history1, fun r hr => ?_, by change runRequests {} h1 ≠ _; rw [run1]; simp⟩
      obtain ⟨i, -, rfl⟩ := mem1 hr
      rfl
    · simp [RequestHistory, recorded, h0c, h1c, runRequests]
  · obtain ⟨i, hi, rfl⟩ := pairs_valid hq
    exact ⟨pair_ok i hi, ⟨ent 0 0 i (act0 i), mem_left i hi, rfl, rfl⟩,
      ⟨ent 1 1 i (act1 i), mem_right i hi, rfl, rfl⟩⟩
  · decide

-- Both histories replay without a fault.
example (cta : Nat) (reason : Tmem.Error) :
    runRequests {} (recorded.tmemHistory cta) ≠ .fault reason := by
  intro hn
  by_cases h0c : cta = 0
  · subst h0c
    change runRequests {} h0 = _ at hn
    rw [run0] at hn; cases hn
  by_cases h1c : cta = 1
  · subst h1c
    change runRequests {} h1 = _ at hn
    rw [run1] at hn; cases hn
  · simp [recorded, h0c, h1c, runRequests] at hn

private theorem recorded_kind {e : EvId} {pc : Nat} {k : Kind}
    (he : recorded.get e = some ⟨pc, k⟩) : ∃ g d a, k = .tc (.resource g d a) := by
  have hm := List.mem_of_getElem? he
  simp only [recorded, X] at hm
  split_ifs at hm
  · obtain ⟨r, -, hr⟩ := List.mem_map.mp hm
    cases hr
    exact ⟨_, _, _, rfl⟩
  · obtain ⟨r, -, hr⟩ := List.mem_map.mp hm
    cases hr
    exact ⟨_, _, _, rfl⟩
  · cases hm

/-- The two CTAs do not synchronize: causality is program order. -/
private theorem recorded_baseCausality {e f : EvId}
    (hh : baseCausality L recorded e f) : e.1 = f.1 := by
  have notKind {e : EvId} {pc : Nat} {k : Kind} (he : recorded.get e = some ⟨pc, k⟩)
      (hk : ∀ g d a, k ≠ .tc (.resource g d a)) : False := by
    obtain ⟨g, d, a, rfl⟩ := recorded_kind he
    exact hk g d a rfl
  have base : ∀ {e f : EvId}, (po recorded e f ∨ CtaBarSync L recorded e f ∨
      MSync L recorded e f ∨ ClusterSync L recorded e f ∨
      WarpBarSync L recorded e f ∨ synchronizesWith L recorded e f ∨
      FenceSync L recorded e f) → e.1 = f.1 := by
    intro e f h
    refine h.elim (fun h => h.1) (fun h => ?_)
    refine h.elim (fun h => ?_) (fun h => ?_)
    · obtain ⟨_, key, i, j, ⟨-, ⟨count, pc, mode, hg⟩, -⟩, -, -, -, -⟩ := h
      exact (notKind hg (by simp)).elim
    refine h.elim (fun h => ?_) (fun h => ?_)
    · obtain ⟨x, w, m, rs, as_, ⟨tx, count, ⟨pc, hg⟩⟩, -⟩ := h
      exact (notKind hg (by simp)).elim
    refine h.elim (fun h => ?_) (fun h => ?_)
    · obtain ⟨-, i, j, hs, -, -, -⟩ := h
      obtain ⟨phase, harr, -⟩ := hs
      obtain ⟨k, s, t, cta, warp, lanes, g, hnil, -⟩ := harr
      have hempty : recorded.clusters (L.clusterOfCta (e.1 / L.block)) = [] := rfl
      rw [hempty] at hnil
      simp at hnil
    refine h.elim (fun h => ?_) (fun h => ?_)
    · obtain ⟨i, j, ⟨-, mask, inst, ⟨pc, hg⟩, -⟩, -, -, -⟩ := h
      exact (notKind hg (by simp)).elim
    refine h.elim (fun h => ?_) (fun h => ?_)
    · obtain ⟨a, b, bs, cs, hw, -, -⟩ := h
      rcases hw with ⟨pc, hg⟩ | ⟨old, ⟨pc, hg⟩⟩
      · exact (notKind hg (by simp)).elim
      · exact (notKind hg (by simp)).elim
    · have hnofence : ∀ e sem s, ¬ recorded.ThreadFence e sem s := by
        intro e sem s hf
        obtain ⟨pc, hf⟩ := hf
        exact notKind hf (by simp)
      exact absurd h (not_fenceSync_of_noFence hnofence e f)
  unfold PTX.baseCausality at hh
  induction hh with
  | single h => exact base h
  | tail _ h ih => exact ih.trans (base h)

/-- EXT-TMEM-ALLOC-ORDER: CTA 0 allocates again after its `cta_group::2` deallocation, and
nothing orders CTA 1's half of that deallocation before the allocation. Whether the columns are
free at that point depends on when CTA 0's half takes effect, so the execution is unsafe, although
its histories are valid and replay. -/
theorem recorded_pending : HistoriesOk L recorded ∧ ResourceUnsafe L recorded := by
  refine ⟨recorded_ok, 0, .inr ⟨1, 2, h0[1], h0[2], rfl, rfl, by decide, rfl, ⟨0, 64, rfl⟩,
    ⟨32, 0, rfl⟩, ⟨(request 0 0 1 (act0 1), request 1 1 1 (act1 1)),
      by simp [recorded, pairs], .inl rfl⟩, ?_⟩⟩
  rintro ⟨q, hq, p, hqp, lane, lane', hh⟩
  have ht := recorded_baseCausality hh
  obtain ⟨i, -, rfl⟩ := pairs_valid hq
  rcases hqp with ⟨-, rfl⟩ | ⟨h, -⟩
  · simp [WarpRequest.event, request, h0, ent, L] at ht
    omega
  · simp [h0, ent, request] at h

-- The pairing covers actual lane instances of both CTAs' requests.
example (lane : Fin 32) : Covered L recorded ((request 0 0 0 (act0 0)).event L lane) :=
  ⟨_, .inr ⟨(request 0 0 0 (act0 0), request 1 1 0 (act1 0)), by simp [recorded, pairs], rfl⟩,
    _, List.mem_cons_self .., lane, rfl⟩
example (lane : Fin 32) : Covered L recorded ((request 1 1 0 (act1 0)).event L lane) :=
  ⟨_, .inr ⟨(request 0 0 0 (act0 0), request 1 1 0 (act1 0)), by simp [recorded, pairs], rfl⟩,
    _, by simp, lane, rfl⟩

-- A recorded but unpaired cta_group::2 request is not complete.
private def unpaired : Execution := { recorded with tmemPairing := [] }
example (lane : Fin 32) : ¬ Covered L unpaired (h0[0].own.event L lane) := by
  rintro ⟨ws, ⟨cta, r, hr, hg, -⟩ | ⟨q, hq, -⟩, -⟩
  · by_cases h0c : cta = 0
    · subst h0c
      obtain ⟨i, -, rfl⟩ := mem0 (show r ∈ h0 from hr)
      cases hg
    by_cases h1c : cta = 1
    · subst h1c
      obtain ⟨i, -, rfl⟩ := mem1 (show r ∈ h1 from hr)
      cases hg
    · simp [unpaired, recorded, h0c, h1c] at hr
  · cases hq

-- Before the deallocation is paired, the prefix is not reported; an extension that records
-- the pairing is (`recorded_pending`).
example : ¬ PendingReleaseAlloc L unpaired 0 := by
  rintro ⟨-, -, -, -, -, -, -, -, -, -, ⟨q, hq, -⟩, -⟩
  cases hq

-- Already recorded histories and pairings cannot be erased by execution extension.
example : ¬ recorded.le { recorded with tmemHistory := fun _ => [] } := by
  intro h
  have hl := (Execution.le_tmemHistory h 0).length_le
  change 4 ≤ 0 at hl
  omega
example : ¬ recorded.le { recorded with tmemPairing := [] } := by
  intro h
  have hl := (Execution.le_tmemPairing h).length_le
  change 4 ≤ 0 at hl
  omega

-- Copying a CTA's history to another CTA's allocator is rejected.
example : ¬ HistoriesOk L { recorded with tmemHistory := fun _ => h0 } := by
  intro h
  have he := (h.1 1).2.1 h0[0] (by simp [h0])
  change 0 = 1 at he
  omega

-- Pairing an allocation with a deallocation is rejected.
example : ¬ HistoriesOk L { recorded with tmemPairing := [(h0[0].own, h1[1].own)] } := by
  intro h
  have hc := ((h.2.1 _ (List.mem_singleton_self _)).1).2.2.2.2.2.2
  simp [h0, h1, ent, request, compatible, Tmem.Action.request] at hc

private def beforeLast : Execution := { recorded with tmemPairing := pairs.take 3 }

-- Pairing the last operation advances the actual execution measure, with exactly the same
-- thread traces and histories.
example : beforeLast.size L < recorded.size L :=
  Execution.recordPairing_size beforeLast L (request 0 0 3 (act0 3), request 1 1 3 (act1 3))

-- The actual request history obeys a bound on counted instructions, not poll count.
example : h0.length ≤ L.threads * 4 := by
  apply RequestHistory.length_le history0 history_ordered 4
  intro g hg
  change ((if g < 32 then h0.map (event ·.own)
    else if 96 ≤ g ∧ g < 128 then h1.map (event ·.own) else [])).countP Event.counts ≤ 4
  split_ifs <;> decide

-- A blocking deallocation return depends on the peer warp's actual request.
private def waiting : Execution := { recorded with tmemPairBlocks := fun _ => true }
example : WaitEdge L waiting ((request 1 1 1 (act1 1)).event L 0)
    ((request 0 0 1 (act0 1)).event L 0) :=
  ⟨_, .inr ⟨(request 0 0 1 (act0 1), request 1 1 1 (act1 1)), by simp [waiting, recorded, pairs],
    rfl⟩, ⟨_, by simp, 0, rfl⟩, ⟨_, List.mem_cons_self .., 0, rfl⟩,
    ⟨11, .two, none, .dealloc 0 64, rfl, .inr rfl⟩⟩

-- With the early-return choice, the same completed operation creates no peer-wait edge.
example : ¬ WaitEdge L recorded ((request 1 1 1 (act1 1)).event L 0)
    ((request 0 0 1 (act0 1)).event L 0) := by
  rintro ⟨ws, -, -, -, pc, group, dst, action, he, hw⟩
  change (some ⟨11, .tc (.resource .two none (.dealloc 0 64))⟩ : Option Event) =
    some ⟨pc, .tc (.resource group dst action)⟩ at he
  cases he
  rcases hw with hw | hw <;> cases hw

-- Both CTAs' whole allocations were explicitly released, even after address reuse.
example : Released recorded := by
  intro cta st hs
  by_cases h0c : cta = 0
  · subst h0c
    cases (Tmem.Outcome.done.inj (run0.symm.trans hs))
    rfl
  by_cases h1c : cta = 1
  · subst h1c
    cases (Tmem.Outcome.done.inj (run1.symm.trans hs))
    rfl
  · have he : recorded.tmemHistory cta = [] := by simp [recorded, h0c, h1c]
    rw [he] at hs
    cases hs
    rfl

private def liveOnly : Execution := { X with
  tmemHistory := fun cta => if cta = 0 then [h0[0]] else if cta = 1 then [h1[0]] else []
  tmemPairing := [(h0[0].own, h1[0].own)] }

example : ¬ Released liveOnly := by
  intro h
  have hf : runRequests {} (liveOnly.tmemHistory 1) =
      .done { previousColumns := some 64, nextLifetime := 1, live := [⟨0, 128, 64⟩] } := by
    decide
  cases h 1 _ hf

-- Holding allocations during execution is not itself a release violation.
example : ¬ ReleaseUnsafe L liveOnly := by
  rintro ⟨hexit, _, _⟩
  rcases hexit 0 (by decide) with hc | ⟨pc, he⟩
  · have ht := hc.1
    cases ht
  · cases he

private def permitOnly : Execution := { X with
  tmemHistory := fun cta => if cta = 0 then [h0[0], ent 0 0 1 .relinquish] else [] }

-- Relinquishing allocation permission leaves the allocation live.
example : ¬ Released permitOnly := by
  intro h
  have hf : runRequests {} (permitOnly.tmemHistory 0) = .done {
      permit := false, previousColumns := some 64, nextLifetime := 1, live := [⟨0, 0, 64⟩] } := by
    decide
  cases h 0 _ hf

/-! Allocation management by different warps of one CTA (§9.7.18.5 Table 55: "Issue from a single
warp in the current CTA would initiate the allocation management instruction."): warp 0 allocates
and frees, then warp 1 allocates and frees the same columns. The history is valid and replays. -/
private def L1 : Launch := { grid := 1, block := 64, params := fun _ => none }
private def own (warp index : Nat) (a : Tmem.Action) : Requests :=
  ⟨⟨0, warp, fun _ => index, 2 * warp + index,
    match a with | .alloc .. => some ⟨.shared, 0, 0⟩ | _ => none, a.request⟩, .one, a⟩
private def handoff : List Requests := [own 0 0 (.alloc 32 0), own 0 1 (.dealloc 0 32),
  own 1 0 (.alloc 32 0), own 1 1 (.dealloc 0 32)]
private def oneEvent (r : Requests) : Event := ⟨r.own.pc, .tc (.resource .one r.own.dst
    r.own.request)⟩
private def Y : Execution := {
  tr := fun g => if g < 32 then [oneEvent (own 0 0 (.alloc 32 0)),
    oneEvent (own 0 1 (.dealloc 0 32))]
    else if g < 64 then [oneEvent (own 1 0 (.alloc 32 0)), oneEvent (own 1 1 (.dealloc 0 32))]
    else [],
  rf := fun _ _ => none }

private theorem handoff_history : RequestHistory L1 Y handoff := by
  intro r hr
  simp only [handoff, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  all_goals refine ⟨by decide, rfl, by decide, by decide,
    fun lane => by fin_cases lane <;> rfl, ?_⟩
  · exact ⟨0, fun lane => by fin_cases lane <;> exact ⟨⟨_, rfl, rfl⟩, by decide⟩⟩
  · exact ⟨1, fun lane => by fin_cases lane <;> exact ⟨⟨_, rfl, rfl⟩, by decide⟩⟩
  · exact ⟨0, fun lane => by fin_cases lane <;> exact ⟨⟨_, rfl, rfl⟩, by decide⟩⟩
  · exact ⟨1, fun lane => by fin_cases lane <;> exact ⟨⟨_, rfl, rfl⟩, by decide⟩⟩

example : runRequests {} handoff = .done { previousColumns := some 32, nextLifetime := 2 } := by
  decide

example : HistoriesOk L1 { Y with tmemHistory := fun cta => if cta = 0 then handoff else [] } := by
  refine ⟨fun cta => ?_, (fun q hq => by cases hq), List.Pairwise.nil⟩
  by_cases hk : cta = 0
  · subst cta
    refine ⟨handoff_history, ?_, ?_⟩
    · intro r hr
      change r ∈ handoff at hr
      simp only [handoff, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> rfl
    · change runRequests {} handoff ≠ .blocked
      decide
  · simp [RequestHistory, hk, runRequests]

-- A cta_group::1 deallocation is performed when it returns: warp 1 reallocating the columns
-- warp 0 released, without synchronization, is not reported (EXT-TMEM-ALLOC-ORDER).
example : ¬ ResourceUnsafe L1 { Y with tmemHistory := fun cta => if cta = 0 then handoff else
                                       [] } := by
  rintro ⟨cta, ⟨reason, hf⟩ | ⟨k, l, d, a, hd, -, -, hg, -⟩⟩
  · by_cases hk : cta = 0
    · subst hk
      change runRequests {} handoff = _ at hf
      rw [show runRequests {} handoff = .done { previousColumns := some 32, nextLifetime := 2 }
        by decide] at hf
      cases hf
    · simp [hk, runRequests] at hf
  · have hd' := List.mem_of_getElem? hd
    by_cases hk : cta = 0
    · subst hk
      change d ∈ handoff at hd'
      simp only [handoff, List.mem_cons, List.not_mem_nil, or_false] at hd'
      rcases hd' with rfl | rfl | rfl | rfl <;> cases hg
    · simp [hk] at hd'

-- The requests are not one warp's program order, which the history does not require.
example : ¬ handoff.Pairwise fun a b => a.own.Before b.own := by
  intro h
  have hb := (List.pairwise_cons.mp h).1 (own 1 0 (.alloc 32 0)) (by simp)
  have := hb.2.1
  simp [own] at this

/-! The `cta_group::2` reallocation of `recorded` with the peer half ordered before the
allocation (EXT-TMEM-ALLOC-ORDER): after its deallocation, CTA 1's warp 1 stores a flag with
`.release` at cluster scope, and CTA 0's warp 0 reads it with `.acquire` before allocating
again. -/
private def flag : Acc := { loc := ⟨.global, 0, 0⟩, size := 4, scope := .cluster }
private def s00 : Requests := ent 0 0 0 (.alloc 64 0)
private def s01 : Requests := ent 0 0 1 (.dealloc 0 64)
private def s03 : Requests := ent 0 0 3 (.alloc 64 0)
private def s10 : Requests := ent 1 1 0 (.alloc 64 128)
private def s11 : Requests := ent 1 1 1 (.dealloc 128 64)
private def ordered : Execution := {
  tr := fun g => if g < 32 then [event s00.own, event s01.own,
      ⟨20, .rd { flag with acquire := true } []⟩, event s03.own]
    else if 96 ≤ g ∧ g < 128 then [event s10.own, event s11.own,
      ⟨21, .wr { flag with release := true } []⟩] else [],
  rf := fun r _ => if r = .thread (0, 2) then some (.thread (96, 2)) else none
  tmemHistory := fun cta => if cta = 0 then [s00, s01, s03] else if cta = 1 then [s10, s11] else []
  tmemPairing := [(s00.own, s10.own), (s01.own, s11.own)] }

/-- CTA 1's half of the deallocation causally precedes CTA 0's allocation. -/
private theorem ordered_peer : PeerBefore L ordered s01.own s03.own := by
  refine ⟨(s01.own, s11.own), by simp [ordered], s11.own, .inl ⟨rfl, rfl⟩, 0, 0, ?_⟩
  have h1 : po ordered (96, 1) (96, 2) := by unfold po; decide
  have h2 : synchronizesWith L ordered (96, 2) (0, 2) :=
    ⟨_, _, _, _, Or.inl ⟨21, rfl⟩, Or.inl ⟨20, rfl⟩, rfl, rfl, rfl, rfl, by decide,
      show SameCluster L 96 0 from ⟨by decide, by decide, by decide⟩,
      show SameCluster L 0 96 from ⟨by decide, by decide, by decide⟩, fun k _ => by simp [ordered]⟩
  have h3 : po ordered (0, 2) (0, 3) := by unfold po; decide
  have hstep : po ordered (96, 2) (0, 2) ∨ CtaBarSync L ordered (96, 2) (0, 2) ∨
      MSync L ordered (96, 2) (0, 2) ∨ ClusterSync L ordered (96, 2) (0, 2) ∨
      WarpBarSync L ordered (96, 2) (0, 2) ∨ synchronizesWith L ordered (96, 2) (0, 2) ∨
      FenceSync L ordered (96, 2) (0, 2) := .inr (.inr (.inr (.inr (.inr (.inl h2)))))
  have h12 : Relation.TransGen (fun e f => po ordered e f ∨ CtaBarSync L ordered e f ∨
      MSync L ordered e f ∨ ClusterSync L ordered e f ∨ WarpBarSync L ordered e f ∨
      synchronizesWith L ordered e f ∨ FenceSync L ordered e f) (96, 1) (0, 2) :=
    (Relation.TransGen.single (.inl h1)).tail hstep
  exact h12.tail (.inl h3)

/-- With the peer half ordered before it, the reallocation is not reported. -/
theorem ordered_safe : ¬ ResourceUnsafe L ordered := by
  rintro ⟨cta, ⟨reason, hf⟩ | ⟨k, l, d, a, hd, ha, hkl, -, ⟨b, n, hdd⟩, ⟨n', b', haa⟩, -, hnp⟩⟩
  · by_cases h0c : cta = 0
    · subst h0c
      change runRequests {} [s00, s01, s03] = _ at hf
      rw [show runRequests {} [s00, s01, s03] =
        .done { previousColumns := some 64, nextLifetime := 2, live := [⟨1, 0, 64⟩] }
        by decide] at hf
      cases hf
    by_cases h1c : cta = 1
    · subst h1c
      change runRequests {} [s10, s11] = _ at hf
      rw [show runRequests {} [s10, s11] = .done { previousColumns := some 64, nextLifetime := 1 }
        by decide] at hf
      cases hf
    · simp [ordered, h0c, h1c, runRequests] at hf
  · by_cases h0c : cta = 0
    · subst h0c
      change [s00, s01, s03][k]? = some d at hd
      change [s00, s01, s03][l]? = some a at ha
      have hl : l < 3 := by simpa using (List.getElem?_eq_some_iff.mp ha).1
      interval_cases l <;> interval_cases k <;> simp at hd ha <;> subst hd ha
      all_goals first
        | simp [s00, ent] at hdd
        | exact hnp ordered_peer
    by_cases h1c : cta = 1
    · subst h1c
      change [s10, s11][k]? = some d at hd
      change [s10, s11][l]? = some a at ha
      have hl : l < 2 := by simpa using (List.getElem?_eq_some_iff.mp ha).1
      interval_cases l
      · omega
      · obtain rfl : k = 0 := by omega
        cases hd
        simp [s10, ent] at hdd
    · simp [ordered, h0c, h1c] at hd

end
end PTX.Tests.TmemPairHistory
