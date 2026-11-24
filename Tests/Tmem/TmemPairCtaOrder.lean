-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Tmem.TmemPairOrder
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Lemmas.Order.WaitOrderObject

namespace PTX.Tests.TmemPairCtaOrder
open Tmem.Pair
noncomputable section

/-! Litmus test for the per-CTA allocator orders of OBJ-TMEM-ORDER (EXT-TMEM-ALLOC-ORDER)
and the separate pairing of cta_group::2 operations (OBJ-TMEM-ORIGIN).

§9.7.18.7.1: "When .cta_group::2 is specified, one warp from each of the peer CTAs must
collectively perform the allocation and de-allocation." and "The number of columns allocated
must not increase between any two allocations in the execution order within the CTA."

A cluster of two CTAs with two warps each. Warp 0 of both CTAs makes operation `A` (a
cta_group::2 allocation of 32 columns); warp 1 of both CTAs makes operation `B` (another one).
Nothing orders the two warps of a CTA. CTA 0's allocator performs `A` then `B`; CTA 1's
allocator performs `B` then `A`. Each CTA's history is valid and replays without fault, at its
own columns; both operations are complete (paired); and the allocator orders are coherent with
causality (`crossed_coherent`). A single history common to the two CTAs could not record both
orders. -/

private def L : Launch := { grid := 2, block := 64, clusterSize := 2, params := fun _ => none }

/-- The request of warp `w` of CTA `c`. -/
private def req (c w : Nat) : WarpRequest :=
  ⟨c, w, fun _ => 0, w, some ⟨.shared, c, 4 * w⟩, .alloc 32⟩

private def ev (c w : Nat) : Event := ⟨w, .tc (.resource .two (some ⟨.shared, c,
    4 * w⟩) (.alloc 32))⟩

/-- The record of CTA `c`'s allocator performing warp `w`'s request at `col`. -/
private def rec (c w col : Nat) : Requests := ⟨req c w, .two, .alloc 32 col⟩

/-- The position of the record of warp `w` of CTA `c` in its CTA's history. -/
private def idx (g : Nat) : Nat := if g < 32 then 0 else if g < 64 then 1 else if g < 96 then 1 else
    0

private def crossed : Execution := {
  tr := fun g => if g < 128 then [ev (g / 64) (g % 64 / 32)] else []
  rf := fun _ _ => none
  tmemHistory := fun c => if c = 0 then [rec 0 0 0, rec 0 1 32]
    else if c = 1 then [rec 1 1 0, rec 1 0 32] else []
  tmemPairing := [(req 0 0, req 1 0), (req 0 1, req 1 1)] }

private theorem get_req (c w : Nat) (hc : c < 2) (hw : w < 2) (lane : Fin 32) :
    crossed.get ((req c w).event L lane) = some ⟨(req c w).pc, .tc (.resource .two (req c w).dst
      (req c w).request)⟩ := by
  have hl := lane.isLt
  have hg : c * 64 + w * 32 + lane.val < 128 := by omega
  have h1 : (c * 64 + w * 32 + lane.val) / 64 = c := by omega
  have h2 : (c * 64 + w * 32 + lane.val) % 64 / 32 = w := by omega
  simp [Execution.get, crossed, WarpRequest.event, req, L, hg, h1, h2, ev]

private theorem valid_req (c w : Nat) (hc : c < 2) (hw : w < 2) : (req c w).Valid L crossed .two :=
  ⟨by simpa [req, L] using hc, by simp [req, L]; omega, get_req c w hc hw, 0,
    fun lane => ⟨⟨_, get_req c w hc hw lane, rfl⟩, by simp [WarpRequest.event, req]⟩⟩

/-- Both CTAs' histories are valid records of their own warps, and both operations are paired. -/
theorem crossed_ok : HistoriesOk L crossed := by
  refine ⟨fun c => ?_, fun q hq => ?_, by decide⟩
  · by_cases h0 : c = 0
    · subst h0
      refine ⟨fun r hr => ?_, fun r hr => ?_, by decide⟩
      all_goals simp only [crossed, ite_true, List.mem_cons, List.not_mem_nil, or_false] at hr
      all_goals rcases hr with rfl | rfl
      all_goals first | rfl | exact ⟨by decide, rfl, valid_req _ _ (by decide) (by decide)⟩
    by_cases h1 : c = 1
    · subst h1
      refine ⟨fun r hr => ?_, fun r hr => ?_, by decide⟩
      all_goals change r ∈ [rec 1 1 0, rec 1 0 32] at hr
      all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      all_goals rcases hr with rfl | rfl
      all_goals first | rfl | exact ⟨by decide, rfl, valid_req _ _ (by decide) (by decide)⟩
    · simp [RequestHistory, crossed, h0, h1, runRequests]
  · simp only [crossed, List.mem_cons, List.not_mem_nil, or_false] at hq
    have hp : ∀ w, w < 2 → PairValid L crossed (req 0 w, req 1 w) := fun w hw =>
      ⟨by decide, valid_req _ _ (by decide) hw, valid_req _ _ (by decide) hw,
        by simp [SameCtaGroup, CtaInCluster, Launch.ctaGroupRanks, CtaGroup.size, req, L,
           Launch.clusterOfCta, Launch.rankOfCta, Launch.locate, ClusterPlace.uniform,
           Dim3.prod],
        by simp [req],
        by simp [req, L, Launch.rankOfCta, Launch.locate, ClusterPlace.uniform,
           Dim3.prod], rfl⟩
    rcases hq with rfl | rfl
    · exact ⟨hp 0 (by decide), ⟨rec 0 0 0, by simp [crossed, req], rfl, rfl⟩,
        ⟨rec 1 0 32, by simp [crossed, req], rfl, rfl⟩⟩
    · exact ⟨hp 1 (by decide), ⟨rec 0 1 32, by simp [crossed, req], rfl, rfl⟩,
        ⟨rec 1 1 0, by simp [crossed, req], rfl, rfl⟩⟩

-- CTA 0's allocator performs `A` at column 0 and `B` at column 32; CTA 1's performs `B` at
-- column 0 and `A` at column 32.
example : runRequests {} (crossed.tmemHistory 0) =
    .done { previousColumns := some 32, nextLifetime := 2, live := [⟨0, 0, 32⟩, ⟨1, 32, 32⟩] } := by
  decide
example : runRequests {} (crossed.tmemHistory 1) =
    .done { previousColumns := some 32, nextLifetime := 2, live := [⟨0, 0, 32⟩, ⟨1, 32, 32⟩] } := by
  decide

-- Both operations are complete in both CTAs.
example (c w : Nat) (hc : c < 2) (hw : w < 2) (lane : Fin 32) :
    Covered L crossed ((req c w).event L lane) := by
  refine ⟨[req 0 w, req 1 w], .inr ⟨(req 0 w, req 1 w), ?_, rfl⟩, req c w, ?_, lane, rfl⟩
  · interval_cases w <;> simp [crossed]
  · interval_cases c <;> simp

-- The two allocators order `A` and `B` oppositely.
example : Precedes L crossed 0 ((req 0 0).event L 0) ((req 0 1).event L 0) :=
  ⟨0, 1, rec 0 0 0, rec 0 1 32, rfl, rfl, by decide, ⟨0, rfl⟩, ⟨0, rfl⟩⟩
example : Precedes L crossed 1 ((req 1 1).event L 0) ((req 1 0).event L 0) :=
  ⟨0, 1, rec 1 1 0, rec 1 0 32, rfl, rfl, by decide, ⟨0, rfl⟩, ⟨0, rfl⟩⟩

/-! ### Coherence: nothing orders the two warps of a CTA -/

private theorem crossed_kind {e : EvId} {pc : Nat} {k : Kind}
    (he : crossed.get e = some ⟨pc, k⟩) : ∃ g d a, k = .tc (.resource g d a) := by
  obtain ⟨g, i⟩ := e
  simp only [Execution.get, crossed] at he
  split_ifs at he
  · rcases i with _ | i <;> simp [ev] at he
    exact ⟨_, _, _, he.2.symm⟩
  · simp at he

private theorem crossed_async (i : EvId) (p : AsyncCopy.Part) : ¬ crossed.AsyncPresent i p := by
  cases p <;> simp [Execution.AsyncPresent, Execution.MmaRead, crossed]

private theorem crossed_len {g : Nat} {i : Nat} {e : Event} (he : crossed.get (g, i) = some e) :
    i = 0 := by
  have := len_of_get he
  simp only [crossed] at this
  split_ifs at this <;> simp at this
  omega

private theorem crossed_noWrite {e : EvId} {a : Acc} {bs : List Byte} :
    ¬ crossed.Writes e a bs := by
  rintro ⟨pc, h⟩
  obtain ⟨g, d, r, hk⟩ := crossed_kind h
  cases hk

private theorem crossed_noRmw {e : EvId} {a : Acc} {o : List (Option Byte)}
    {n : Option (List Byte)} : ¬ crossed.Rmw e a o n := by
  rintro ⟨pc, h⟩
  obtain ⟨g, d, r, hk⟩ := crossed_kind h
  cases hk

/-- The one event of a thread writes nothing: it is a Tensor Memory allocation. -/
private theorem crossed_noMemWrites {e : EvId} {a : Acc} {bs : List Byte} :
    ¬ crossed.MemWrites (.thread e) a bs := by
  rintro (h | ⟨o, h⟩)
  · exact crossed_noWrite h
  · exact crossed_noRmw h

/-- Program order relates no two events of these one-event threads. -/
private theorem crossed_noPo {e f : EvId} : ¬ po crossed e f := by
  rintro ⟨-, h1, h2, -⟩
  have hl : f.2 = 0 :=
    crossed_len (g := f.1) (i := f.2) (e := (crossed.tr f.1)[f.2]) (by
      simp [Execution.get, List.getElem?_eq_getElem h2])
  omega

/-- Every stage edge needs a present asynchronous stage, and this execution has none. -/
private theorem crossed_noStageEdge {e f : AsyncCopy.Ref} : ¬ StageEdge crossed e f := by
  intro h
  unfold StageEdge at h
  repeat' split at h
  all_goals simp_all [crossed_async]

/-- Causality is program order, which relates no two events of these one-event threads. -/
private theorem crossed_baseCausality {e f : EvId} (hh : baseCausality L crossed e f) : False := by
  have notKind {e : EvId} {pc : Nat} {k : Kind} (he : crossed.get e = some ⟨pc, k⟩)
      (hk : ∀ g d a, k ≠ .tc (.resource g d a)) : False := by
    obtain ⟨g, d, a, rfl⟩ := crossed_kind he
    exact hk g d a rfl
  have base : ∀ {e f : EvId}, (po crossed e f ∨ CtaBarSync L crossed e f ∨
      MSync L crossed e f ∨ ClusterSync L crossed e f ∨
      WarpBarSync L crossed e f ∨ synchronizesWith L crossed e f ∨ FenceSync L crossed e f) →
      False := by
    intro e f h
    rcases h with ⟨h1, h2, h3, -⟩ | ⟨_, _, _, _, _, ⟨_, ⟨_, _, hb⟩, _⟩, _⟩ |
        ⟨_, _, _, _, _, _, ⟨⟨_, _, hw⟩, _⟩, _⟩ | ⟨_, _, _, ⟨_, ⟨k, _, _, _, _, _, _, hk, _⟩, _⟩,
          _⟩ |
        ⟨_, _, ⟨_, _, _, ⟨_, hb⟩, _⟩, _⟩ | ⟨_, _, _, _, hw, -⟩ |
        ⟨_, _, _, _, _, _, _, _, hw, -⟩ | ⟨-, hsc⟩
    · obtain ⟨g, i⟩ := e
      obtain ⟨g', j⟩ := f
      simp only at h1 h2 h3
      subst h1
      simp only [crossed] at h3
      split_ifs at h3 <;> simp at h3
      omega
    · exact notKind hb (by simp)
    · exact notKind hw (by simp)
    · simp [crossed] at hk
    · exact notKind hb (by simp)
    · exact crossed_noMemWrites hw
    · exact crossed_noMemWrites hw
    · simp [crossed] at hsc
  unfold PTX.baseCausality at hh
  induction hh with
  | single h => exact base h
  | tail _ h _ => exact base h

/-- The position of a node: its record's position in its CTA's history, then issue before
return. -/
private def pos : AsyncCopy.Ref × Bool → Nat
  | (.thread e, b) => 2 * idx e.1 + b.toNat
  | (.async _ _, _) => 0

/-- The only causal edges are from an event's issue to its return. -/
private theorem crossed_cause {a c : AsyncCopy.Ref × Bool} (hc : stageCausality L crossed a c) :
    pos a < pos c := by
  obtain ⟨e, b⟩ := a
  obtain ⟨f, b'⟩ := c
  rcases hc with (⟨rfl, rfl, rfl, hp⟩ | ⟨-, -, he⟩) | ⟨-, -, i, j, rfl, rfl, hc⟩ |
      ⟨-, -, j, rfl, hc⟩
  · cases e with
    | thread e => simp [pos]
    | async i p => exact (crossed_async i p hp).elim
  · exact (crossed_noStageEdge he).elim
  · exact (crossed_baseCausality hc).elim
  · obtain ⟨i, p, w, ws, -, -, -, -, ho⟩ := hc
    exact (crossed_noPo (e := w) (f := j) ho).elim

/-- **The crossed orders are coherent with causality**: each CTA's history orders requests that
causality does not order. -/
theorem crossed_coherent : ObjectCoherent L crossed := fun o =>
  acyclic_of_rank pos fun a c h => by
    rcases h with h | h
    · exact crossed_cause h
    · obtain ⟨e, b⟩ := a
      obtain ⟨f, b'⟩ := c
      cases o with
      | mbar m =>
        obtain ⟨h, -⟩ := h
        obtain ⟨-, -, ha⟩ := h
        simp [crossed, MBarrier.Before] at ha
      | ctaBar c id =>
        obtain ⟨-, -, -, -, -, -, -, -, k, -, r, -, hr, -⟩ := h
        simp [crossed] at hr
      | cluster c =>
        obtain ⟨-, -, -, -, -, -, k, -, r, -, hr, -⟩ := h
        simp [crossed] at hr
      | tmem c =>
        obtain ⟨rfl, rfl, i, j, rfl, rfl, k, l, x, y, hx, hy, hkl, ⟨li, rfl⟩, ⟨lj, rfl⟩⟩ := h
        have hpos : ∀ n r (lane : Fin 32), (crossed.tmemHistory c)[n]? = some r →
            pos (.thread (r.own.event L lane), true) = 2 * n + 1 := by
          intro n r lane hn
          have hl := lane.isLt
          by_cases h0 : c = 0
          · subst h0
            change [rec 0 0 0, rec 0 1 32][n]? = some r at hn
            have hlt := (List.getElem?_eq_some_iff.mp hn).1
            simp only [List.length_cons, List.length_nil] at hlt
            interval_cases n <;> simp at hn <;> subst hn
            · simp [pos, idx, WarpRequest.event, rec, req, L]
            · simp [pos, idx, WarpRequest.event, rec, req, L]
              omega
          by_cases h1 : c = 1
          · subst h1
            change [rec 1 1 0, rec 1 0 32][n]? = some r at hn
            have hlt := (List.getElem?_eq_some_iff.mp hn).1
            simp only [List.length_cons, List.length_nil] at hlt
            interval_cases n <;> simp at hn <;> subst hn
            · simp [pos, idx, WarpRequest.event, rec, req, L]
              omega
            · simp [pos, idx, WarpRequest.event, rec, req, L]
              split_ifs <;> omega
          · simp [crossed, h0, h1] at hn
        rw [hpos k x li hx, hpos l y lj hy]
        omega

end
end PTX.Tests.TmemPairCtaOrder
