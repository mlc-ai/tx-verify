-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Assembly.Correctness
public import Core.Source.Decode

/-! `bar.arrive` (§9.7.15.1, §8.9.4): decoding, its event, its participation in a named barrier
generation together with `bar.sync`, the synchronizes-with edge it gives (a write before the
`bar.arrive` is ordered before a read after the matching `bar.sync`), the order it does not give
(events after a `bar.arrive`), and its faults (zero count, count mismatch, a second arrival of a
warp in one generation, a warp mixing the two forms). -/
namespace PTX.Tests.CtaBarrierArrive
open PTX.Syntax
noncomputable section

/-! ## Decoding -/

private def env : Decode.Env := { classes := [⟨"%r".toList, 2, 32⟩], labels := [], params := [] }

-- `bar.arrive a, b` is `barrier.arrive.aligned a, b` (§9.7.15.1); a register barrier works.
example : Decode.op env "bar.arrive" [.register "%r0", .literal "64"] =
    .ok (.barArrive (.reg 0) (.imm 64) true) := rfl
example : Decode.op env "barrier.arrive.aligned" [.literal "2", .literal "416"] =
    .ok (.barArrive (.imm 2) (.imm 416) true) := rfl
example : Decode.op env "barrier.arrive" [.literal "2", .literal "416"] =
    .ok (.barArrive (.imm 2) (.imm 416) false) := rfl
-- The thread count is mandatory for `bar.arrive`.
example : (Decode.op env "bar.arrive" [.literal "2"]).isOk = false := rfl
-- `bar.sync` with a register barrier keeps its form.
example : Decode.op env "bar.sync" [.register "%r1", .literal "64"] =
    .ok (.barSyncN (.reg 1) (.imm 64) true) := rfl

/-! ## The event -/

private def launch : Launch := { grid := 1, block := 128, params := fun _ => none }

-- An arrive event retains its id, count and form.
example : barTmpl launch 0 {} (.imm 1) (some (.imm 64)) .arrive =
    .bar 1 { pc := 1 } (some 64) .arrive := rfl
-- A whole-CTA count is the omitted-count form, as for `bar.sync`.
example : barTmpl launch 0 {} (.imm 1) (some (.imm 128)) .arrive =
    .bar 1 { pc := 1 } none .arrive := rfl
example : eventTmpl [] launch 0 {} (.barArrive (.imm 2) (.imm 32) true) =
    .bar 2 { pc := 1 } (some 32) .arrive := rfl
-- "a non-zero thread count is required for barrier{.cta}.arrive": zero is a fault, while zero on
-- `bar.sync` is the whole-CTA form (EXT-BAR-ZERO-COUNT).
example : barTmpl launch 0 {} (.imm 1) (some (.imm 0)) .arrive = .ub .badBarrier := rfl
example : barTmpl launch 0 {} (.imm 1) (some (.imm 0)) .sync = .bar 1 { pc := 1 } := rfl
-- A count that is not a multiple of the warp size, or an id of 16, is a fault for either form.
example : barTmpl launch 0 {} (.imm 1) (some (.imm 48)) .arrive = .ub .badBarrier := rfl
example : barTmpl launch 0 {} (.imm 16) (some (.imm 64)) .arrive = .ub .badBarrier := rfl

/-! ## One generation completed by a `bar.arrive` warp and a `bar.sync` warp

In a CTA of four warps, warp 0 writes `x`, arrives at barrier 1 with `bar.arrive 1, 64` and
writes `y`; warp 1 executes `bar.sync 1, 64` and then reads `x`. -/

private def x : Acc := { loc := ⟨.global, 0, 0⟩, size := 1 }
private def y : Acc := { loc := ⟨.global, 0, 8⟩, size := 1 }

private def lanes (w i : Nat) : List (Nat × EvId) :=
  (List.range 32).map fun lane => let g := w * 32 + lane; (g, (g, i))

private def history : List (CtaBarrier.Record EvId) :=
  [.arrival 1 0 (some 64) (lanes 0 1), .arrival 1 1 (some 64) (lanes 1 0)]

private def execution : Execution := {
  tr := fun g =>
    if g < 32 then
      [⟨0, .wr x [(.bits 8 7, 0)]⟩, ⟨1, .bar 1 (some 64) .arrive⟩, ⟨2, .wr y [(.bits 8 1, 0)]⟩]
    else if g < 64 then [⟨3, .bar 1 (some 64) .sync⟩, ⟨4, .rd x [some (.bits 8 7, 0)]⟩]
    else []
  rf := fun _ _ => none
  barriers := fun c => if c = 0 then history else []
}

-- The `bar.arrive` of thread 0 is an arrival in generation 0 of barrier 1 (key `1 + 16 * 0`).
theorem arrive_key : CtaBarArrivalK launch execution (0, 1) 1 :=
  ⟨by decide, ⟨some 64, 1, .arrive, rfl⟩, 0, _, 0, some 64, lanes 0 1, 0, rfl, rfl, by decide,
    rfl, _, rfl⟩

-- It is not a `bar.sync` arrival: it has no `CtaBarK` key.
theorem arrive_not_sync (key : Nat) : ¬ CtaBarK launch execution (0, 1) key := by
  rintro ⟨-, ⟨count, pc, h⟩, -⟩
  simp [Execution.IsBarrier, Execution.get, execution] at h

theorem sync_key : CtaBarK launch execution (32, 0) 1 :=
  ⟨by decide, ⟨some 64, 3, rfl⟩, 1, _, 1, some 64, lanes 1 0, 32, rfl, rfl, by decide, rfl, _,
    rfl⟩

-- The two warps complete generation 0: the `bar.sync` may pass.
theorem generation_done : CtaBarDone launch execution 0 1 :=
  ⟨1, _, _, _, rfl, rfl, rfl, rfl, rfl⟩

-- §8.9.4: "A bar{.cta}.sync or bar{.cta}.red or bar{.cta}.arrive operation synchronizes with a
-- bar{.cta}.sync or bar{.cta}.red operation executed on the same barrier." The write before the
-- `bar.arrive` happens before the read after the `bar.sync`.
theorem write_baseCausality_read : baseCausality launch execution (0, 0) (32, 1) :=
  .single (.inr (.inl ⟨⟨by decide, by decide, by decide⟩, 1, 1, 0, arrive_key, sync_key,
    by decide, by decide, by decide⟩))

-- No barrier edge orders anything into an event after a `bar.arrive`: the target of `CtaBarSync`
-- follows a `bar.sync` arrival of its own thread, and thread 0 has none.
theorem no_sync_into_arriver (e : EvId) (k : Nat) : ¬ CtaBarSync launch execution e (0, k) := by
  rintro ⟨-, key, i, j, -, ⟨-, ⟨count, pc, h⟩, -⟩, -, hj, -⟩
  simp only [Execution.IsBarrier, Execution.get, execution] at h
  obtain _ | _ | _ | j := j <;> simp at h

/-! ## `bar.arrive` does not wait for the other warps

Warp 0 passes its `bar.arrive` (it writes `y` afterwards) while warp 1 has not arrived: the
generation is open and the execution is still blocking-consistent. Passing the `bar.arrive`
needs its warp's arrival recorded in the history (performed when it executes), not the
generation completed. -/

private def early : Execution := {
  tr := fun g =>
    if g < 32 then
      [⟨0, .wr x [(.bits 8 7, 0)]⟩, ⟨1, .bar 1 (some 64) .arrive⟩, ⟨2, .wr y [(.bits 8 1, 0)]⟩]
    else []
  rf := fun _ _ => none
  barriers := fun c => if c = 0 then [.arrival 1 0 (some 64) (lanes 0 1)] else []
}

theorem early_open : ¬ CtaBarDone launch early 0 1 := by
  rintro ⟨i, r, s, t, hr, hs, hp, hg, hg'⟩
  obtain _ | i := i
  · simp only [early, ite_true] at hr
    cases hr
    cases hs
    cases hp
    revert hg'
    decide
  · simp [early] at hr

/-- The early execution has a checked barrier history, and its `bar.arrive` events do not block:
each is recorded in its CTA's history, and its needs (DEP-ORDER) are only those of its warp,
without the release of its generation. -/
theorem early_blocking : CtaBarHistoryOk launch early ∧
    ∀ e id count pc, early.get e = some ⟨pc, .bar id count .arrive⟩ →
      ctaBarNeeds launch early e .arrive = ctaBarWarpNeeds launch early e ∧
        e ∈ (early.barriers (e.1 / launch.block)).flatMap CtaBarrier.Record.refs := by
  refine ⟨⟨fun c hc => ?_, fun c hc => ?_⟩, ?_⟩
  · have : 1 ≤ c := hc
    simp [early]; omega
  · obtain rfl : c = 0 := by
      have : c < 1 := hc
      omega
    refine ⟨by decide, ?_, _, rfl⟩
    intro r hr
    simp only [early, ite_true, List.mem_singleton] at hr
    subst hr
    intro p hp
    simp only [lanes, List.mem_map, List.mem_range] at hp
    obtain ⟨lane, hl, rfl⟩ := hp
    refine ⟨by simp [launch]; omega, by simp, 1, .arrive, ?_⟩
    simp [Execution.get, early, show lane < 32 from hl]
  · rintro ⟨g, i⟩ id count pc he
    refine ⟨by simp [ctaBarNeeds], ?_⟩
    simp only [Execution.get, early] at he
    split_ifs at he with hg
    · obtain _ | _ | _ | i := i <;> simp at he
      have h0 : g / launch.block = 0 := by simp [launch]; omega
      simp only [early, h0, ite_true, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        CtaBarrier.Record.refs, lanes, List.mem_map, List.mem_range]
      exact ⟨(g, (g, 1)), ⟨g, hg, by simp⟩, rfl⟩
    · simp at he

/-! ## Faults of the resource -/

-- After warp 0's `bar.arrive 1, 64`, a `bar.sync 1, 128` of warp 1 joins the open generation with
-- another count: the resource cannot perform it (`countMismatch`, a fault of `CtaBarFault`).
example : ∃ s, CtaBarrier.run 128 {} [.arrival 1 0 (some 64) (lanes 0 1)] = .ok s ∧
    CtaBarrier.Record.perform 128 s (.arrival 1 1 (some 128) (lanes 1 0)) =
      .error .countMismatch :=
  ⟨_, rfl, rfl⟩

-- Warp 0 executes `bar.arrive 1, 64` and then `bar.sync 1, 64` before warp 1 arrived (the case
-- §9.7.15.1 warns about): its second arrival in the open generation is `duplicateArrival`.
example : ∃ s, CtaBarrier.run 128 {} [.arrival 1 0 (some 64) (lanes 0 1)] = .ok s ∧
    CtaBarrier.Record.perform 128 s (.arrival 1 0 (some 64) (lanes 0 2)) =
      .error .duplicateArrival :=
  ⟨_, rfl, rfl⟩

example : CtaBarrier.Error.isFault .countMismatch = true ∧
    CtaBarrier.Error.isFault .duplicateArrival = true := ⟨rfl, rfl⟩

/-! ## A warp mixing the two forms -/

private def mixed : Execution := {
  tr := fun g => if g = 0 then [⟨1, .bar 1 (some 64) .arrive⟩]
    else if g = 1 then [⟨3, .bar 1 (some 64) .sync⟩] else []
  rf := fun _ _ => none
}

-- Lanes 0 and 1 of warp 0 execute their first barrier instruction in different forms.
theorem mixed_mismatch : BarMismatch launch mixed :=
  .inr ⟨0, 1, 0, 0, 1, 1, some 64, some 64, .sync, 1, 3,
    ⟨⟨by decide, by decide, by decide⟩, by decide⟩, rfl, rfl, rfl,
    .inr (.inr (by decide))⟩

end
end PTX.Tests.CtaBarrierArrive
