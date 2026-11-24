-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Thread.Run
public import Core.Assembly.Waiting
public import Core.Assembly.Dependency

namespace PTX.Tests.NamedBarriers

private def lanes (w : Nat) : List (Nat × EvId) :=
  (List.range 32).map fun lane => let g := w * 32 + lane; (g, (g, 0))

private def history : List (CtaBarrier.Record EvId) :=
  [.arrival 3 0 (some 32) (lanes 0), .arrival 3 1 (some 32) (lanes 1)]

private def launch : Launch := { grid := 1, block := 64, params := fun _ => none }

private def execution : Execution := {
  tr := fun g => if g < 64 then [⟨0, .bar 3 (some 32)⟩, ⟨1, .exit⟩] else []
  rf := fun _ _ => none
  barriers := fun c => if c = 0 then history else []
}

private def afterFirst : CtaBarrier.State := {
  slots := fun id => if id = 3 then { generation := 1 } else {}
}

private def afterSecond : CtaBarrier.State := {
  slots := fun id => if id = 3 then { generation := 2 } else afterFirst.slots id
}

-- Thread 32's first barrier is resource generation 1, NOT its per-thread ordinal 0.
example : CtaBarK launch execution (32, 0) 19 := by
  refine ⟨by decide, ⟨some 32, 0, rfl⟩, ?_⟩
  refine ⟨1, afterFirst, 1, some 32, lanes 1, 32, rfl, ?_, ?_, rfl, ?_⟩
  · rfl
  · decide
  · exact ⟨afterSecond, rfl⟩

-- The same event cannot also be assigned to phase 0 just because it is the
-- first barrier in its thread's trace.
example : ¬ CtaBarK launch execution (32, 0) 3 := by
  intro hk
  obtain ⟨i, s, w, count, ls, g, hi, hs, he, hg, _⟩ := hk.2.2
  change history[i]? = some (.arrival 3 w count ls) at hi
  cases i with
  | zero =>
    simp only [history, List.getElem?_cons_zero] at hi
    cases hi
    simp only [lanes, List.mem_map, List.mem_range] at he
    obtain ⟨lane, hl, hp⟩ := he
    have hh := congrArg (fun p : Nat × EvId => p.2.1) hp
    simp only [Nat.zero_mul, Nat.zero_add] at hh
    omega
  | succ i =>
    cases i with
    | zero =>
      simp only [history, List.getElem?_cons_succ, List.getElem?_cons_zero] at hi
      cases hi
      have hstate : afterFirst = s := by
        apply Except.ok.inj
        exact (show CtaBarrier.run 64 {} (history.take 1) = .ok afterFirst from rfl).symm.trans hs
      cases hstate
      exact (by decide : (1 : Nat) ≠ 0) hg
    | succ i => simp [history] at hi

example : CtaBarDone launch execution 0 19 := by
  exact ⟨1, .arrival 3 1 (some 32) (lanes 1), afterFirst, afterSecond,
    rfl, rfl, rfl, rfl, rfl⟩

-- Source provenance checks the count operand, not merely the barrier ID.
example : ¬ CtaBarSources launch execution 0
    (.arrival 3 1 (some 64) [(32, (32, 0))]) := by
  intro h
  obtain ⟨_, _, pc, hp⟩ := h (32, (32, 0)) (by simp)
  simp [Execution.IsBarArrival, Execution.get, execution] at hp

-- A record cannot claim a lane from another CTA.
example : ¬ CtaBarSources launch execution 0
    (.arrival 3 1 (some 32) [(32, (96, 0))]) := by
  intro h
  have hp := (h (32, (96, 0)) (by simp)).2.1
  exact (by decide : (96 : Nat) ≠ 32) hp

-- The real instruction path preserves a partial-CTA count in its event template.
example : barTmpl { launch with block := 384 } 128 {} (.imm 3) (some (.imm 128)) =
    .bar 3 { pc := 1 } (some 128) := rfl

example : Fires 7 (.bar 3 { pc := 8 } (some 128))
    ⟨7, .bar 3 (some 128)⟩ (some { pc := 8 }) := ⟨rfl, rfl⟩

-- A trace cannot pass its barrier just because its source event exists.
-- It needs an actual collective arrival and completion in the resource history: the condition
-- need of its `bar.sync` (DEP-ORDER) is unfilled, so the barrier event is not ready.
example : ¬ Ready launch { execution with barriers := fun _ => [] } (0, 0) := by
  let X : Execution := { execution with barriers := fun _ => [] }
  intro h
  have hn := h (.cond (∃ key, CtaBarK launch X (0, 0) key ∧ CtaBarDone launch X 0 key)) (by
    simp only [Needs, Execution.get, X, execution]
    simp [KindNeeds, ctaBarNeeds])
  obtain ⟨key, hk, _⟩ := hn
  obtain ⟨i, s, w, count, ls, g, hi, _⟩ := hk.2.2
  simp [X] at hi

-- Zero is the whole-CTA sync form, not an immediate release or undefined count.
example : barTmpl launch 0 {} (.imm 0) (some (.imm 0)) =
    .bar 0 { pc := 1 } := rfl

end PTX.Tests.NamedBarriers
