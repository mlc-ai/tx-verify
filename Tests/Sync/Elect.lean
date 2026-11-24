-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Elect
public import Core.Source.Decode
public import Mathlib.Tactic

namespace PTX.Tests.Elect
noncomputable section
private def L : Launch := { grid := 1, block := 32, params := fun _ => none }
private def X : Execution := {
  tr := fun g => if g = 5 then [⟨10, .elect 32 19 5⟩] else []
  rf := fun _ _ => none }

private theorem event_eq {e : EvId} {pc mask inst leader : Nat}
    (h : X.Elect e pc mask inst leader) :
    e = (5, 0) ∧ pc = 10 ∧ mask = 32 ∧ inst = 19 ∧ leader = 5 := by
  rcases e with ⟨g, i⟩
  by_cases hg : g = 5
  · subst g
    cases i with
    | zero => simpa [Execution.Elect, Execution.get, X, eq_comm] using h
    | succ i => simp [Execution.Elect, Execution.get, X] at h
  · simp [Execution.Elect, Execution.get, X, hg] at h

-- A nonzero lane and a partial mask are legal; no lane-zero convention is assumed.
example : ElectOk L X := by
  refine ⟨?_, ?_, ?_⟩
  · intro e pc mask inst leader he
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := event_eq he
    exact ⟨by decide, by decide, by decide⟩
  · intro e f pc pc' mask mask' inst leader leader' he hf hw
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := event_eq he
    obtain ⟨rfl, rfl, rfl, _, rfl⟩ := event_eq hf
    exact ⟨rfl, rfl, rfl, fun _ => rfl⟩
  · intro e f pc pc' mask inst inst' leader leader' he hf _
    exact (event_eq he).2.2.2.2.trans (event_eq hf).2.2.2.2.symm

-- An executing nonmember faults before any election event can be returned.
example : electTmpl L 0 {} none 0 (.imm 32) = .ub .badValue := rfl
example : electTmpl L 5 {} none 0 (.imm 32) =
    .elect 32 (fun leader => next (setReg {} 0 (.pred (5 == leader)))) := rfl

-- The needs of an election name every lane of its member mask.
private theorem needs_elect {Y : Execution} {e : EvId} {pc mask inst leader lane : Nat}
    (h : Y.get e = some ⟨pc, .elect mask inst leader⟩) (hlane : lane < 32)
    (hm : mask.testBit lane = true) :
    (Need.node fun x => ∃ j pc leader, x = .thread (warpLane L e.1 lane, j) ∧
      Y.get (warpLane L e.1 lane, j) = some ⟨pc, .elect mask inst leader⟩) ∈ Needs L Y e := by
  simp only [Needs, h, KindNeeds, List.mem_map, List.mem_filter, List.mem_range]
  exact ⟨lane, ⟨hlane, hm⟩, rfl⟩

-- A returned collective cannot omit another member lane.
example {Y : Execution} (he : Y.Elect (0, 0) 10 3 7 0)
    (missing : ∀ h j pc leader, SameWarp L 0 h → laneOf L h = 1 →
      ¬ Y.Elect (h, j) pc 3 7 leader) : ¬ Ready L Y (0, 0) := by
  intro hy
  obtain ⟨x, _, j, pc, leader, rfl, hget⟩ :=
    hy _ (needs_elect (lane := 1) he (by decide) (by decide))
  simp only [warpLane, laneOf, L] at hget
  exact missing 1 j pc leader ⟨⟨by decide, by decide, rfl⟩, by decide⟩ (by decide) hget

-- Repeating a mask cannot silently change its chosen leader.
example {Y : Execution} (ha : Y.Elect (0, 0) 10 3 7 0)
    (hb : Y.Elect (0, 1) 10 3 8 1) : ¬ ElectOk L Y := by
  intro hy
  have h := hy.deterministic ha hb (show SameWarp L 0 0 from ⟨⟨by decide, by decide, rfl⟩, rfl⟩)
  cases h

-- One label cannot merge two loop iterations from the same lane.
example {Y : Execution} (ha : Y.Elect (0, 0) 10 1 7 0)
    (hb : Y.Elect (0, 1) 10 1 7 0) : ¬ ElectOk L Y := by
  intro hy
  have he := hy.instance_unique ha hb (show SameWarp L 0 0 from
    ⟨⟨by decide, by decide, rfl⟩, rfl⟩) rfl
  cases he

-- Election rendezvous participates in realizability: a participant's arrival fills a need of the
-- election's return, so the return cannot then depend on that arrival.
example {K : Kernel} {Y : Execution} {o : OrderObject} {e f : EvId} (hen : o.Enabling)
    (he : Witness L Y (.thread f) e)
    (back : Relation.TransGen
      (fun a c => DepStep L K Y a c ∨ ObjectOrder L Y o a c) (.thread e, true) (.thread f, false)) :
    ¬ DependencyOk L K Y := by
  intro ha
  exact ha.acyclic o hen (.thread f, false)
    (Relation.TransGen.head (.inl (DepStep.of_witness L he)) back)

-- Two warps with one mask may elect different lanes (§9.7.15.15 fixes the leader per warp).
private def L2 : Launch := { grid := 1, block := 64, params := fun _ => none }
private def X2 : Execution := {
  tr := fun g => if g = 0 ∨ g = 1 then [⟨10, .elect 3 0 0⟩]
    else if g = 32 ∨ g = 33 then [⟨10, .elect 3 0 1⟩] else []
  rf := fun _ _ => none }

private theorem event2 {e : EvId} {pc mask inst leader : Nat}
    (h : X2.Elect e pc mask inst leader) :
    pc = 10 ∧ mask = 3 ∧ inst = 0 ∧ e.2 = 0 ∧
      ((e.1 = 0 ∨ e.1 = 1) ∧ leader = 0 ∨ (e.1 = 32 ∨ e.1 = 33) ∧ leader = 1) := by
  rcases e with ⟨g, i⟩
  simp only [Execution.Elect, Execution.get, X2] at h
  split_ifs at h with h1 h2 <;> cases i <;> simp at h
  all_goals (obtain ⟨rfl, rfl, rfl, rfl⟩ := h;
             refine ⟨rfl, rfl, rfl, rfl, ?_⟩; first | exact .inl ⟨h1, rfl⟩ | exact .inr ⟨h2, rfl⟩)

private theorem lanes3 {lane : Nat} (h : electMember 3 lane) : lane = 0 ∨ lane = 1 := by
  obtain ⟨hl, hb⟩ := h
  interval_cases lane <;> first | exact .inl rfl | exact .inr rfl | exact absurd hb (by decide)

/-- Elections of two warps with the same mask may choose different lanes: the same-mask
leader is fixed within one warp only (§9.7.15.15). -/
example : ElectOk L2 X2 := by
  have hth : L2.threads = 64 := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro e pc mask inst leader he
    obtain ⟨rfl, rfl, rfl, h2, hcase⟩ := event2 he
    refine ⟨by omega, ?_, ?_⟩
    · rcases hcase with ⟨h | h, -⟩ | ⟨h | h, -⟩ <;> simp [electMember, laneOf, L2, h] <;> decide
    · rcases hcase with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  · intro e f pc pc' mask mask' inst leader leader' he hf hw
    obtain ⟨rfl, rfl, rfl, he2, hce⟩ := event2 he
    obtain ⟨rfl, rfl, -, hf2, hcf⟩ := event2 hf
    obtain ⟨-, hwarp⟩ := hw
    simp only [L2] at hwarp
    refine ⟨rfl, rfl, ?_, fun h => Prod.ext h (by omega)⟩
    rcases hce with ⟨h1 | h1, rfl⟩ | ⟨h1 | h1, rfl⟩ <;>
      rcases hcf with ⟨h2 | h2, rfl⟩ | ⟨h2 | h2, rfl⟩ <;>
      simp only [h1, h2] at hwarp <;> omega
  · intro e f pc pc' mask inst inst' leader leader' he hf hw
    obtain ⟨rfl, rfl, rfl, -, hce⟩ := event2 he
    obtain ⟨-, -, -, -, hcf⟩ := event2 hf
    obtain ⟨-, hwarp⟩ := hw
    simp only [L2] at hwarp
    rcases hce with ⟨h1 | h1, rfl⟩ | ⟨h1 | h1, rfl⟩ <;>
      rcases hcf with ⟨h2 | h2, rfl⟩ | ⟨h2 | h2, rfl⟩ <;>
      simp only [h1, h2] at hwarp <;> omega

-- Readiness of an election names the lanes of its own warp: X2 supplies the two lanes of mask 3.
example : Ready L2 X2 (0, 0) := by
  intro n hn
  have hget : X2.get (0, 0) = some ⟨10, .elect 3 0 0⟩ := by simp [Execution.get, X2]
  have hn' : n ∈ ((List.range 32).filter (fun l => (3 : Nat).testBit l)).map
      (fun l => Need.node fun x => ∃ j pc leader, x = .thread (warpLane L2 0 l, j) ∧
        X2.get (warpLane L2 0 l, j) = some ⟨pc, .elect 3 0 leader⟩) := by
    simpa only [Needs, hget, KindNeeds] using hn
  obtain ⟨lane, hmem, rfl⟩ := List.mem_map.mp hn'
  obtain ⟨-, hbit⟩ := List.mem_filter.mp hmem
  have hbit' : electMember 3 lane := ⟨List.mem_range.mp (List.mem_filter.mp hmem).1, hbit⟩
  rcases lanes3 hbit' with rfl | rfl
  · refine ⟨.thread (0, 0), ⟨⟨⟨10, .elect 3 0 0⟩, hget⟩, 0, 10, 0, ?_, ?_⟩⟩
    · simp [warpLane, laneOf, L2]
    · simp [warpLane, laneOf, L2, Execution.get, X2]
  · refine ⟨.thread (1, 0), ⟨⟨⟨10, .elect 3 0 0⟩, by simp [Execution.get, X2]⟩, 0, 10, 0, ?_, ?_⟩⟩
    · simp [warpLane, laneOf, L2]
    · simp [warpLane, laneOf, L2, Execution.get, X2]

private def env : Decode.Env :=
  { classes := [⟨"p".toList, 0, 1⟩, ⟨"r".toList, 0, 32⟩], labels := [], params := [] }
example : Decode.op env "elect.sync" [.pair [.sink, .register "p"], .literal "-1"] =
    .ok (.warp { kind := .elect, dsts := [none, some 0], mask := some (.imm (-1)) }) := rfl
example : Decode.op env "elect.sync" [.pair [.register "r", .register "p"], .literal "3"] =
    .ok (.warp { kind := .elect, dsts := [some 1, some 0], mask := some (.imm 3) }) := rfl

end
end PTX.Tests.Elect
