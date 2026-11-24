-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode
public import Mathlib.Tactic
public import Lemmas.Order.OrderWaits
public import Lemmas.Order.DependencyWitness

namespace PTX.Tests.WarpBarrier
noncomputable section
private def L : Launch := { grid := 1, block := 64, params := fun _ => none }
example : warpBarTmpl L 0 {} (.imm 2) = .ub .badBarrier := rfl
example : warpBarTmpl L 1 {} (.imm 2) = .warpBar 2 (next {}) := rfl
example : Decode.op { classes := [], labels := [], params := [] } "bar.warp.sync" [.literal "3"] =
    .ok (.warp { kind := .barWarp, mask := some (.imm 3) }) := rfl

-- Every named lane must actually participate, not merely belong to the launch: its event is a
-- need of the barrier's return (`KindNeeds`, DEP-ORDER), which readiness fills.
example {X : Execution} (h : WarpBarOk L X) (hready : ∀ e, Returned X e → Ready L X e)
    (he : X.WarpBar (0, 0) 3 7) :
    ∃ g j, g < L.threads ∧ SameWarp L 0 g ∧ laneOf L g = 1 ∧ X.WarpBar (g, j) 3 7 := by
  obtain ⟨pc, hp⟩ := he
  have hneed : Need.node (fun x => ∃ k, x = .thread (warpLane L 0 1, k) ∧
      X.WarpBar (warpLane L 0 1, k) 3 7) ∈ Needs L X (0, 0) :=
    warpBarNeed_of_lane hp (by decide) (by decide)
  obtain ⟨x, -, k, rfl, hw⟩ := hready _ (by simp [Returned, hp, Kind.resume]) _ hneed
  have hsw : SameWarp L 0 (warpLane L 0 1) := by
    unfold SameWarp SameCta warpLane laneOf L Launch.threads
    decide
  have hlane : laneOf L (warpLane L 0 1) = 1 := by
    unfold warpLane laneOf L
    decide
  exact ⟨_, k, (h.1 _ _ _ hw).1, hsw, hlane, hw⟩

-- One dynamic instance cannot stand for two iterations by the same lane.
example {X : Execution} (h : WarpBarOk L X)
    (a : X.WarpBar (0, 0) 3 7) (b : X.WarpBar (0, 1) 3 7) : False := by
  have he := (h.2 _ _ _ _ _ a b (by unfold SameWarp SameCta L Launch.threads; decide)).2 rfl
  have := congrArg Prod.snd he
  omega

example {X : Execution} : ¬ WarpBarEdge L X (0, 0) (32, 0) := by
  intro h
  have bad : ¬ SameWarp L 0 32 := by unfold SameWarp SameCta L Launch.threads; decide
  exact bad h.1

-- Barrier order is part of hb, and therefore of the actual read/race checks.
example {X : Execution} {e f : EvId} (h : WarpBarSync L X e f) : baseCausality L X e f :=
  .single (.inr (.inr (.inr (.inr (.inl h)))))
example {X : Execution} {e f : EvId} (h : WarpBarSync L X e f) :
    Relation.TransGen (Waits L X) (.thread e, true) (.thread f, false) :=
  baseCausality_waits (.single (.inr (.inr (.inr (.inr (.inl h))))))
end
end PTX.Tests.WarpBarrier
