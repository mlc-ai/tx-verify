-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof.Softmax.Control.Machine

@[expose] public section
namespace PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
open PTX.Flow

set_option maxRecDepth 12000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

variable {p : Params} {L : Launch} {g : Nat} {e : Event} {a : Softmax.D}

/-- A live value-machine transition retains exactly the control successor. -/
def Projects (d : Softmax.D) : Prop :=
  ∀ e a, Softmax.succ p L g d e = some (some a) →
    succ p L g (erase d) e = some (some (erase a))

set_option hygiene false in
scoped macro "project_step" : tactic => `(tactic| (
  intro ev a hn
  simp only [succ, erase, D.scheduler, V.scheduler, D.site, D.v, D.k]
  simp only [Softmax.succ, D.scheduler, V.scheduler, word32, afterTiles, afterTotal, loopHead,
      scanExit, passStart, afterFirst, afterBias, afterPlain, plainEntry, afterRound,
      Softmax.D.ite] at hn ⊢
  repeat' split at hn
  all_goals simp_all (config := {maxSteps := 40000}) only [Option.map_some, Option.map_none,
      Option.some.injEq, reduceCtorEq, not_true_eq_false, false_implies, D.scheduler, V.scheduler,
    ↓reduceIte, Bool.false_eq_true, not_false_eq_true, Option.some_ne_none]
  all_goals first | rfl | (subst a; rfl)))

end PTX.Kernels.TmlFa4Fwd.Proof.Softmax.Control
