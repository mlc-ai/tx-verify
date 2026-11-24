-- SPDX-License-Identifier: Apache-2.0
module

public meta import Lean

@[expose] public section

/-! Kernel-checked reflexivity for concrete equations. -/
open Lean Meta Elab Tactic

elab "kernel_rfl" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← whnf (← instantiateMVars (← goal.getType))
  let some (_, _, rhs) := target.eq? | throwError "expected equality"
  let proof ← mkEqRefl rhs
  let lctx ← getLCtx
  let used ← (collectFVars (collectFVars {} target) proof).addDependencies
  let variables := lctx.getFVars.filter fun localVar =>
    used.fvarSet.contains localVar.fvarId!
  let closedType ← mkForallFVars variables target (usedLetOnly := false)
  let closedProof ← mkLambdaFVars variables proof (usedLetOnly := false)
  let closedType ← instantiateMVars closedType
  let closedProof ← instantiateMVars closedProof
  let levels := (collectLevelParams {} closedType).params.toList
  let name ← withOptions (Elab.async.set · false) <|
    mkAuxLemma levels closedType closedProof
  let arguments := variables.filter fun localVar =>
    !(lctx.get! localVar.fvarId!).isLet
  goal.assign (mkAppN (mkConst name (levels.map .param)) arguments)
  replaceMainGoal []
