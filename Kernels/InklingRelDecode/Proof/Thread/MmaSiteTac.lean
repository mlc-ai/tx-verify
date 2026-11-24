-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.InklingRelDecode.Proof.Thread.MmaStepBase
public import Lemmas.Flow.Step.SiteIte
public import Lemmas.Flow.Step.StopReason

@[expose] public section

/-! # What `site_cases` needs of the MMA warp

The obligations of `code` are proved by `site_cases` (`MmaSteps`) with the tactics of this file:

* `mma_env`: the shape facts of the launch and the loop (`Env`) from `Pre` and the invariant in
  context, as hypotheses for the evaluation's arithmetic;
* `mma_seg`: a segment, by evaluation with the bit lemmas of the loop (`ink_seg`'s set);
* `mma_inv`: the successor's invariant, from `inv_site`, `inv_far` or `inv_ldNum`;
* `mma_guard`: the elected-lane guards of the MMAs and commits, true in the table. -/

namespace PTX.Kernels.InklingRelDecode.Proof.Mma
open PTX PTX.Proof PTX.Flow

noncomputable section
set_option maxRecDepth 100000

variable {P : Params} {L : Launch} {mem0 : Mem0} {g : Nat}

/-- The invariant at `barrier.sync 1` after the read of `num_iters`: `%r10` holds the word read,
and `n` is the number the code reads it as. -/
theorem inv_ldNum {i n tm : Nat} {pro : Nat → Value} (hi : Inv ⟨.ldNum, i, n, tm, pro⟩)
    (v : Value) :
    Inv ⟨.bar0, i, (Raw.word32Of v).getD 0, tm, Function.update pro 471 v⟩ := by
  refine ⟨?_, hi.tm, hi.col, fun _ => hi.pre trivial, fun h => False.elim h,
    fun h => False.elim h, fun h => absurd trivial h, fun _ m hm => ?_, fun h => False.elim h⟩
  · cases hw : Raw.word32Of v with
    | none => simp
    | some m => simpa using Raw.word32Of_lt hw
  · simp only [Function.update_self] at hm ⊢
    simp [hm]

open Lean Elab Tactic Meta

/-- Run a tactic with elaboration errors as failures; on failure, leave the goal unchanged. -/
meta def tryStrict (stx : TSyntax `tactic) : TacticM Unit := do
  let s ← saveState
  try Term.withoutErrToSorry (evalTactic stx)
  catch _ => s.restore

/-- `mma_env`: the facts of `Env` and of the loop bounds, from `Pre` and the invariant in
context, as hypotheses (for the evaluation's arithmetic). -/
elab "mma_env" : tactic => withMainContext do
  for ld in ← getLCtx do
    if ld.isImplementationDetail then continue
    let ty ← instantiateMVars ld.type
    if ty.isAppOfArity ``Pre 3 then
      let h ← Term.exprToSyntax ld.toExpr
      tryStrict (← `(tactic| have := pre_shared $h))
  for ld in ← getLCtx do
    if ld.isImplementationDetail then continue
    let ty ← whnfR (← instantiateMVars ld.type)
    if ty.isAppOfArity ``Inv 1 then
      let h ← Term.exprToSyntax ld.toExpr
      tryStrict (← `(tactic| (have := ($h).n; have := ($h).tm)))
      tryStrict (← `(tactic| obtain ⟨_, _⟩ := ($h).qk trivial))
      tryStrict (← `(tactic| obtain ⟨_, _, _⟩ := ($h).pv trivial))
      tryStrict (← `(tactic| simp only at *))
      tryStrict (← `(tactic| have : D.i $(← Term.exprToSyntax ty.appArg!) < 2 ^ 31 := by
        simp only at *; omega))
      tryStrict (← `(tactic| simp only at *))
      return
  throwError "mma_env: no invariant"

/-- A segment by evaluation, with the loop's bit lemmas. -/
macro "mma_seg" : tactic => `(tactic| (
  mma_env
  intro t h
  seg_fp h using
    try ink_values
    all_goals seg_close [mulhi3, Nat.and_one_is_mod, bfe_u32, lor_field, qLo, kLo, vLo,
      desc, vdesc, descHi]))

/-- `mma_pre` (the role's `seg_pre`): a segment to the state after the QK half (`afterQk`) or after
an iteration (`iterNext`) is cut where that control code starts (pc 2500, pc 2447); the rest
is `seg_afterQk` or `seg_iter`, whose test of `num_iters` reads the loaded word. -/
elab "mma_pre" : tactic => withMainContext do
  let ty ← instantiateMVars (← getMainTarget)
  let some e := ty.find? (fun e => e.isAppOfArity ``afterQk 1 || e.isAppOfArity ``iterNext 1) |
    throwError "mma_pre: no control code"
  let some (_, body) := ty.consumeMData.app2? ``Exists | throwError "mma_pre: not a segment"
  let .lam _ _ seg _ := body.consumeMData | throwError "mma_pre: not a segment"
  let tL ← Term.exprToSyntax (seg.getArg! 2)
  let td ← Term.exprToSyntax e.appArg!
  let mut hpre? := none
  let mut hi? := none
  for ld in ← getLCtx do
    if ld.isImplementationDetail then continue
    let t ← instantiateMVars ld.type
    if t.isAppOfArity ``Pre 3 then hpre? := some (← Term.exprToSyntax ld.toExpr)
    if (← whnfR t).isAppOfArity ``Inv 1 then hi? := some (← Term.exprToSyntax ld.toExpr)
  let (some hpre, some hi) := (hpre?, hi?) | throwError "mma_pre: no Pre or invariant"
  let stx ← if e.isAppOfArity ``afterQk 1 then
      `(tactic| refine Seg.comp_ex (q := 2500) (H := factsAt $tL 2500 $td) ?_
        (seg_afterQk (env_qk $hpre $hi trivial).1 (env_qk $hpre $hi trivial).2))
    else
      `(tactic| refine Seg.comp_ex (q := 2447) (H := factsAt $tL 2447 $td) ?_
        (seg_iter (env_pv $hpre $hi trivial).1 (env_pv $hpre $hi trivial).2.2))
  Term.withoutErrToSorry (evalTactic stx)

macro_rules | `(tactic| seg_pre) => `(tactic| mma_pre)

set_option hygiene false in
/-- The successor's invariant. -/
macro "mma_inv" : tactic => `(tactic| (intro hi; first
  | exact inv_afterQk hi (hi.qk trivial).2 (hi.qk trivial).1 (not_pre_of_qk trivial)
  | exact inv_iterNext hi (hi.pv trivial).2.2 (hi.pv trivial).2.1 (not_pre_of_pv trivial)
  | exact inv_site hi _ (fun h => False.elim h) (fun _ => hi.qk trivial) (fun h => False.elim h)
  | exact inv_site hi _ (fun h => False.elim h) (fun h => False.elim h) (fun _ => hi.pv trivial)
  | exact inv_far hi _ (fun h => h) (fun h => h) (fun h => h)
  | exact inv_site hi _ (fun _ => hi.pre trivial) nofun nofun
  | exact inv_ldNum hi _
  | fail "mma_inv"))

/-- The guard of an MMA or commit: the elected-lane predicate, true in the table. -/
macro "mma_guard" : tactic => `(tactic| first
  | rfl
  | (ink_values; done)
  | fail "mma_guard")

/-- `mma_steps s`: the obligations of the sites `s` ranges over, except the given overrides and
the sites `skip_by` closes. -/
syntax "mma_steps " ident (" except " "[" siteOverride,* "]")? " skip_by " "(" tacticSeq ")" :
  tactic
macro_rules
  | `(tactic| mma_steps $s $[except [$ovs,*]]? skip_by ($skip)) => do
    let ovs := (ovs.map (·.getElems)).getD #[]
    `(tactic| site_cases $s except [$ovs,*] skip_by ($skip)
      trans [next, qkNext, pvNext, Option.some.injEq, Fin.val_zero, Fin.coe_ofNat_eq_mod,
        Nat.reduceMod, Nat.reduceAdd, Nat.reduceLT, ↓reduceDIte]
      seg_by (mma_seg) inv_by (mma_inv) guard_by (mma_guard))

end
end PTX.Kernels.InklingRelDecode.Proof.Mma
