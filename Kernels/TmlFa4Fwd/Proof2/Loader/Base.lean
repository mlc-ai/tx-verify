-- SPDX-License-Identifier: Apache-2.0
module

public import Kernels.TmlFa4Fwd.Proof2.Loader.Machine
public import Kernels.TmlFa4Fwd.Proof2.Epilogue.Base
public import Lemmas.Flow.Step.SiteIte
public import Lemmas.Flow.TryRt

@[expose] public section

/-! # Shared facts and tactics of the loader warps' step files

The role's tactic for the obligations of one family of sites (`load_sites`): `site_cases` over
the site, segments by `seg_fp` closed by `rfl` or `sym_close` (as the output warp's `ep_seg`, with
its launch facts: the explicit parameters, the CTA index bound, no rule of an assumption on the
integer code; `load_seg`), the successor's invariant by its sub-step (`load_inv`). -/

namespace PTX.Kernels.TmlFa4Fwd.Proof2.Loader
open PTX PTX.Proof PTX.Flow
open PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue (scmpi andi)

noncomputable section
set_option maxRecDepth 100000

/-- The role's landing obligation: the successor's sub-step is 0 and its accumulator empty (in
every branch of a conditional successor), its segment by `seg_auto`, else `seg_sym` (which
splits a conditional end itself), and its invariant by the role's tactic. Tried before the
library's rules. -/
macro_rules
  | `(tactic| lands_auto ($seg) ($inv)) => `(tactic| (
      intros
      refine ⟨?seg, ?sub, ?acc, ?inv⟩
      case sub => first | rfl | ((repeat' ite_cases) <;> rfl)
      case acc => first | rfl | ((repeat' ite_cases) <;> rfl)
      case seg =>
        intro _
        site_norm
        try dsimp only [PTX.Flow.Code.electFacts]
        try drop_norm
        first
          | seg_auto using $seg
          | seg_sym using $seg
      case inv =>
        site_norm
        ($inv)))

theorem geW_true {x y : BitVec 64} (h : geW x y = true) : Epilogue.scmp .ge .s x y = true :=
  (geW_eq x y).symm.trans h
theorem geW_false {x y : BitVec 64} (h : ¬ geW x y = true) : Epilogue.scmp .ge .s x y = false := by
  rw [geW_eq] at h; simpa using h
theorem ltZ_true {x : BitVec 64} (h : ltZ x = true) : scmpi .lt .s x 0 = true :=
  (ltZ_eq x).symm.trans h
theorem ltZ_false {x : BitVec 64} (h : ¬ ltZ x = true) : scmpi .lt .s x 0 = false := by
  rw [ltZ_eq] at h; simpa using h

open Lean Elab Tactic Meta in
/-- `opaque_decide`: close the decision `c = b` of the code's branch from a hypothesis about an
opaque condition (`geW`, `ltZ`) whose unfolding is `c` (by unification). -/
elab "opaque_decide" : tactic => withMainContext do
  let goal ← getMainGoal
  let gty ← instantiateMVars (← goal.getType)
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    -- only a hypothesis about `geW` or `ltZ` (`c = true`, or its negation)
    let ty ← instantiateMVars d.type
    let ty := if ty.isAppOfArity ``Not 1 then ty.appArg! else ty
    let some (_, lhs, _) := ty.consumeMData.eq? | continue
    unless lhs.isAppOfArity ``geW 2 || lhs.isAppOfArity ``ltZ 1 do continue
    for lem in [``geW_true, ``geW_false, ``ltZ_true, ``ltZ_false] do
      let ok ← tryCatchRuntimeEx (observing? do
        let pf ← mkAppM lem #[d.toExpr]
        unless ← isDefEq (← inferType pf) gty do failure
        pure pf) (fun _ => pure none)
      if let some pf := ok then
        goal.assign pf
        replaceMainGoal []
        return
  throwError "opaque_decide: no hypothesis"

/-- The code's branch on a condition the machine states as an opaque constant (`geW`, `ltZ`):
decided by the hypothesis of the successor's case split, unfolded. -/
macro_rules
  | `(tactic| sym_decide) => `(tactic| opaque_decide)

/-- The invariant of a successor: a state at sub-step 0, or the second element of an address
load. -/
macro "load_inv" : tactic => `(tactic| first
  | exact fun _ => Or.inl rfl
  | exact fun _ => Or.inr trivial
  | ((intro _; repeat' split) <;> exact Or.inl rfl))

/-- A segment by its footprint (`seg_fp`), closed by `rfl` or `sym_close`. An evaluation that runs
away (the segments of 25 and more instructions through a loop's back edge into the warm and
steady blocks) fails instead of aborting (`catch_rt`), so that `seg_sym` takes the segment. -/
macro "load_seg" : tactic => `(tactic| (
  intro t h
  catch_rt seg_fp h using first | rfl | sym_close))

/-- `load_sites s except […]`: the obligations of the sites of `s` that the theorem's hypothesis
`hs` admits. -/
syntax "load_sites " (ppSpace colGt ident)+ (" except " "[" siteOverride,* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| load_sites $ss* $[except [$ovs,*]]?) => `(tactic|
      site_cases $ss* $[except [$ovs,*]]? skip_by (simp at hs)
        trans [succ, word32, scAt, D.mk', D.ite, D.iteS, afterTotal, loopHead, scanExit, passStart,
          afterTiles, drain0, pgEnter, withSetup, afterArrive, afterPrime, afterWarm, afterTail,
          warmEnd, steadyEnd, pkStart, rowCond,
          groupEnd, teNext, teElected, dwNext, PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue.loopOf,
          PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue.Scan.late,
          PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue.tlOf]
        seg_by (load_seg) inv_by (load_inv) guard_by (trivial))

/-- `load_step`: the obligation of the one site of the goal (`site_step` with the role's
lemmas). -/
syntax "load_step" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| load_step) => `(tactic|
      site_step
        trans [succ, word32, scAt, D.mk', D.ite, D.iteS, afterTotal, loopHead, scanExit, passStart,
          afterTiles, drain0, pgEnter, withSetup, afterArrive, afterPrime, afterWarm, afterTail,
          warmEnd, steadyEnd, pkStart, rowCond,
          groupEnd, teNext, teElected, dwNext, PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue.loopOf,
          PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue.Scan.late,
          PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue.tlOf]
        seg_by (load_seg) inv_by (load_inv) guard_by (trivial))

/-- `load_issue lemma`: the obligation of an event that continues at the next instruction by
`lemma` (an override of `load_sites`). -/
syntax "load_issue " term : tactic
set_option hygiene false in
macro_rules
  | `(tactic| load_issue $adv) => `(tactic|
      issue_step $adv
        trans [succ, word32, scAt, D.mk', D.ite, D.iteS, afterTotal, loopHead, scanExit, passStart,
          afterTiles, drain0, pgEnter, withSetup, afterArrive, afterPrime, afterWarm, afterTail,
          warmEnd, steadyEnd, pkStart, rowCond,
          groupEnd, teNext, teElected, dwNext, PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue.loopOf,
          PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue.Scan.late,
          PTX.Kernels.TmlFa4Fwd.Proof2.Epilogue.tlOf]
        seg_by (load_seg) inv_by (load_inv))

/-- A segment cut at program counter `q`, where the facts are the end state's table. -/
theorem seg_cut {K : Kernel} {A : List Assumption} {L : Launch} {g s b : Nat}
    (q : Nat) {F : List (Nat × Value)} {val : Nat → Value}
    (h1 : ∃ n, Seg K A L g n s F q (Flow.factsFrom (Flow.live q) val))
    (h2 : ∃ n, Seg K A L g n q (Flow.factsFrom (Flow.live q) val) b
      (Flow.factsFrom (Flow.live b) val)) :
    ∃ n, Seg K A L g n s F b (Flow.factsFrom (Flow.live b) val) :=
  Seg.comp_ex h1 h2

/-- The predicates of the dispatch on the warp index that the loader's return passes, for warps
14 and 15. -/
theorem warp_facts {w : Nat} (hw : w = 14 ∨ w = 15) :
    scmpi .eq .b (warpW w) 13 = false ∧ scmpi .ne .b (warpW w) 12 = true ∧
      scmpi .gt .s (warpW w) 7 = true ∧ scmpi .ne .b (andi (warpW w) (-4)) 8 = true := by
  rcases hw with rfl | rfl <;> decide

/-- A state whose sub-step is not one its site has: its obligation holds vacuously. -/
theorem stepAt_junk {p : Params} {L : Launch} {g w : Nat} {ent : Nat → Value} {d : D}
    (h : ¬ (d.k = 0 ∨ d.site.midOk d.k)) : (code p L g w ent).StepAt d :=
  ⟨fun hi => absurd hi h, fun _ _ hi => absurd hi h⟩

end
end PTX.Kernels.TmlFa4Fwd.Proof2.Loader
