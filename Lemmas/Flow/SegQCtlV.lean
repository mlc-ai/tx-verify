-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.SegQCtl

@[expose] public section

/-! # `segq_ctlv`: `segq_ctl` for facts stated in their own normal form

`segq_ctl` (`Lemmas/Flow/SegQCtl.lean`) closes the lookups of the facts a typed piece carries by
`rfl`: the carried values are the code's computed terms, which equal the stated ones only up to
arithmetic (`n % 2 ^ 32` against `truncBits`). `segq_ctlv` closes them by the supplied tactic
as well. -/

namespace PTX.Flow.Havoc
open PTX PTX.Proof PTX.Flow.Tagged Lean Meta Elab Tactic

/-- `segq_ctl` whose lookups of carried facts are closed by the given tactic too, for facts
whose values are stated apart from the code's own terms. `rules` and `hooks` are the
plain-stretch hypotheses (`PlainRules`, `PlainSegs` over a range containing the stretch) and `hA`
the rules' frame (`RulesFrame`, for an exact piece that writes none of the tagged registers); the
supplied tactic simplifies values of the exact pieces, as for `seg_fp`. -/
syntax "segq_ctlv " term:max ", " term:max ", " term:max ", " term:max " using " tacticSeq : tactic

/-- `segq_ctlv` whose cuts between pieces take the register values of the target's table
(`valueOf`-style functions) instead of computing them, for stretches whose symbolic values the
checkpoint evaluation cannot reduce (a signed shift of an unknown word). -/
syntax "segq_ctlt " term:max ", " term:max ", " term:max ", " term:max " using " tacticSeq : tactic

meta def runSegq (qt hN hS hA : TSyntax `term) (vals : TSyntax ``Lean.Parser.Tactic.tacticSeq)
    (tbl : Bool) : TacticM Unit := withMainContext do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    unless target.isAppOfArity ``SegQ 9 do throwError "segq_ctlv: expected SegQ"
    let #[k, asms, launch, thread, _q, a, f, b, g] := target.getAppArgs |
      throwError "segq_ctlv: expected SegQ"
    let pair ← mkAppM ``Prod #[mkConst ``Nat, mkConst ``Value]
    let finish ← factValuesQ g
    let start ← natValue a
    let stop ← natValue b
    unless start ≤ stop do throwError "segq_ctlv: backward stretch"
    let pieces ← sliceQ (← mkAppM ``Kernel.code #[k]) start stop finish.toArray.unzip.1
    let mut input := f
    let mut todo := pieces
    if todo.isEmpty then todo := [⟨start, stop, false, #[]⟩]
    for p in todo do
      let last := p.hi == stop
      let known ← factValuesQ input
      let output ← if last then pure g else do
        let mut entries := #[]
        for r in p.live do
          let v ← if tbl && p.exactStep then do
              match finish[r]? with
              | some v => pure v
              | none =>
                match (← splitFacts g).2 with
                | some (_, f) => pure (mkApp f (mkNatLit r))
                | none => throwError "segq_ctlt: no table value for register {r}"
            else if p.exactStep then do
            let o ← whnfD (← mkAppM ``PTX.Flow.checkpoint #[k, asms, launch, thread, mkNatLit p.lo,
              mkNatLit (p.hi - p.lo), input, mkNatLit r])
            unless o.isAppOfArity ``Option.some 2 do
              throwError "segq_ctlv: cannot compute register {r} at checkpoint {p.hi}"
            pure (o.getArg! 1)
            else match known[r]? with
              | some v => pure v
              | none => throwError "segq_ctlv: missing input for register {r} at {p.lo}"
          entries := entries.push (← mkAppM ``Prod.mk #[mkNatLit r, v])
        mkListLit pair entries.toList
      unless last do
        let mid ← Term.exprToSyntax output
        let pc := quote p.hi
        evalTactic (← `(tactic| refine SegQ.comp (b := $pc) (G := $mid) ?_ ?_))
      let regs ← pieceRegs k (← mkAppM ``Kernel.code #[k]) p.lo p.hi
      let ft ← Term.exprToSyntax (← factTagList known regs)
      if p.exactStep then
        let n := quote (p.hi - p.lo)
        evalTactic (← `(tactic| focus
          first
          | refine SegQ.of_seg_typed $qt (Ft := $ft) (n := $n) ?_ rfl (by decide +kernel)
              (by decide +kernel) (PlainRules.mono $hN (by decide +kernel) (by decide +kernel))
              (PlainSegs.mono $hS (by decide +kernel) (by decide +kernel))
              (factTags_of_B (by rfl)) (by decide +kernel)
          | refine SegQ.of_seg_frame $hA ?_ rfl (by decide +kernel) (by decide +kernel)
              (PlainSegs.mono $hS (by decide +kernel) (by decide +kernel))
              (by decide +kernel) (by decide +kernel)
          intro t ht
          seg_fp ht using $vals))
      else
        let keys ← Term.exprToSyntax (← mkRegList (← regList
          (← mkAppM ``List.map #[← mkAppOptM ``Prod.fst #[some (mkConst ``Nat),
            some (mkConst ``Value)], output])))
        evalTactic (← `(tactic| focus
          refine SegQ.of_typed $qt (Ft := $ft) (by decide +kernel) (by decide +kernel)
            (PlainRules.mono $hN (by decide +kernel) (by decide +kernel))
            (PlainSegs.mono $hS (by decide +kernel) (by decide +kernel))
            (factTags_of_B (by rfl))
            (by change checkQ _ _ _ _ $keys _ = true; decide +kernel) ?_
          apply PTX.Flow.Selected.subset
          repeat' apply And.intro (by
            first
            | rfl
            | (simp only [List.lookup, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte,
                beq_self_eq_true, Option.some.injEq]
               first | rfl | ($vals))
            | ($vals))
          exact True.intro))
      input ← instantiateMVars output

elab_rules : tactic
  | `(tactic| segq_ctlv $qt, $hN, $hS, $hA using $vals) => runSegq qt hN hS hA vals false
  | `(tactic| segq_ctlt $qt, $hN, $hS, $hA using $vals) => runSegq qt hN hS hA vals true


end PTX.Flow.Havoc
