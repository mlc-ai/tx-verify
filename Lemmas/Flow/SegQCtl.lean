-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.HavocTyped
public import Lemmas.Flow.Footprint
public import Lemmas.Flow.SegCtl
public import Lemmas.Flow.SegQOps
public meta import Lean

@[expose] public section

/-! # Control segments under a tag invariant (`segq_ctl`)

The strict analogue of `seg_ctl` (`Lemmas/Flow/SegCtl.lean`): a stretch of control code is cut into
exact pieces (the instructions that produce a register the target facts name) and the rest; an
exact piece is a strict segment (`seg_fp`) that also passes the typed check (`SegQ.of_seg_typed`),
the rest is a typed piece (`SegQ.of_typed`). No piece can fail, so there is no dead alternative.
The tags of the facts a piece reads are computed from the facts' constructors (`factTagsB`). The
meta helpers are public copies of the private ones of `SegCtl.lean` (that file is not edited). -/

namespace PTX.Flow.Havoc
open PTX PTX.Proof PTX.Flow.Tagged

variable {A : List Assumption} {L : Launch} {g : Nat}

/-- A bulk check that the tags `Ft` are those of the facts `F`. -/
def factTagsB (F : List (Nat × Value)) : Env → Bool
  | [] => true
  | (r, tg) :: rest => (match F.lookup r with
    | some v => tagOf v == some tg
    | none => false) && factTagsB F rest

theorem factTags_of_B {F : List (Nat × Value)} :
    ∀ {Ft : Env}, factTagsB F Ft = true → FactTags F Ft
  | [], _ => trivial
  | (r, tg) :: rest, h => by
    simp only [factTagsB, Bool.and_eq_true] at h
    refine ⟨?_, factTags_of_B h.2⟩
    cases hl : F.lookup r with
    | none => simp [hl] at h
    | some v => simpa [hl] using h.1

theorem PlainRules.mono {a b a' b' : Nat} (h : PlainRules A L g a b) (h1 : a ≤ a')
    (h2 : b' ≤ b) : PlainRules A L g a' b' :=
  fun t ha hb => h t (by omega) (by omega)

theorem PlainSegs.mono {a b a' b' : Nat} (h : PlainSegs A a b) (h1 : a ≤ a')
    (h2 : b' ≤ b) : PlainSegs A a' b' :=
  fun pc ha hb => h pc (by omega) (by omega)

end PTX.Flow.Havoc

namespace PTX.Flow.Havoc
open PTX PTX.Proof PTX.Flow.Tagged Lean Meta Elab Tactic

/-- A piece of a stretch: its instructions `[lo, hi)`, whether it is an exact piece, and the
registers to carry at its end. -/
meta structure PieceQ where
  lo : Nat
  hi : Nat
  exactStep : Bool
  live : Array Nat

/-- Walk the decoded list once and cut it into pieces (as `SegCtl.slice`). -/
meta def sliceQ (code : Expr) (a b : Nat) (targets : Array Nat) : MetaM (List PieceQ) := do
  let mut tail ← mkAppM ``List.drop #[mkNatLit a, code]
  let mut ops := #[]
  for pc in [a:b] do
    let cell ← whnfD tail
    unless cell.isAppOfArity ``List.cons 3 do throwError "segq_ctl: code ends before {pc}"
    let ins ← whnfD (cell.getArg! 1)
    ops := ops.push (← whnfD (ins.getArg! 1))
    tail := cell.getArg! 2
  let mut needed := targets
  let mut pieces : List PieceQ := []
  let mut carryNeeded := false
  for j in [0:ops.size] do
    let idx := ops.size - j - 1
    let pc := a + idx
    let op := ops[idx]!
    let writes ← regList (← mkAppM ``writesRegs #[op])
    let mut cin := false
    let mut cout := false
    if op.isAppOf ``Op.int then
      let flags ← whnfD (← mkAppM ``PTX.Flow.carryIO #[op])
      cin := (← whnfD (flags.getArg! 2)).isConstOf ``Bool.true
      cout := (← whnfD (flags.getArg! 3)).isConstOf ``Bool.true
    let use := carryNeeded || writes.any needed.contains
    carryNeeded := (carryNeeded && !cout) || (use && cin)
    match pieces with
    | p :: rest =>
      if p.exactStep == use then pieces := { p with lo := pc } :: rest
      else pieces := ⟨pc, pc+1, use, needed⟩ :: pieces
    | [] => pieces := [⟨pc, pc+1, use, needed⟩]
    if use then
      let names ← regList (← mkAppM ``opRegs #[op])
      needed := needed.filter (!writes.contains ·)
      for r in names do
        if names.count r > writes.count r && !needed.contains r then needed := needed.push r
  return pieces

/-- The values of the registers a fact list names. -/
meta def factValuesQ (facts : Expr) : MetaM (Std.HashMap Nat Expr) := do
  let (ex, tbl) ← splitFacts facts
  let mut vals := {}
  if let some (rs, v) := tbl then
    for r in ← regList rs do vals := vals.insert r (mkApp v (mkNatLit r))
  for e in ex.reverse do
    let p ← whnfD e
    vals := vals.insert (← natValue (p.getArg! 2)) (p.getArg! 3)
  return vals

/-- The registers the instructions `[lo, hi)` of the kernel `k` name. -/
meta def pieceRegs (k code : Expr) (lo hi : Nat) : MetaM (Array Nat) := do
  let mut regs : Array Nat := #[]
  for pc in [lo:hi] do
    let some ins ← instrAt k code pc | throwError "segq_ctl: no instruction at {pc}"
    let ins ← whnfD ins
    let op ← whnfD (ins.getArg! 1)
    regs := regs ++ (← regList (← mkAppM ``opRegs #[op]))
  return regs

/-- The tags of the facts (among the registers `only`) whose values are bit patterns or
predicates, as a literal list. -/
meta def factTagList (vals : Std.HashMap Nat Expr) (only : Array Nat) : MetaM Expr := do
  let pair ← mkAppM ``Prod #[mkConst ``Nat, mkConst ``Tag]
  let mut entries := #[]
  for (r, v) in vals.toList.mergeSort (fun x y => x.1 ≤ y.1) do
    unless only.contains r do continue
    let v ← whnfD v
    if v.isAppOfArity ``Value.bits 2 then
      let w ← natValue (v.getArg! 0)
      entries := entries.push (← mkAppM ``Prod.mk #[mkNatLit r,
        mkApp (mkConst ``Tag.bits) (mkNatLit w)])
    else if v.isAppOfArity ``Value.pred 1 then
      entries := entries.push (← mkAppM ``Prod.mk #[mkNatLit r, mkConst ``Tag.pred])
  mkListLit pair entries.toList

/-- Prove a strict control segment under the tag invariant `QT qt`. `rules` and `hooks` are the
plain-stretch hypotheses (`PlainRules`, `PlainSegs` over a range containing the stretch) and `hA`
the rules' frame (`RulesFrame`, for an exact piece that writes none of the tagged registers); the
supplied tactic simplifies values of the exact pieces, as for `seg_fp`. -/
syntax "segq_ctl " term:max ", " term:max ", " term:max ", " term:max " using " tacticSeq : tactic

elab_rules : tactic
  | `(tactic| segq_ctl $qt, $hN, $hS, $hA using $vals) => withMainContext do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    unless target.isAppOfArity ``SegQ 9 do throwError "segq_ctl: expected SegQ"
    let #[k, asms, launch, thread, _q, a, f, b, g] := target.getAppArgs |
      throwError "segq_ctl: expected SegQ"
    let pair ← mkAppM ``Prod #[mkConst ``Nat, mkConst ``Value]
    let finish ← factValuesQ g
    let start ← natValue a
    let stop ← natValue b
    unless start ≤ stop do throwError "segq_ctl: backward stretch"
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
          let v ← if p.exactStep then do
            let o ← whnfD (← mkAppM ``PTX.Flow.checkpoint #[k, asms, launch, thread, mkNatLit p.lo,
              mkNatLit (p.hi - p.lo), input, mkNatLit r])
            unless o.isAppOfArity ``Option.some 2 do
              throwError "segq_ctl: cannot compute register {r} at checkpoint {p.hi}"
            pure (o.getArg! 1)
            else match known[r]? with
              | some v => pure v
              | none => throwError "segq_ctl: missing input for register {r} at {p.lo}"
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
          repeat' apply And.intro rfl
          exact True.intro))
      input ← instantiateMVars output

end PTX.Flow.Havoc
