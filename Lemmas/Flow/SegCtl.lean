-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.Havoc
public import Lemmas.Flow.Footprint
public meta import Lean

@[expose] public section

namespace PTX.Flow

open PTX.Proof

/-- A lookup certificate avoids deciding equality of symbolic control values. -/
def Selected (F : List (Nat × Value)) : List (Nat × Value) → Prop
  | [] => True
  | (r,v) :: rest => F.lookup r = some v ∧ Selected F rest

theorem Selected.subset {F G : List (Nat × Value)} (h : Selected F G) : ∀ p ∈ G, p ∈ F := by
  induction G with
  | nil => exact fun _ h => List.not_mem_nil h |>.elim
  | cons p ps ih =>
    intro q hq
    rcases List.mem_cons.mp hq with rfl | ht
    · exact mem_of_lookup h.1
    · exact ih h.2 q ht

/-- Candidate values at a checkpoint. The exact piece independently proves them from arbitrary
initial registers and carry flag. -/
noncomputable def checkpoint (K : Kernel) (A : List Assumption) (L : Launch) (g pc n : Nat)
    (F : List (Nat × Value)) (r : Nat) : Option Value := do
  let u ← run K A L g n { pc := pc, regs := override F (fun _ => none) }
  u.regs r

open Lean Meta Elab Tactic

private meta structure Piece where
  lo : Nat
  hi : Nat
  exactStep : Bool
  live : Array Nat

def carryIO : Op → Bool × Bool
  | .int i =>
    match i.op with
    | .addCarry cin cout | .subCarry cin cout | .madCarry _ cin cout => (cin, cout)
    | _ => (false, false)
  | _ => (false, false)

/-- Walk the decoded list once. The proof emitted for a skipped piece checks the list in bulk. -/
private meta def slice (code : Expr) (a b : Nat) (targets : Array Nat) : MetaM (List Piece) := do
  let mut tail ← mkAppM ``List.drop #[mkNatLit a, code]
  let mut ops := #[]
  for pc in [a:b] do
    let cell ← whnfD tail
    unless cell.isAppOfArity ``List.cons 3 do throwError "seg_ctl: code ends before {pc}"
    let ins ← whnfD (cell.getArg! 1)
    ops := ops.push (← whnfD (ins.getArg! 1))
    tail := cell.getArg! 2
  let mut needed := targets
  let mut pieces : List Piece := []
  let mut carryNeeded := false
  for j in [0:ops.size] do
    let idx := ops.size - j - 1
    let pc := a + idx
    let op := ops[idx]!
    let writes ← regList (← mkAppM ``writesRegs #[op])
    let mut cin := false
    let mut cout := false
    if op.isAppOf ``Op.int then
      let flags ← whnfD (← mkAppM ``carryIO #[op])
      cin := (← whnfD (flags.getArg! 2)).isConstOf ``Bool.true
      cout := (← whnfD (flags.getArg! 3)).isConstOf ``Bool.true
    -- A scalar checkpoint cannot express a carry fact. Keep its producer and consumer
    -- in the same exact piece, including the instructions in between.
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

private meta def factValues (facts : Expr) : MetaM (Std.HashMap Nat Expr) := do
  let (ex, tbl) ← splitFacts facts
  let mut vals := {}
  if let some (rs, v) := tbl then
    for r in ← regList rs do vals := vals.insert r (mkApp v (mkNatLit r))
  for e in ex.reverse do
    let p ← whnfD e
    vals := vals.insert (← natValue (p.getArg! 2)) (p.getArg! 3)
  return vals

/-- Prove a control segment with the local-rule frame and hook table for the kernel.
The supplied tactic simplifies values of the selected instructions, as for `seg_fp`. -/
syntax "seg_ctl " term:max ", " term:max " using " tacticSeq : tactic

elab_rules : tactic
  | `(tactic| seg_ctl $rules, $hooks using $vals) => withMainContext do
    let target := (← instantiateMVars (← getMainTarget)).consumeMData
    unless target.isAppOfArity ``SegU 8 do throwError "seg_ctl: expected SegU"
    let #[k, asms, launch, thread, a, f, b, g] := target.getAppArgs |
      throwError "seg_ctl: expected SegU"
    let pair ← mkAppM ``Prod #[mkConst ``Nat, mkConst ``Value]
    let finish ← factValues g
    let start ← natValue a
    let stop ← natValue b
    unless start ≤ stop do throwError "seg_ctl: backward stretch"
    let pieces ← slice (← mkAppM ``Kernel.code #[k]) start stop finish.toArray.unzip.1
    let mut input := f
    let mut todo := pieces
    if todo.isEmpty then todo := [⟨start, stop, false, #[]⟩]
    for p in todo do
      let last := p.hi == stop
      let output ← if last then pure g else do
        let known ← factValues input
        let mut entries := #[]
        for r in p.live do
          let v ← if p.exactStep then do
            let o ← whnfD (← mkAppM ``checkpoint #[k, asms, launch, thread, mkNatLit p.lo,
              mkNatLit (p.hi - p.lo), input, mkNatLit r])
            unless o.isAppOfArity ``Option.some 2 do
              throwError "seg_ctl: cannot compute register {r} at checkpoint {p.hi}"
            pure (o.getArg! 1)
            else match known[r]? with
              | some v => pure v
              | none => throwError "seg_ctl: missing input for register {r} at {p.lo}"
          entries := entries.push (← mkAppM ``Prod.mk #[mkNatLit r, v])
        mkListLit pair entries.toList
      unless last do
        let mid ← Term.exprToSyntax output
        let pc := quote p.hi
        evalTactic (← `(tactic| refine SegU.comp (b := $pc) (G := $mid) ?_ ?_))
      if p.exactStep then
        let n := quote (p.hi - p.lo)
        evalTactic (← `(tactic| focus
          apply SegU.of_seg (n := $n)
          intro t ht
          seg_fp ht using $vals))
      else
        let keys ← Term.exprToSyntax (← mkRegList (← regList
          (← mkAppM ``List.map #[← mkAppOptM ``Prod.fst #[some (mkConst ``Nat),
            some (mkConst ``Value)], output])))
        evalTactic (← `(tactic| focus
          apply SegU.of_havoc $rules $hooks (by decide +kernel) (by decide +kernel)
            (by change Havoc.check _ $keys _ _ _ = true; decide +kernel)
          apply Selected.subset
          repeat' apply And.intro rfl
          exact True.intro))
      input ← instantiateMVars output

macro "seg_ctl " rules:term:max ", " hooks:term:max : tactic =>
  `(tactic| seg_ctl $rules, $hooks using rfl)

end PTX.Flow
