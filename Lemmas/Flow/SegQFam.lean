-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.SegQ
public meta import Lean

@[expose] public section

/-! # `seg_fam`: a statement over finite indices, one declaration per index value

A declaration has a fixed budget of heartbeats, and a family of strict stretches whose program
counters depend on an index (the twelve elections, the preload blocks) does not fit it in one
proof. `seg_fam name (i 12) (j 4) : stmt := tac` declares, for each pair of values of the indices
`i : Fin 12` and `j : Fin 4` (written as typed numerals in `stmt`), a theorem `name_i_j : stmt`
proved by `tac`, and `name : ∀ (i : Fin 12) (j : Fin 4), stmt` from them. -/

open Lean Elab Command

namespace PTX.Flow

syntax famIdx := " (" ident num ")"

syntax (name := segFam) "seg_fam " ident famIdx* " : " term " := " tacticSeq : command

meta partial def substId (id : Name) (rep : Syntax) : Syntax → Syntax
  | stx@(.ident ..) => if stx.getId == id then rep else stx
  | .node i k args => .node i k (args.map (substId id rep))
  | stx => stx

meta def famCases : List (Name × Nat) → List (List Nat)
  | [] => [[]]
  | (_, n) :: rest => (List.range n).flatMap fun k => (famCases rest).map (k :: ·)

@[command_elab segFam] meta def elabSegFam : CommandElab
  | `(command| seg_fam $name $[($ids:ident $ns:num)]* : $stmt := $tac) => do
    let idxs := (ids.zip ns).toList.map fun (i, n) => (i.getId, n.getNat)
    let mut thms : Array (TSyntax `term) := #[]
    for c in famCases idxs do
      let nm := mkIdent (c.foldl (fun (n : Name) k => n.appendAfter s!"_{k}") name.getId)
      let mut s : Syntax := stmt.raw
      for ((id, n), k) in idxs.zip c do
        let lit := Syntax.mkNumLit (toString k)
        let nl := Syntax.mkNumLit (toString n)
        s := substId id (← `(($lit : Fin $nl))).raw s
      elabCommand (← `(command| theorem $nm : $(⟨s⟩) := by $tac))
      thms := thms.push nm
    let mut ty : TSyntax `term := stmt
    let mut splits : Array (TSyntax `tactic) := #[]
    for (id, n) in idxs.reverse do
      let nl := Syntax.mkNumLit (toString n)
      ty ← `(∀ ($(mkIdent id) : Fin $nl), $ty)
    for (id, _) in idxs do
      splits := splits.push (← `(tactic| intro $(mkIdent id):ident))
    for (id, _) in idxs do
      splits := splits.push (← `(tactic| all_goals fin_cases $(mkIdent id):ident))
    elabCommand (← `(command| theorem $name : $ty := by
      $splits:tactic*
      exacts [$thms,*]))
  | _ => throwUnsupportedSyntax

end PTX.Flow
