-- SPDX-License-Identifier: Apache-2.0
module

public import Lemmas.Flow.SegQ
public meta import Lean

@[expose] public section

/-! # `seg_chain`: a long strict stretch as a chain of short ones

A declaration has a fixed budget, and a stretch of some dozens of instructions does not fit it.
`seg_chain name S F from lo to hi step k by tac` declares, for each chunk `[a, b)`
of `k` instructions, a theorem `name_a : S a (F a) b (F b)` proved by `tac`, and
`name : S lo (F lo) hi (F hi)` as their composition (`SegQ.comp`). `S` is the segment relation
(`fun a F b G => SegQ ...`) and `F` the facts at a program counter. -/

open Lean Elab Command

namespace PTX.Flow

syntax (name := segChain) "seg_chain " ident term:max term:max " from " num " to " num
  " step " num " by " tacticSeq : command

@[command_elab segChain] meta def elabSegChain : CommandElab
  | `(command| seg_chain $name $S $F from $lo to $hi step $k by $tac) => do
    let lo := lo.getNat
    let hi := hi.getNat
    let k := k.getNat
    let mut cur := lo
    let mut proofs : Array (TSyntax `term) := #[]
    while cur < hi do
      let nxt := min (cur + k) hi
      let nm := mkIdent (name.getId.appendAfter s!"_{cur}")
      let a := Syntax.mkNumLit (toString cur)
      let b := Syntax.mkNumLit (toString nxt)
      elabCommand (← `(command| theorem $nm : $S $a ($F $a) $b ($F $b) := by $tac))
      proofs := proofs.push (← `(by apply $nm))
      cur := nxt
    let mut proof := proofs.back!
    for i in [0:proofs.size - 1] do
      let p := proofs[proofs.size - 2 - i]!
      proof ← `(SegQ.comp $p $proof)
    let a := Syntax.mkNumLit (toString lo)
    let b := Syntax.mkNumLit (toString hi)
    elabCommand (← `(command| theorem $name : $S $a ($F $a) $b ($F $b) := $proof))
  | _ => throwUnsupportedSyntax

end PTX.Flow
