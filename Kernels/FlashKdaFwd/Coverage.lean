-- SPDX-License-Identifier: Apache-2.0
import Core.Source.Decode
import Kernels.FlashKdaFwd.Ptx

/-! Decode each production entry in its own actual environment. Report the first location and
the count for every rejected form and every decoded form missing an execution rule. -/
open PTX

def main : IO Unit := do
  let source := Generated.FlashKdaFwd.module
  if let .error e := Decode.target source.directives then
    throw (IO.userError e)
  let mut missing := false
  for (f, index) in source.functions.zipIdx do
    match Decode.prepare source.globals f with
    | .error msg =>
      IO.println s!"entry {index}: declarations: {msg}"
      missing := true
    | .ok p =>
      let mut issues : Std.TreeMap String (Nat × Nat) := ∅
      for ((pred, opcode, args), pc) in p.instrs.zipIdx do
        let result := do
          let _ ← Decode.guard p.env pred
          let op ← Decode.op { p.env with pc } opcode args
          unless op.rule.isSome do throw "no execution rule"
        if let .error msg := result then
          let key := s!"{opcode}: {msg}"
          let (first, count) := issues.getD key (pc, 0)
          issues := issues.insert key (first, count + 1)
      IO.println s!"entry {index}: {p.instrs.length} instructions, {issues.size} issue kinds"
      for (reason, first, count) in issues do
        IO.println s!"  pc {first}, {count} occurrences: {reason}"
      missing := missing || !issues.isEmpty
  if missing then throw (IO.userError "incomplete instruction coverage")
