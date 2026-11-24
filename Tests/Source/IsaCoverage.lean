-- SPDX-License-Identifier: Apache-2.0
module

public import Core.Source.Decode
public meta import Core.Source.Decode

/-!
# Coverage of the instruction tables

`lean --run Tests/Source/IsaCoverage.lean` reads one instruction per line from standard input (the
opcode, then its operands, separated by tabs, in the encoding of `readOp`) and prints one status per
line.
`Tools/isa/doc_table.py` writes the lines for every legal modifier combination of every
instruction entry and compresses the statuses into `docs/core/isa-coverage.json`.

The status of an instruction is what the decoder (`Decode.op`) and `Op.rule` give: `core <ID>`
when `Op.rule` names a contract entry, `decode-only` when the instruction decodes without a rule,
and `rejected <reason>` when decoding fails.

The input line `sregs` prints, on one line, `<name>=<status>` for every special register of
`SReg.table`, separated by `;`. The status is `rejected <reason>` when the decoder does not accept
a `mov` of the register's width from it, and otherwise what `SReg.rule` and `SReg.kind` give:
`core <ID> <kind>` or `decode-only`.
-/

namespace PTX.Tests.IsaCoverage
open PTX.Isa PTX.Syntax

/-- Read a name up to a separator. -/
partial def readName (cs : List Char) (acc : List Char) : String × List Char :=
  match cs with
  | [] => (String.ofList acc.reverse, [])
  | c :: rest =>
    if c = ',' ∨ c = '(' ∨ c = ')' ∨ c = '\t' then (String.ofList acc.reverse, cs)
    else readName rest (c :: acc)

mutual
/-- Read one operand of the line encoding. -/
partial def readOp (cs : List Char) : Option (Operand × List Char) :=
  match cs with
  | 'r' :: rest => let (n, r) := readName rest []; some (.register n, r)
  | 's' :: rest => let (n, r) := readName rest []; some (.symbol n, r)
  | 'l' :: rest => let (n, r) := readName rest []; some (.literal n, r)
  | '_' :: rest => some (.sink, rest)
  | 'a' :: '(' :: rest => (readOps rest []).map fun (os, r) => (.address os, r)
  | 'v' :: '(' :: rest => (readOps rest []).map fun (os, r) => (.vector os, r)
  | 'p' :: '(' :: rest => (readOps rest []).map fun (os, r) => (.pair os, r)
  | 'n' :: '(' :: rest => do
    let (o, r) ← readOp rest
    match r with
    | ')' :: r => some (.negate o, r)
    | _ => none
  | 'o' :: sg :: '(' :: rest => do
    let (b, r) ← readOp rest
    match r with
    | ',' :: r =>
      let (l, r) ← readOp r
      match r with
      | ')' :: r => some (.offset (String.singleton sg) b l, r)
      | _ => none
    | _ => none
  | _ => none
/-- Read operands up to the closing parenthesis. -/
partial def readOps (cs : List Char) (acc : List Operand) : Option (List Operand × List Char) :=
  match cs with
  | ')' :: rest => some (acc.reverse, rest)
  | ',' :: rest => readOps rest acc
  | _ => do
    let (o, r) ← readOp cs
    readOps r (o :: acc)
end

/-- The names of the registers an operand mentions. -/
partial def regNames : Operand → List String
  | .register n => [n]
  | .address cs | .vector cs | .pair cs => cs.flatMap regNames
  | .offset _ b o => regNames b ++ regNames o
  | .negate o => regNames o
  | _ => []

/-- The register class of the names `%<type>_<i>`: the width of the data type `<type>` names. -/
def typeClass (ty : String) : Option Decode.RegClass := do
  let ts ← opTokens (bytes ty) 0 []
  let [t] := ts | none
  let d ← Decode.dtypeOf? t
  some ⟨("%" ++ ty ++ "_").toList, 256, d.width⟩

/-- The decoding environment of a sample: one register class per type name used, the address
registers `%A32_i` and `%A64_i`, the label `L`, the branch table `T`, scalar parameters `P<w>` and
parameter objects `O<w>`. -/
def mkEnv (types : List String) : Decode.Env :=
  { classes := ⟨"%A32_".toList, 256, 32⟩ :: ⟨"%A64_".toList, 256, 64⟩ ::
      types.filterMap typeClass
    labels := [("L", 0)]
    params := [8, 16, 32, 64, 128].map fun w => (s!"P{w}", w)
    objects := [8, 16, 32, 64].map fun w => ⟨s!"O{w}", w, 64 / (w / 8), 128⟩
    tables := [("T", 0, [0])] }

/-- The status of a decoded operation: the rule `Op.rule` names (PROG-INSTR-RULE), which is the
case split of `execLocal` and, by `eventTmpl_rule`, of `eventTmpl`. -/
def status (op : Op) : String :=
  match op.rule with
  | some r => "core " ++ r.id
  | none => "decode-only"

/-- The name of a kind of special register value. -/
def kindName : SRegKind → String
  | .launch => "launch"
  | .lane => "lane"
  | .initial => "initial"
  | .varying => "varying"

/-- The status of the special register `s` spelled `name`: the decoder must accept a `mov` of the
register's width from it; then the rule `SReg.rule` names and the kind `SReg.kind` gives. -/
def sregStatus (s : SReg) (name : String) : String :=
  let (opcode, dst) := match s.width with
    | 1 => ("mov.pred", "%pred_0")
    | 64 => ("mov.b64", "%b64_0")
    | _ => ("mov.b32", "%b32_0")
  match Decode.op (mkEnv ["pred", "b32", "b64"]) opcode [.register dst, .register name] with
  | .error e => "rejected " ++ e
  | .ok _ => match s.rule, s.kind with
    | some r, some k => "core " ++ r.id ++ " " ++ kindName k
    | _, _ => "decode-only"

/-- The statuses of every special register of `SReg.table`, on one line. -/
def sregLine : String :=
  ";".intercalate (SReg.table.map fun (bs, s) =>
    let name := "%" ++ String.ofList (bs.map Char.ofNat)
    name ++ "=" ++ sregStatus s name)

/-- The status of one sample line: the entry that the grammar recognizes must be the expected
one, and the decoder must accept the instruction. The line `sregs` gives `sregLine`. -/
def line (env : Decode.Env) (l : String) : String :=
  if l = "sregs" then sregLine else
  match l.splitOn "\t" with
  | want :: opcode :: args =>
    match args.mapM (fun a => (readOp a.toList).map (·.1)) with
    | none => "bad line"
    | some os =>
      match Grammar.parse env.isPred opcode os with
      | .error e => "rejected grammar: " ++ e
      | .ok r =>
        if (toString (repr r.entry)).drop 14 != want then
          "rejected grammar: recognized as " ++ (toString (repr r.entry)).drop 14
        else
          match Decode.op env opcode os with
          | .ok op => status op
          | .error e => "rejected " ++ e
  | _ => "bad line"

/-- Read all lines of standard input, build the environment from the register names, and print
the status of each line. -/
def main : IO Unit := do
  let stdin ← IO.getStdin
  let mut lines : Array String := #[]
  repeat
    let l ← stdin.getLine
    if l.isEmpty then break
    lines := lines.push (l.dropEndWhile (· == '\n')).copy
  let mut types : List String := []
  for l in lines do
    match l.splitOn "\t" with
    | _ :: _ :: args =>
      for a in args do
        match readOp a.toList with
        | some (o, _) =>
          for n in regNames o do
            match n.toList.reverse.dropWhile (·.isDigit) with
            | '_' :: ty =>
              let ty := (String.ofList ty.reverse).drop 1 |>.copy
              unless ty = "A32" ∨ ty = "A64" ∨ types.contains ty do types := ty :: types
            | _ => pure ()
        | none => pure ()
    | _ => pure ()
  let env := mkEnv types
  let out ← IO.getStdout
  for l in lines do
    out.putStrLn (line env l)

end PTX.Tests.IsaCoverage

public def main : IO Unit := PTX.Tests.IsaCoverage.main
